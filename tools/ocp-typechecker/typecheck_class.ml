(**************************************************************************)
(*                                                                        *)
(*   Typerex Tools                                                        *)
(*                                                                        *)
(*   Copyright 2011-2017 OCamlPro SAS                                     *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3 described in the file       *)
(*   LICENSE.                                                             *)
(*                                                                        *)
(**************************************************************************)

open Typecheck_types
open Typecheck_typexpr
open Typecheck_expr
open Typecheck_utils
open Typecheck_flags
open Typecheck_result
open Types
open Btype
open Typedtree
open Asttypes

module Ctype = Typecheck_ctype

(* Error related functions *)

type error =
    Self_type_different of type_expr * type_expr
  | Not_an_object of type_expr
  | Undeclared_method of string
  | Illformed_object_type of type_expr

exception Class_error of (error * Location.t)

(* let raise_error loc e = raise (Class_error (e, loc)) *)

(* Utility functions and values *)

(*
   Self type have a dummy private method, thus preventing it to become
   closed.
*)
let dummy_method = Btype.dummy_method

(*
   Path associated to the temporary class type of a class being typed
   (its constructor is not available).
*)
let unbound_class = Path.Pident (Ident.create "")

let transl_method_ctype cl_env id priv cty self_type =
  let _, ty' =
    Ctype.filter_self_method cl_env.val_env id priv cl_env.meths self_type in
  let ty, tvars =
    transl_ctype_aux
      { cl_env.ctx with env = cl_env.val_env }
      cl_env.tvars Extensible true cty in
  match Typecheck_typing.instance cl_env.ctx ty ty' TyMap.empty with
    Ok (_, ctx) -> { cl_env with ctx; tvars }
  | Error _ -> raise (Class_error (Self_type_different (ty, ty'), cty.ctyp_loc))

let gen_object_type final meths concr_meths =
  let dummy_kind, row_var =
    if final then Fabsent, newgenty Tnil
    else Fvar (ref None), newgenty (Tvar None) in
  Meths.fold (fun n (id, ty) k ->
      let kind =
        if Concr.mem n concr_meths then Fpresent
        else if final then Fabsent else Fvar (ref None) in
      fun ty' -> k @@ newgenty (Tfield (n, kind, ty, ty')))
    meths (fun ty -> ty) row_var |> fun ty ->
  newgenty (Tfield (dummy_method, dummy_kind, newgenty (Ttuple []), ty))

(* Fully expand the head of a class type *)
let rec scrape_class_type =
  function
    Cty_constr (_, _, cty) -> scrape_class_type cty
  | cty                     -> cty

(* Generalize a class type *)
let rec generalize_class_type gen =
  function
    Cty_constr (_, params, cty) ->
      List.iter gen params;
      generalize_class_type gen cty
  | Cty_signature {csig_self = sty; csig_vars = vars; csig_inher = inher} ->
      gen sty;
      Vars.iter (fun _ (_, _, ty) -> gen ty) vars;
      List.iter (fun (_,tl) -> List.iter gen tl) inher
  | Cty_arrow (_, ty, cty) ->
      gen ty;
      generalize_class_type gen cty

let generalize_class_type vars =
  let gen = if vars then Ctype.generalize else Ctype.generalize_structure in
  generalize_class_type gen


let virtual_methods sign =
  let (fields, _) =
    print_debug (
      Format.asprintf "virtual_methods, fields: %a"
        Printtyp.raw_type_expr sign.Types.csig_self);
    Ctype.flatten_fields (Ctype.object_fields sign.Types.csig_self)
  in
  List.fold_left
    (fun virt (lab, _, _) ->
       if lab = dummy_method then virt else
       if Concr.mem lab sign.csig_concr then virt else
       lab::virt)
    [] fields

let concr_vals vars =
  Vars.fold
    (fun id (_, vf, _) s -> if vf = Virtual then s else Concr.add id s)
    vars Concr.empty

let rec abbreviate_class_type path params cty =
  match cty with
    Cty_constr (_, _, _) | Cty_signature _ ->
      Cty_constr (path, params, cty)
  | Cty_arrow (l, ty, cty) ->
      Cty_arrow (l, ty, abbreviate_class_type path params cty)

let extract_constraints cty =
  let sign = Ctype.signature_of_class_type cty in
  (Vars.fold (fun lab _ vars -> lab :: vars) sign.csig_vars [],
   begin let (fields, _) =
    print_debug (
      Format.asprintf "extract_constraints, fields: %a"
        Printtyp.raw_type_expr sign.Types.csig_self);
     Ctype.flatten_fields (Ctype.object_fields sign.csig_self)
   in
   List.fold_left
     (fun meths (lab, _, _) ->
        if lab = dummy_method then meths else lab::meths)
     [] fields
   end,
   sign.csig_concr)

(** Environment relative functions *)

let add_val cl_env id kind ty =
  { cl_env with
    val_env = Env.add_value id
        { val_type = ty; val_kind = kind;
          val_attributes = []; val_loc = Location.none } cl_env.val_env;
    meth_env = Env.add_value id
        { val_type = ty; val_kind = Val_unbound;
          val_attributes = []; val_loc = Location.none } cl_env.meth_env;
    par_env = Env.add_value id
        { val_type = ty; val_kind = Val_unbound;
          val_attributes = []; val_loc = Location.none } cl_env.par_env
  }

let add_meth cl_env id kind ty =
  { cl_env with
    val_env = Env.add_value id
        { val_type = ty; val_kind = Val_unbound;
          val_attributes = []; val_loc = Location.none } cl_env.val_env;
    meth_env = Env.add_value id
        { val_type = ty; val_kind = kind;
          val_attributes = []; val_loc = Location.none } cl_env.meth_env;
    par_env = Env.add_value id
        { val_type = ty; val_kind = Val_unbound;
          val_attributes = []; val_loc = Location.none } cl_env.par_env
  }

let add_val cl_num (cl_env : class_env) inh mut virt id ty =
  let (exists, virt) =
    try
      let (id, mut', virt', ty') = Vars.find (Ident.name id) !(cl_env.vars) in
      if mut <> mut' then failwith "Mutability mismatch";
      match Typecheck_typing.instance cl_env.ctx ty ty' TyMap.empty with
        Ok (_, _) -> not inh, if virt' = Asttypes.Concrete then virt' else virt
      | Error _ -> failwith "Field type mismatch"
    with Not_found -> false, virt
  in
  print_debug
    (Format.asprintf "Adding val %a, exists already? %b"
       Typecheck_pretty.ident id exists);
  let cl_env = if exists then cl_env
    else add_meth cl_env id (Val_ivar (mut, cl_num)) ty in
  cl_env.vars := Vars.add (Ident.name id) (id, mut, virt, ty) !(cl_env.vars);
  cl_env


let rec approx_class = function
    Cty_signature sg -> sg.csig_self
  | Cty_arrow (l, ty, cty) ->
    Ctype.newty (Tarrow (l, ty, approx_class cty, Cok))
  | Cty_constr  (p, tys, cty) ->
    Ctype.newty (Tconstr (p, tys, ref Mnil))

(* Typing of class types and class expressions *)

let cl_num = ref 0

let add_val_sig env loc lab (mut, virt, ty) val_sig =
  let virt =
    try
      let (mut', virt', ty') = Vars.find lab val_sig in
      if virt' = Concrete then virt' else virt
    with Not_found -> virt
  in
  Vars.add lab (mut, virt, ty) val_sig

let type_inherit self_type env cl_ctx ov loc p =
  match scrape_class_type p with
    Cty_signature cl_sig ->
    (* Verifies that the self type includes the super class (might result with
       an error, to check) *)
    begin
      match Typecheck_typing.instance (create_context env)
              self_type cl_sig.csig_self TyMap.empty with
      | Ok _ -> ()
      | Error _ -> failwith "Self type mismatch with super constructor"
    end;
    let over_meths = Concr.inter cl_sig.csig_concr cl_ctx.concr_meths in
      let concr_vals = concr_vals cl_sig.csig_vars in
      let over_vals = Concr.inter concr_vals cl_ctx.concr_vals in
      begin match ov with
        Some Fresh ->
          let _cname =
            match p with
              Cty_constr (p, _, _) -> Path.name p
            | _ -> "inherited"
          in
          ()
          (* if not (Concr.is_empty over_meths) then *)
          (*   Location.prerr_warning loc *)
          (*     (Warnings.Method_override (cname :: Concr.elements over_meths)); *)
          (* if not (Concr.is_empty over_vals) then *)
          (*   Location.prerr_warning loc *)
          (*     (Warnings.Instance_variable_override *)
          (*        (cname :: Concr.elements over_vals)); *)
      | Some Override
        when Concr.is_empty over_meths && Concr.is_empty over_vals->
        failwith "No overriding"
      | _ -> ()
      end;

      let concr_meths = Concr.union cl_sig.csig_concr cl_ctx.concr_meths
      and concr_vals = Concr.union concr_vals cl_ctx.concr_vals in

      (cl_sig, { cl_ctx with concr_meths; concr_vals })
  | _ -> assert false


let rec transl_class_type (cl_num : int) cl_env tcty =
  let cty, cl_env =
    match tcty.cltyp_desc with
      Tcty_signature csig ->
      let sg, cl_env = transl_class_sig cl_num cl_env csig in
      Cty_signature sg, cl_env
    | Tcty_arrow (l, ty, res) ->
      let ty, tvars =
        Typecheck_typexpr.transl_ctype_aux
          {cl_env.ctx with env = cl_env.val_env }
          ~decl:true cl_env.tvars Extensible false ty in
      let cty_res, cl_env =
        transl_class_type cl_num { cl_env with tvars } res in
      Cty_arrow (l, ty, cty_res), cl_env
    | Tcty_constr (p, lid, args) ->
      let decl = Env.find_cltype p cl_env.val_env in
      if Path.same p unbound_class then
        failwith "Unbound class_type";
      let params, clty = decl.clty_params, decl.clty_type in
      if List.length params <> List.length args then
        failwith "Arity mismatch";
      let tvars =
        Typecheck_typexpr.transl_multiple_ctype
          {cl_env.ctx with env = cl_env.val_env }
          cl_env.tvars args in
      let args = List.map (fun c -> c.ctyp_type) args in
      let subst, ctx =
        match Typecheck_typing.instance_types
                { cl_env.ctx with env = cl_env.val_env }
                args params TyMap.empty with
          Ok (subst, ctx) -> subst, ctx
        | Error _ -> failwith "Type args mismatch"
      in
      let args = Typecheck_typing.apply_types args subst in
      let cty_res = abbreviate_class_type p args decl.clty_type in
      cty_res, { cl_env with ctx; tvars }
  in
  (* !!! TODO: Checks *)
  cty, cl_env

and transl_class_sig cl_num cl_env csig =
  let self_type_constr, tvars =
    Typecheck_typexpr.transl_ctype_aux
      { cl_env.ctx with env = cl_env.val_env }
      ~decl:true cl_env.tvars Extensible false csig.csig_self
  in
  let self_type, cl_env =
    match Typecheck_typing.instance
            { cl_env.ctx with env = cl_env.val_env }
            csig.csig_self.ctyp_type self_type_constr cl_env.substs with
      Ok (substs, ctx) -> csig.csig_self.ctyp_type, { cl_env with ctx; substs }
    | Error _ -> failwith "Self type does not match pattern" in
  print_debug (
    Format.asprintf "transl_class_sig, self_type: %a"
      Printtyp.raw_type_expr self_type);
  let self_type =
    Typecheck_typing.apply_subst self_type cl_env.substs in
  print_debug (
    Format.asprintf "transl_class_sig, self_type after subst: %a"
      Printtyp.raw_type_expr self_type);
  let cl_env, cl_ctx, vars =
    List.fold_left (fun (cl_env, cl_ctx, vals) cf ->
        transl_class_field cl_num cl_env cl_ctx vals self_type cf)
      (cl_env, empty_class_context, Vars.empty) csig.csig_fields in
  (* !!! TODO: check signatures *)
  let sg =
    Types.({
        csig_self = self_type;
        csig_vars = vars;
        csig_concr = cl_ctx.concr_meths;
        csig_inher = cl_ctx.inherited;
      }) in
  sg, { cl_env with tvars }

and transl_class_field cl_num cl_env cl_ctx vals self_type cf =
  match cf.ctf_desc with
    Tctf_inherit cty ->
    let parent, cl_env = transl_class_type cl_num cl_env cty in
    let inherited =
      match parent with
        Types.Cty_constr (p, tys, _) -> (p, tys) :: cl_ctx.inherited
      | _ -> cl_ctx.inherited in
    (* Generates the environment that contains the inherited method and checks
       the overriding. *)
    let psig, cl_ctx =
      type_inherit self_type cl_env.val_env cl_ctx None cf.ctf_loc parent in

    (* Checks for inconsistencies *)
    let vals =
      Vars.fold
        (fun n (mut, virt, ty) vals ->
           add_val_sig cl_env cf.ctf_loc n (mut, virt, ty) vals)
        psig.csig_vars vals in
    cl_env, { cl_ctx with inherited }, vals
  | Tctf_val (n, mut, virt, cty) ->
    let ty, tvars =
      Typecheck_typexpr.transl_ctype_aux
        { cl_env.ctx with env = cl_env.val_env }
        ~decl:true cl_env.tvars Extensible false cty
        in
    { cl_env with tvars }, cl_ctx,
    add_val_sig cl_env cf.ctf_loc n (mut, virt, ty) vals
  | Tctf_method (n, priv, virt, cty) ->
    let ty, tvars =
      Typecheck_typexpr.transl_ctype_aux
        { cl_env.ctx with env = cl_env.val_env }
        ~decl:true cl_env.tvars Extensible false cty
    in
    let concr_meths =
      match virt with
        Concrete -> Concr.add n cl_ctx.concr_meths
      | Virtual -> cl_ctx.concr_meths in
    { cl_env with tvars }, { cl_ctx with concr_meths }, vals
  | Tctf_constraint (cty, cty') ->
    assert false
  | _ -> assert false

let rec type_class_expr cl_num cl_env ce =
  let cty, cl_env = type_class_expr_desc cl_num cl_env ce.cl_loc ce.cl_desc in
  match Typecheck_typing.eq_class_type cl_env.ctx cty ce.cl_type with
    Error _ -> failwith "Incompatible types"
  | Ok _ -> cty, cl_env

and type_class_expr_desc cl_num cl_env loc = function
    Tcl_ident (p, lid, ctys) ->
    let decl = try
        Env.find_class p cl_env.val_env
      with Not_found -> failwith "Unbound class" in
    if Path.same p unbound_class then
      failwith "Unbound class";
    let tvars = transl_multiple_ctype
        { cl_env.ctx with env = cl_env.val_env }
        cl_env.tvars ctys in
    let tys = List.map (fun c -> c.ctyp_type) ctys in
    if List.length tys <> List.length decl.cty_params then
      failwith "Arity mismatch";
    let subst, ctx =
      match Typecheck_typing.instance_types
              { cl_env.ctx with env = cl_env.val_env }
              tys decl.cty_params TyMap.empty with
        Ok (subst, ctx) -> subst, ctx
      | Error _ -> failwith "Type args mismatch"
    in
    let tys = Typecheck_typing.apply_types tys subst in
    let cty_res = abbreviate_class_type p tys decl.cty_type in
    cty_res, { cl_env with ctx; tvars }
  | Tcl_structure cstr ->
    let csig, cl_env = type_class_structure cl_num false cl_env loc cstr in
    Cty_signature csig, cl_env
  | Tcl_fun (l, pat, idents, body, _partial) ->
    let restore_vars = Variables.set_curr_vars cl_env.tvars true in
    let ty, binded, cl_env =
      Typecheck_expr.type_class_arg_pattern cl_num cl_env l pat in
    restore_vars ();
    print_debug
      (Format.asprintf "Tcl_fun, type arg: %a"
         Printtyp.raw_type_expr ty);
    (* Checks that the retained Texp_ident have the expected type*)
    let substs = List.fold_left (fun subst (id, _, exp) ->
        let ty, _, _ =
          try SMap.find (Ident.name id) binded
          with Not_found ->
            failwith "Incoherent: variable not bound in pattern" in
        match Typecheck_typing.instance cl_env.ctx ty exp.exp_type cl_env.substs
        with
          Ok (subst, _) -> subst
        | Error _ -> failwith "Incoherent") cl_env.substs idents in
    (* assert false *)
    Typecheck_ctype.begin_def();
    let ty_body, cl_env = type_class_expr cl_num { cl_env with substs } body in
    Typecheck_ctype.end_def();
    Cty_arrow (l, ty, ty_body), cl_env
  | Tcl_apply (expr, args) ->
    let ty_cfun, cl_env = type_class_expr cl_num cl_env expr in
    let ty_capp, cl_env = type_class_application cl_num cl_env loc ty_cfun args
    in
    ty_capp, cl_env
  | Tcl_let (rec_flag, vbs, vals, cl) ->
    let restore_vars = Variables.set_curr_vars cl_env.tvars true in
    let defs, ctx =
      Typecheck_expr.type_let (create_context cl_env.val_env) vbs rec_flag in
    restore_vars ();
    let cl_env = List.fold_left2 (fun cl_env (id, vd, _) (id', _, exp) ->
        assert (Ident.name id = Ident.name id');
        begin
          match Typecheck_typing.eq (create_context cl_env.val_env)
                  vd.val_type exp.exp_type with
            Ok _ -> ()
          | Error _ -> failwith "Let-Incoherent"

        end;
        let meth_env =
          Env.add_value id'
            { vd with val_kind = Val_ivar (Immutable, cl_num) } cl_env.meth_env in
        { cl_env with meth_env }) { cl_env with val_env = ctx.env } defs vals in
    type_class_expr cl_num cl_env cl
  | Tcl_constraint (cl, ctyopt, vals, meths, concr) ->
    let cty, cl_env = type_class_expr cl_num cl_env cl in
    let cty_constr, cl_env = match ctyopt with
        Some cty -> transl_class_type 0 cl_env cty
      | None -> (* gen_signature *) assert false in
    match Typecheck_typing.coercible_class
            (create_context cl_env.val_env) cty cty_constr TyMap.empty with
      Ok _ -> cty_constr, cl_env
    | Error _ -> failwith "Cannot constraint"

and type_class_application cl_num cl_env loc cty_fun args =
  let (cty_res, subst, cl_env) = List.fold_left
      (fun (cty_res, subst, cl_env) (l, eopt, opt) ->
         let arg = match eopt with
             Some e -> e
           | None -> assert false in
         let ty_arg, cty_res =
           match cty_res with
             Cty_arrow (l', ty, cty_res) when l = l' -> ty, cty_res
           | _ -> failwith "Not a function"
         in
         let ty_arg', subst =
           Typecheck_expr.type_argument cl_env.ctx ty_arg arg subst in
         match subst with
           Error _ -> failwith "Incompatible types"
         | Ok (subst, ctx) -> cty_res, subst, { cl_env with ctx })
      (cty_fun, TyMap.empty, cl_env) args in
  Typecheck_typing.apply_class_type cty_res subst, cl_env


and type_class_structure cl_num final cl_env loc cstr =
  (* Remove all fields in the current environment.
     Type self to recover its type.
     Test that type(self) = cstr.cstr_sig.csig_type.
     Using self, type the structure.
     Test that type(self) = type(sig).
  *)
  let self_type_pat, self_type_sig = cstr.cstr_self, cstr.cstr_type.csig_self in
  print_debug
    (Format.asprintf "In typedtree, self_pattern:\n%a\nself_sig:\n%a."
       Printtyp.raw_type_expr self_type_pat.pat_type
       Printtyp.raw_type_expr self_type_sig);
  let restore_vars = Variables.set_curr_vars cl_env.tvars false in
  let self_ty, cl_env =
    Typecheck_expr.type_self_pattern cl_num cl_env cstr.cstr_self in
  restore_vars ();
  print_debug
    (Format.asprintf "Type of self: %a" Printtyp.raw_type_expr self_ty);
  let cl_env, cl_ctx = List.fold_left (fun (cl_env, cl_ctx) cf ->
      type_class_field cf.cf_loc final cl_num cl_env cl_ctx self_ty cf.cf_desc)
      (cl_env, empty_class_context) cstr.cstr_fields in
  let cobj = gen_object_type final !(cl_env.meths) cl_ctx.concr_meths |>
             fun ty -> newgenty (Tobject (ty, ref None)) in
  print_debug
    (Format.asprintf "self: %a\ncobj: %a"
       Printtyp.raw_type_expr cstr.cstr_type.csig_self
       Printtyp.raw_type_expr cobj);
  begin
    match Typecheck_typing.eq
          cl_env.ctx cobj cstr.cstr_type.csig_self with
      Ok _ -> ()
    | Error _ ->
      raise (Class_error (
          Self_type_different (cobj, cstr.cstr_type.csig_self), loc))
  end;
  let sign =
    { csig_self = cobj;
      csig_vars =
        Vars.map (fun (id, mut, vr, ty) -> (mut, vr, ty)) !(cl_env.vars);
      csig_concr = cl_ctx.concr_meths;
      csig_inher = cl_ctx.inherited; }
  in
  if final then begin
    Ctype.hide_private_methods cobj;
    let mets = virtual_methods sign in
    let vals = Vars.fold
        (fun name (mut, vr, ty) l -> if vr = Virtual then name :: l else l)
        sign.csig_vars [] in
    if mets <> [] || vals <> [] then failwith "Virtual class"
  end;
  (* !!! TO CHECK !!! *)
  sign, cl_env

and type_class_field loc final cl_num cl_env cl_ctx self_type = function
  | Tcf_inherit (ov, cle, name, inst_vars, concr_meths) ->
    (* override flag * class expression * super constructor name *
       variables inherited * method inherited *)
    let parent, cl_env = type_class_expr cl_num cl_env cle in
    let inherited =
      match parent with
        Types.Cty_constr (p, tys, _) -> (p, tys) :: cl_ctx.inherited
      | _ -> cl_ctx.inherited in
    (* Generates the environment that contains the inherited method and checks
       the overriding. *)
    let psig, cl_ctx =
      type_inherit self_type cl_env.val_env cl_ctx (Some ov) loc parent in

    (* Checks for inconsistencies *)
    let inh_vars, cl_env =
      Vars.fold
        (fun n (mut, virt, ty) (inh_vars, cl_env) ->
           let cl_env =
             add_val cl_num cl_env true mut virt (List.assoc n inst_vars) ty in
           n :: inh_vars, cl_env)
        psig.csig_vars ([], cl_env) in
    List.iter (fun n ->
        if not @@ List.mem_assoc n inst_vars then failwith "Inconsistency") inh_vars;
    List.iter (fun (n, _) ->
        if not @@ Concr.mem n psig.csig_concr then failwith "Inconsistency")
    concr_meths;

    (* Adds the super constructor in the environment *)
    let cl_env =
      match name with
        None -> cl_env
      | Some n -> add_meth cl_env (Ident.create n) (Val_anc (concr_meths, cl_num)) self_type
    in
    cl_env, { cl_ctx with inherited }
  | Tcf_val (name, mut, id, Tcfk_virtual cty, _) ->
    let ty, tvars =
      transl_ctype_aux { cl_env.ctx with env = cl_env.val_env }
        cl_env.tvars Extensible true cty
    in
    let cl_env = add_val cl_num cl_env false mut Asttypes.Virtual id ty in
    { cl_env with tvars }, cl_ctx

  | Tcf_val (name, mut, id, Tcfk_concrete (ov, e), _) ->
    if Concr.mem name.Location.txt cl_ctx.local_vals then
      failwith "Duplicate name";
    (* check for override *)
    let restore_vars = Variables.set_curr_vars cl_env.tvars false in
    let tyexp, _ =
      type_expr_aux { cl_env.ctx with env = cl_env.val_env }
        e e.exp_type in
    Ctype.generalize_structure tyexp;
    restore_vars ();
    let cl_env =
      add_val cl_num cl_env false mut Asttypes.Concrete id tyexp in
    cl_env, { cl_ctx with local_vals =
                            Concr.add name.Location.txt cl_ctx.local_vals;
                          concr_vals =
                            Concr.add name.Location.txt cl_ctx.concr_vals }
  | Tcf_method (name, priv, Tcfk_virtual cty) ->
    let cl_env =
      transl_method_ctype cl_env name.Location.txt priv cty self_type in
    cl_env, cl_ctx
  | Tcf_method (name, priv, Tcfk_concrete (ov, expr)) ->
    if Concr.mem name.txt cl_ctx.local_meths then
      failwith "Duplicate methods";
    if not @@ Concr.mem name.txt cl_ctx.concr_meths && ov = Override then
      failwith "No overriding";
    print_debug
      (Format.asprintf "FIlter method (%s, %a) in %a"
         name.txt
         Typecheck_pretty.private_flag priv
         Printtyp.raw_type_expr self_type);
    let ty =
      if priv = Public then
        begin
          let ty = Extract.find_meth { cl_env.ctx with env = cl_env.val_env }
              loc name.txt priv self_type in
          cl_env.meths :=
            Meths.add name.txt (Ident.create name.txt, ty) !(cl_env.meths);
          Some ty
        end
      else
        None in
    (* print_debug *)
    (*   (Format.asprintf "Type of method `%s` in self: %a." name.txt *)
    (*      (fun fmt tyo -> match tyopt withPrinttyp.raw_type_expr ty); *)
    let ty_constr, tvars = match expr.exp_desc with
        Texp_function ("", [ { c_lhs = self_pat;
                               c_rhs = exp };
                           ], _) ->
        let cty = extract_poly exp.exp_extra in
        let restore_vars = Variables.set_curr_vars cl_env.tvars false in
        let ty_pat, _, _ = type_pattern cl_env.val_env self_pat in
        restore_vars ();
        print_debug
          (Format.asprintf "Self_type in meth: %a" Printtyp.raw_type_expr ty_pat);
        begin
          match Typecheck_typing.eq cl_env.ctx self_type ty_pat with
            Ok _ -> ()
          | Error _ -> failwith "Illformed self argument of type: ??"
        end;
        begin
          match cty with
            None -> None, cl_env.tvars
          | Some cty ->
            let ty, vars =
              transl_ctype_aux
                { cl_env.ctx with env = cl_env.val_env }
                cl_env.tvars Univars final cty
            in
            print_debug
              (Format.asprintf "poly_constraint for method %s:\n%a"
                 name.txt Printtyp.raw_type_expr ty);
            Some ty, vars
        end;
      | _ -> failwith "Illformed method expression: Exp_poly expected."
    in
    let _vars_local = !(cl_env.vars) in
    let substs =
      match ty_constr, ty with
        None, _ | Some _, None -> cl_env.substs
      | Some ty_exp, Some ty ->
        match Typecheck_typing.instance { cl_env.ctx with env = cl_env.val_env }
                ty ty_exp cl_env.substs with
          Ok (substs, _) -> substs
        | Error _ -> failwith "Incompatible types"
    in
    let expected = match ty with
        Some ty -> newgenty (Tarrow ("", self_type, ty, Cok))
      | None -> expr.exp_type
    in
    (* let expected = Typecheck_typing.apply_subst expected substs in *)
    (* print_debug *)
    (*   (Format.asprintf "Type of the method afer constraint application:\n%a" *)
    (*      Printtyp.raw_type_expr expected); *)
    (* if !Typecheck_flags.debug then begin *)
    (*     Format.printf "Env values before meth %s:\n%!" name.txt; *)
    (*     Env.fold_values (fun s p vd _ -> *)
    (*         Format.printf "(%s, %a, %a);\n%!" *)
    (*           s Typecheck_pretty.path p *)
    (*           Typecheck_pretty.Types.value_kind vd.val_kind) None *)
    (*       cl_env.meth_env () *)
    (* end; *)
    let _ = type_expr_aux { cl_env.ctx with env = cl_env.meth_env }
        expr expected in
    { cl_env with tvars; substs; },
    { cl_ctx with
      concr_meths = Concr.add name.txt cl_ctx.concr_meths;
      local_meths = Concr.add name.txt cl_ctx.local_meths; }
  | _ -> assert false

and type_object ctx loc cl_str : Types.class_signature =
  incr cl_num;
  let csig, _ =
    type_class_structure
      (string_of_int !cl_num)
      true
      (new_cl_env ctx Variables.empty_variables) loc cl_str in
  csig

type class_decl_infos =
  { cl_id : Ident.t;
    cl_desc : Types.class_declaration;
    cty_id : Ident.t;
    cty_desc : Types.class_type_declaration;
    ty_id : Ident.t;
    ty_desc : Types.type_declaration;
    opty_id : Ident.t;
    opty_desc : Types.type_declaration;
  }

let class_decl_infos def_class kind ctx cl_num cl
    (cl_id, cty_id, ty_id, opty_id) =
  Typecheck_ctype.begin_class_def ();
  let tyvars, vars = List.fold_left (fun (tys, vars) (cty, variance) ->
      let ty, vars =
        transl_ctype_aux
          ctx vars ~decl:true Extensible true cty in
      (ty, variance) :: tys, vars)
      ([], Variables.empty_variables) cl.ci_params in
  let tyvars = List.rev tyvars in
  let params, variance = List.split tyvars in
  let cl_env = new_cl_env ctx vars in
  let cl_env =
    match Typecheck_typing.instance_types
            cl_env.ctx
            (List.map (fun (cty, _) -> cty.ctyp_type) cl.ci_params)
            params
            cl_env.substs
    with
      Ok (substs, ctx) -> { cl_env with substs; ctx }
    | Error _ -> assert false in
  let params = Typecheck_typing.apply_types params cl_env.substs in

  let cty, cl_env = kind (new_cl_env ctx vars) cl.ci_expr in

  Typecheck_ctype.end_def();
  let self_type = Ctype.self_type cty in

  (* Generalization *)
  print_debug (
    Format.asprintf "cdi, fields: %a" Printtyp.raw_type_expr self_type);
  let (fields, _) = Ctype.flatten_fields (Ctype.object_fields self_type) in
  List.iter (fun (met, _, ty) -> if met = dummy_method then Ctype.generalize ty)
    fields;
  (* Generalize the row variable *)
  let rv = Ctype.row_variable self_type in
  List.iter (Ctype.limited_generalize rv) params;
  Ctype.limited_generalize rv self_type;


  (* Generating the object type *)
  let ty_params, obj_cl = Ctype.instance_class params cty in
  let obj_ty = Ctype.self_type obj_cl in
  let s = Format.asprintf "obj_ty: %a" Printtyp.raw_type_expr obj_ty in
  print_debug s;
  Ctype.close_object obj_ty;

  (* Generating the opened object type *)
  let opty_params, opty_cl = Ctype.instance_class params cty in
  let op_ty = Ctype.self_type opty_cl in
  Ctype.hide_private_methods op_ty;

  begin
    match Typecheck_typing.instance ctx obj_ty self_type TyMap.empty with
      Ok (_, _) -> ()
    | Error e ->
      Typecheck_typing.print_error Format.err_formatter (e, cl.ci_loc);
      failwith "Type abbreviation builded seems incorrect"
  end;
  (* Workaround: *dummy_method* will be set as absent otherwise, so we do it
     after checking the instantiation. *)
  Ctype.hide_private_methods obj_ty;

  let cl_cty = {
    cty_params = params;
    cty_variance = cl.ci_type_decl.clty_variance;
    cty_type = cty;
    cty_new =
      (match cl.ci_virt with Virtual -> None | Concrete -> Some obj_ty);
    cty_path = Path.Pident ty_id;
    cty_loc = cl.ci_loc;
    cty_attributes = cl.ci_attributes;
  } in
  let cl_clty = {
    clty_params = params;
    clty_variance = cl.ci_type_decl.clty_variance;
    clty_type = cty;
    clty_path = Path.Pident ty_id;
    clty_loc = cl.ci_loc;
    clty_attributes = cl.ci_attributes;
  } in
  let ctx = { ctx with
              env =
                Env.add_cltype cty_id cl_clty
                  (if def_class then Env.add_class cl_id cl_cty ctx.env
                   else ctx.env) } in

  if cl.ci_virt = Concrete then
    begin
      let sg = Ctype.signature_of_class_type cty in
      let mets = virtual_methods sg in
      let vals = Vars.fold (fun n (_, vr, _) m ->
          if vr = Virtual then n :: m else m) sg.csig_vars [] in
      if mets <> [] || vals <> [] then failwith "Virtual class"
    end;

  let obj_decl = {
    type_params = ty_params;
    type_arity = List.length params;
    type_kind = Type_abstract;
    type_private = Public;
    type_manifest = Some obj_ty;
    type_variance = cl_cty.cty_variance;
    type_newtype_level = None;
    type_loc = cl.ci_loc;
    type_attributes = [];
  } in
  Ctype.set_object_name ty_id (Ctype.row_variable op_ty) opty_params op_ty;
  let cl_decl = {
    obj_decl with
    type_params = opty_params;
    type_manifest = Some op_ty;
  } in
  ((cl_id, cl_cty), (cty_id, cl_clty), (ty_id, obj_decl), (opty_id, cl_decl)), ctx

let init_env define_class approx ctx (cl_id, cty_id, ty_id, opty_id)
    (cl : 'a class_infos) =
  let approx_type_decl ct =
    let ty = approx ct in
    let params =  Typecheck_types.extract_vars_list [] ty in
    { type_params = params;
      type_arity = List.length params;
      type_kind = Type_abstract;
      type_manifest = Some ty;
      type_private = Public;
      type_variance = cl.ci_type_decl.clty_variance;
      type_newtype_level = None;
      type_loc = Location.none;
      type_attributes = [] } in
  let env = Env.add_class cl_id cl.ci_decl @@
    Env.add_cltype cty_id cl.ci_type_decl @@
    Env.add_type ~check:false ty_id (approx_type_decl cl.ci_decl.cty_type) @@
    Env.add_type
      ~check:false opty_id (approx_type_decl cl.ci_decl.cty_type) ctx.env
  in
  { ctx with env }

let gen_env define ctx
    ((cl_id, cl_cty), (cty_id, cl_clty), (ty_id, obj_decl), (opty_id, cl_decl)) =
  let env =
    Env.add_type ~check:true ty_id
      (Subst.type_declaration Subst.identity obj_decl) (
      Env.add_type ~check:true opty_id
        (Subst.type_declaration Subst.identity cl_decl) (
        Env.add_cltype cty_id (Subst.cltype_declaration Subst.identity cl_clty) (
          if define then
            Env.add_class
              cl_id (Subst.class_declaration Subst.identity cl_cty) ctx.env
          else ctx.env))) in
  { ctx with env }

let type_class_declarations define_class kind approx ctx
    (cls: ('a class_infos) list) =
  let ids =
    List.map (fun cl ->
      (cl.ci_id_class, cl.ci_id_class_type,
       cl.ci_id_object, cl.ci_id_typesharp)) cls in
  let temp_ctx = List.fold_left2 (init_env define_class approx) ctx ids cls in
  let rev_decls, temp_ctx =
    List.fold_left2 (fun (prev, ctx) ids cl ->
        incr cl_num;
        let (curr_ids, ctx) =
          class_decl_infos
            define_class kind ctx (string_of_int !cl_num) cl ids in
        curr_ids :: prev, ctx) ([], temp_ctx) ids cls in
  let decls = List.rev rev_decls in
  let ctx = List.fold_left (gen_env define_class) ctx decls in

  let final_decls =
    let first = ref true in
    let is_first () =
      if !first then (first := false; Trec_first) else Trec_next in
    List.map (fun ((cl_id, cl_cty),
                   (cty_id, cl_clty),
                   (ty_id, obj_decl),
                   (opty_id, cl_decl)) ->

               List.iter Ctype.generalize cl_cty.cty_params;
               generalize_class_type true cl_cty.cty_type;
               Typecheck_utils.may  Ctype.generalize cl_cty.cty_new;
               List.iter Ctype.generalize obj_decl.type_params;
               Typecheck_utils.may  Ctype.generalize obj_decl.type_manifest;
               List.iter Ctype.generalize cl_decl.type_params;
               Typecheck_utils.may  Ctype.generalize cl_decl.type_manifest;

               let rs = is_first () in
               let sg =
                 [Sig_class_type (cty_id, cl_clty, rs);
                  Sig_type(ty_id, obj_decl, rs);
                  Sig_type(opty_id, cl_decl, rs)] in
               if define_class then Sig_class (cl_id, cl_cty, rs) :: sg else sg)
      decls in
  List.flatten final_decls, ctx

let type_class_decl ctx (cls: (class_expr class_infos * string list * 'b) list) =
  incr cl_num;
  let cls = List.map (fun (cl, _, _) -> cl) cls in
  type_class_declarations
    true (type_class_expr (string_of_int !cl_num)) approx_class ctx cls

let type_class_types ctx cls =
  let cls = List.map (fun (_, _, cl) -> cl) cls in
  type_class_declarations false (transl_class_type 0) approx_class ctx cls

let print_error fmt = function
    Self_type_different (ty, ty') ->
    Format.fprintf fmt "The self types are not equivalent: %a & %a."
      Printtyp.raw_type_expr ty Printtyp.raw_type_expr ty'
  | Not_an_object ty ->
    Format.fprintf fmt "An object was expected. %a is not an object type."
      Printtyp.type_expr ty
  | Undeclared_method m ->
    Format.fprintf fmt "The method %s is missing." m
  | Illformed_object_type ty ->
    Format.fprintf fmt
      "The object type %a is illformed." Printtyp.raw_type_expr ty

let print_error fmt (e, loc) =
  Format.fprintf fmt "%a\n%a\n"
    Location.print_loc loc
    print_error e

let () =
  Typecheck_expr.type_object := type_object
