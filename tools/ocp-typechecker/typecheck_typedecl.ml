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

open Asttypes
open Typecheck_flags
open Typedtree
open Types
open Typecheck_ctype
open Typecheck_utils
open Typecheck_typexpr
open Typecheck_result
open Typecheck_types

(* module Ctype = Typecheck_ctype *)

type error =
    Incoherent_constraints of (type_expr * type_expr) list
  | Unextensible_type of Path.t
  | No_row_variable
  | Generalized_incorrect_return_path of Path.t * Path.t
  | Generalized_incorrect_return_type of Path.t * type_expr
  | Typecheck_inconsistence of string
  | Cyclic_abbreviation
  | Inconsistent_constraint of type_expr
  | Definition_mismatch
  | Redefinition_mismatch
  | Unbound_type_constructor of Path.t
  | Value_declaration_mismatch of type_expr * type_expr
  | Extension_arity_mismatch
  | Unbound_constructor of Path.t


exception Typedecl_error of (error * Location.t)


let raise_error loc e =
  raise (Typedecl_error (e, loc))

(* Determine if a type definition defines a fixed type. (PW)
   Adapted for Typedtree from Typedecl
*)
let is_fixed_type td =
  let rec has_row_var cty =
    match cty.ctyp_desc with
      Ttyp_alias (cty, _) -> has_row_var cty
    | Ttyp_class _
    | Ttyp_object (_, Open)
    | Ttyp_variant (_, Open, _)
    | Ttyp_variant (_, Closed, Some _) -> true
    | _ -> false
  in
  match td.typ_manifest with
    None -> false
  | Some cty ->
      td.typ_kind = Ttype_abstract &&
      td.typ_private = Private &&
      has_row_var cty

(* Set the row variable in a fixed type *)
let set_fixed_row env loc p decl =
  let tm =
    match decl.type_manifest with
      None -> assert false
    | Some t -> Ctype.expand_head env t
  in
  let rv =
    match tm.desc with
      Tvariant row ->
        let row = Btype.row_repr row in
        tm.desc <- Tvariant {row with row_fixed = true};
        if Btype.static_row row then Btype.newgenty Tnil
        else row.row_more
    | Tobject (ty, _) ->
        snd (Ctype.flatten_fields ty)
    | _ ->
      raise_error loc No_row_variable
  in
  if not (Btype.is_Tvar rv) then
    raise_error loc No_row_variable;
  rv.desc <- Tconstr (p, decl.type_params, ref Mnil)

let narrow vars =
  increase_global_level (), vars.Variables.vars

let reset_type_variables vars =
  reset_global_level ();
  Variables.{ vars with vars = SMap.empty }

let widen (gl, v) vars =
  restore_global_level gl;
  Variables.{ vars with vars = v }

let make_constructor env loc path tyargs args ret =
  match ret with
    None ->
    let targs = List.map (fun arg ->
        fst @@ transl_ctype_aux env tyargs Extensible false arg)
        args in
    targs, None
  | Some ret ->
    let z = narrow tyargs in
    let vars = reset_type_variables tyargs in
    let args, vars = List.fold_left (fun (tys, vars) arg ->
        let ty, vars =
          transl_ctype_aux env vars Extensible true arg in
        ty :: tys, vars) ([], vars) args in
    (* The result type of the GADT can generate new type variables *)
    let ret, _ =
      transl_ctype_aux env vars Extensible true ret in
    begin
      let ret = repr ret in
      match ret.desc with
        Tconstr (p', _, _) when Path.same path p' ->
        print_debug (Format.asprintf "path res: %a, path exp: %a"
          Typecheck_pretty.path p' Typecheck_pretty.path path)
      | Tconstr (p', _, _) ->
        raise_error loc @@ Generalized_incorrect_return_path (path, p')
      | _ ->
        raise_error loc @@ Generalized_incorrect_return_type (path, ret)
    end;
    let _vars = widen z vars in
    List.rev args, Some ret

let is_float env ty =
  match Ctype.repr (Ctype.expand_head_opt env ty) with
    {desc = Tconstr(p, _, _)} -> Path.same p Predef.path_float
  | _ -> false

let verify_constraints env loc cstrs =
  let subst = List.fold_left (fun subst (tvar, tcstr) ->
      match subst with
        Error _ -> subst
      | Ok (subst, ctx) ->
        Typecheck_typing.instance ctx tcstr tvar subst)
      (Ok (Typecheck_types.TyMap.empty, Typecheck_types.create_context env))
      cstrs in
  match subst with
    Ok (subst, ctx) -> subst
  | Error _ -> raise_error loc @@ Incoherent_constraints cstrs

let check_type_redefinition loc ctx man kind =
  match kind, man with
    Type_abstract, _ | _, None -> ()
  | _, Some t ->
    match (Btype.repr t).desc with
    | Tconstr (p, vars, _) ->
      let td = Env.find_type p ctx.env in
      let subst =
        Typecheck_typing.instance_types ctx vars td.type_params TyMap.empty in
      begin
        match subst with
          Error _ -> raise_error loc Redefinition_mismatch
        | Ok (subst, _) ->
          let kind' = Typecheck_typing.apply_kind td.type_kind subst in
          match Typecheck_typing.eq_kind ctx kind kind' with
            Ok _ -> ()
          | Error _ -> raise_error loc Redefinition_mismatch
      end
    | _ -> raise_error loc Redefinition_mismatch
      
let transl_typedecl env id decl =
  begin_def();
  (* Generating type arguments *)
  let ctx = create_context env in
  let loc = decl.typ_loc in
  let _tdecl = decl.typ_type in
  let tyvars, vars = List.fold_left
      (fun (tys, vars) (cty, variance) ->
         let ty, vars =
           transl_ctype_aux
             ctx
             vars ~decl:true Extensible true cty in
         (ty, variance) :: tys, vars)
      ([], Variables.empty_variables) decl.typ_params in
  print_debug (
    Format.asprintf "transl_tydecl vars: [%a]"
       Variables.print vars);
  let tyvars = List.rev tyvars in
  (* Typing constraints (not verifying) and generating *)
  let cstrs, vars = List.fold_left (fun (cstrs, vars) (cty, cty', _) ->
      let ty, vars = transl_ctype_aux ctx vars Extensible false cty in
      let ty', vars =
        transl_ctype_aux ctx vars Extensible true cty' in
      (ty, ty') :: cstrs, vars) ([], vars) decl.typ_cstrs in
  let cstrs = List.rev cstrs in
  let subst = verify_constraints env decl.typ_loc cstrs in
  (* Typing the declaration *)
  let kind = match decl.typ_kind with
      Ttype_abstract -> Type_abstract
    | Ttype_variant cstrs ->
      if cstrs = [] then
        raise_error loc @@ Typecheck_inconsistence
          "This sum type declaration has no constructor.";
      let cstrs' = List.map (fun cstr ->
          let id_cstr = Ident.create cstr.cd_name.txt in
          let args, ret =
            make_constructor ctx
              cstr.cd_loc
              (Path.Pident id) vars cstr.cd_args cstr.cd_res in
          { cd_id = id_cstr;
            cd_args = Typecheck_typing.apply_types args subst;
            cd_res = Typecheck_typing.apply_opt ret subst;
            cd_loc = cstr.cd_loc;
                    cd_attributes = cstr.cd_attributes; }) cstrs in
      Type_variant cstrs'
    | Ttype_record l ->
      if l = [] then
        raise_error loc @@ Typecheck_inconsistence
          "This record reclaration has no fields.";
      let lbls = List.map (fun (ld : Typedtree.label_declaration) ->
          let cty = force_poly ld.ld_type in
          let ty, _ =
            transl_ctype_aux ctx vars Extensible false cty in
          Types.({ ld_id = ld.ld_id;
                   ld_mutable = ld.ld_mutable;
                   ld_type = (match ty.desc with
                         Tpoly (t, []) -> Typecheck_typing.apply_subst t subst
                       | _ -> Typecheck_typing.apply_subst ty subst);
                   ld_loc = ld.ld_loc;
                   ld_attributes = ld.ld_attributes; })) l in
      let rep = if List.for_all (fun l -> is_float env l.ld_type) lbls
        then Record_float
        else Record_regular in
      Type_record (lbls, rep)
    | Ttype_open -> Type_open in
  (* Typing the manifest *)
  let man = match decl.typ_manifest with
      None -> None
    | Some cty ->
      let no_row = if not (is_fixed_type decl) then Fixed else Extensible in
      let ty = fst @@
        transl_ctype_aux ctx vars no_row false cty in
      Some (Typecheck_typing.apply_subst ty subst) in
  check_type_redefinition loc ctx man kind;
  let tdecl = {
    type_params = List.map (fun (tyvar, _) ->
        Typecheck_typing.apply_subst tyvar subst) tyvars;
    type_arity = List.length tyvars;
    type_kind = kind;
    type_private = decl.typ_private;
    type_manifest = man;
    type_variance = decl.typ_type.type_variance;
      (* List.map (fun _ -> Variance.full) tyvars; *)
    type_newtype_level = None;
    type_loc = decl.typ_loc;
    type_attributes = decl.typ_attributes;
  } in
  end_def ();
  if is_fixed_type decl then begin
    (* let (p, _) = *)
    (*   try Env.lookup_type (Longident.Lident(Ident.name id ^ "#row")) env *)
    (*   with Not_found -> assert false in *)
    assert false
    (* set_fixed_row env decl.type_loc p decl *)
  end;
  (* Check for cyclic abbreviations *)
  begin match man with
      None -> ()
    | Some ty ->
      if Typecheck_ctype.cyclic_abbrev env id ty then
        raise_error loc Cyclic_abbreviation
  end;
  begin
    match Typecheck_typing.eq_type_decl (create_context env)
            ~strict:true id _tdecl id tdecl with
      Ok _ -> ()
    | Error _ -> failwith "Not equal"
  end;
  _tdecl

let generalize_decl decl =
  List.iter generalize decl.type_params;
  begin match decl.type_kind with
    Type_abstract ->
      ()
  | Type_variant v ->
      List.iter
        (fun c ->
          List.iter Typecheck_ctype.generalize c.Types.cd_args;
          Misc.may Typecheck_ctype.generalize c.Types.cd_res)
        v
  | Type_record(r, rep) ->
      List.iter (fun l -> Typecheck_ctype.generalize l.Types.ld_type) r
  | Type_open ->
      ()
  end;
  begin match decl.type_manifest with
  | None    -> ()
  | Some ty -> Typecheck_ctype.generalize ty
  end

(* From Typedecl *)

module TypeSet = Btype.TypeSet
module TypeMap = Btype.TypeMap

let check_well_founded env loc path to_check ty =
  let open Typedecl in
  let visited = ref TypeMap.empty in
  let rec check ty0 exp_nodes ty =
    let ty = Btype.repr ty in
    if TypeSet.mem ty exp_nodes then begin
      (*Format.eprintf "@[%a@]@." Printtyp.raw_type_expr ty;*)
      if match ty0.desc with
      | Tconstr (p, _, _) -> Path.same p path
      | _ -> false
      then raise (Typedecl.Error (loc, Recursive_abbrev (Path.name path)))
      else raise (Typedecl.Error (loc, Cycle_in_def (Path.name path, ty0)))
    end;
    let (fini, exp_nodes) =
      try
        let prev = TypeMap.find ty !visited in
        if TypeSet.subset exp_nodes prev then (true, exp_nodes) else
        (false, TypeSet.union exp_nodes prev)
      with Not_found ->
        (false, exp_nodes)
    in
    let snap = Btype.snapshot () in
    if fini then () else try
      visited := TypeMap.add ty exp_nodes !visited;
      match ty.desc with
      | Tconstr(p, args, _)
        when not (TypeSet.is_empty exp_nodes) || to_check p ->
          let ty' = Ctype.try_expand_once_opt env ty in
          let ty0 = if TypeSet.is_empty exp_nodes then ty else ty0 in
          check ty0 (TypeSet.add ty exp_nodes) ty'
      | _ -> raise Ctype.Cannot_expand
    with
    | Ctype.Cannot_expand ->
        let nodes =
          if !Clflags.recursive_types && Ctype.is_contractive env ty
          || match ty.desc with Tobject _ | Tvariant _ -> true | _ -> false
          then TypeSet.empty
          else exp_nodes in
        Btype.iter_type_expr (check ty0 nodes) ty
    | Ctype.Unify _ ->
        (* Will be detected by check_recursion *)
        Btype.backtrack snap
  in
  check ty TypeSet.empty ty


let check_manifest env path decl =
  match decl.type_manifest with
    None -> ()
  | Some ty ->
  let args = List.map (fun _ -> Ctype.newvar()) decl.type_params in
  check_well_founded env decl.type_loc path (Path.same path) (Ctype.newconstr
                                                                path args)

let check_decl env path decl to_check =
  let open Btype in
  let it =
    {type_iterators with
     it_type_expr = (fun _ -> check_well_founded env decl.type_loc path to_check)} in
  it.it_type_declaration it (Ctype.instance_declaration decl)

(* Check for ill-defined abbrevs *)

let check_recursion env loc path decl to_check =
  let open Typedecl in
  (* to_check is true for potentially mutually recursive paths.
     (path, decl) is the type declaration to be checked. *)

  if decl.type_params = [] then () else

  let visited = ref [] in

  let rec check_regular cpath args prev_exp ty =
    let ty = Ctype.repr ty in
    if not (List.memq ty !visited) then begin
      visited := ty :: !visited;
      match ty.desc with
      | Tconstr(path', args', _) ->
          if Path.same path path' then begin
            if not (Ctype.equal env false args args') then
              raise (Error(loc,
                     Parameters_differ(cpath, ty, Ctype.newconstr path args)))
          end
          (* Attempt to expand a type abbreviation if:
              1- [to_check path'] holds
                 (otherwise the expansion cannot involve [path]);
              2- we haven't expanded this type constructor before
                 (otherwise we could loop if [path'] is itself
                 a non-regular abbreviation). *)
          else if to_check path' && not (List.mem path' prev_exp) then begin
            try
              (* Attempt expansion *)
              let (params0, body0, _) = Env.find_type_expansion path' env in
              let (params, body) =
                Ctype.instance_parameterized_type params0 body0 in
              begin
                try List.iter2 (Ctype.unify env) params args'
                with Ctype.Unify _ ->
                  raise (Error(loc, Constraint_failed
                                 (ty, Ctype.newconstr path' params0)));
              end;
              check_regular path' args (path' :: prev_exp) body
            with Not_found -> ()
          end;
          List.iter (check_regular cpath args prev_exp) args'
      | Tpoly (ty, tl) ->
          let (_, ty) = Ctype.instance_poly ~keep_names:true false tl ty in
          check_regular cpath args prev_exp ty
      | _ ->
          Btype.iter_type_expr (check_regular cpath args prev_exp) ty
    end in

  Misc.may
    (fun body ->
      let (args, body) =
        Ctype.instance_parameterized_type
          ~keep_names:true decl.type_params body in
      check_regular path args [] body)
    decl.type_manifest

let check_abbrev_recursion env id to_check decl =
  check_recursion env decl.type_loc (Path.Pident id) decl to_check

(* Force recursion to go through id for private types*)
let name_recursion tdecl id decl =
  match decl with
  | { type_kind = Type_abstract;
      type_manifest = Some ty;
      type_private = Private; } when is_fixed_type tdecl ->
    let ty = Ctype.repr ty in
    let ty' = Btype.newty2 ty.level ty.desc in
    if Ctype.deep_occur ty ty' then
      let td = Tconstr(Path.Pident id, decl.type_params, ref Mnil) in
      Btype.link_type ty (Btype.newty2 ty.level td);
      {decl with type_manifest = Some ty'}
    else decl
  | _ -> decl

let check_constraints env loc decl =
  let visited = ref TypeSet.empty in
  let rec check env ty =
    let ty = repr ty in
    if not @@ TypeSet.mem ty !visited then
      let _ = visited := TypeSet.add ty !visited in
      match ty.desc with
        Tconstr (p, args, _ ) ->
        let ty'= newconstr p (List.map (fun _ -> newvar ()) args) in
        begin try enforce_constraints env ty'
          with _ ->
            raise_error loc @@ Inconsistent_constraint ty
        end;
        begin
          match Typecheck_typing.instance' env ty ty' with
            Error _ -> raise_error loc @@
            Incoherent_constraints [ty, ty']
          | Ok _ -> List.iter (check env) args
        end
      | Tpoly (ty, tl) ->
        let _, ty = instance_poly false tl ty in
        check env ty
      | _ -> Btype.iter_type_expr (check env) ty
  in
  begin match decl.type_kind with
    Type_abstract -> ()
  | Type_variant cstrs ->
    List.iter (fun { cd_args; cd_res } ->
        List.iter (check env) cd_args;
        match cd_res with
          None -> ()
        | Some ty -> check env ty) cstrs
  | Type_record (l, _) ->
    List.iter (fun { ld_type } -> check env ld_type) l
  | Type_open -> ()
  end;
  match decl.type_manifest with
    None -> ()
  | Some ty -> check env ty

let check_coherence env id loc decl =
  match decl with
    { type_kind = ( Type_variant _ | Type_open | Type_record _ );
      type_manifest = Some ty } ->
    begin match (repr ty).desc with
        Tconstr (p, args, _) ->
        begin try let mdecl = Env.find_type p env in
            if List.length mdecl.type_params <> List.length args then
              raise_error loc @@ Typecheck_inconsistence
                "Number of type parameters is different from the number of \
                 arguments of the type manifest.";
            if not @@ equal env false args decl.type_params then
              raise_error loc @@ Typecheck_inconsistence
                "Type parameters et arguments of manifests are differents.";
            let errs =
              Includecore.type_declarations ~equality:true env
                (Path.last p) mdecl
                id (Subst.type_declaration
                      (Subst.add_type id p Subst.identity) decl) in
            if errs <> [] then
              raise_error loc Definition_mismatch
          with Not_found ->
            raise_error loc @@ Unbound_type_constructor p
        end
      | _ -> raise_error loc Definition_mismatch
    end
  | _ -> ()

(* Current version:
   - no variance

*)
let type_tydecl env (* path *) decls =
  print_debug "Generating ids";
  let ids =
    List.map (fun decl ->
        print_debug (Format.asprintf "Id:%a" Printtyp.ident decl.typ_id);
        decl.typ_id
        (* Ident.create decl.typ_name.txt *)) decls in
  Ctype.init_def (Ident.current_time ());
  begin_def ();

  print_debug "Generating temp_env";
  let temp_env = List.fold_left2 (fun env decl id ->
      Env.add_type ~check:false id decl.typ_type env) env decls ids in
  print_debug "Translating";
  let tdecls = List.map2 (transl_typedecl temp_env) ids decls in
  print_debug "Generating new env";
  let new_env = List.fold_left2 (fun env decl id ->
      Env.add_type ~check:false id decl env) env tdecls ids in
  end_def ();
  print_debug (Format.asprintf "Typedecls, before gen (level:%d):\n%a"
    (Ctype.get_current_level())
    Typecheck_pretty.Types.type_declaration_list tdecls);
  List.iter generalize_decl tdecls;
  print_debug (Format.asprintf "Typedecls, after gen:\n%a"
    Typecheck_pretty.Types.type_declaration_list tdecls);
  (* Verify manifest (check_well_founded_manifest) *)
  List.iter2 (fun decl id ->
      check_manifest new_env (Path.Pident id) decl) tdecls ids;
  let to_check =
    function Path.Pident id -> List.mem id ids | _ -> false in
  List.iter2 (fun decl id ->
      check_decl new_env (Path.Pident id) decl to_check) tdecls ids;
  List.iter2 (fun decl id ->
      check_abbrev_recursion new_env id to_check decl) tdecls ids;
  (* Checking that all type variables are closed
  *)
  List.iter
    (fun decl ->
       let open Typedecl in
       match Ctype.closed_type_decl decl with
         Some ty -> raise(Error(decl.type_loc, Unbound_type_var(ty,decl)))
       | None   -> ())tdecls;
  let tdecls = List.map2 (fun id (decl, tdecl) ->
      name_recursion decl id tdecl) ids @@ List.combine decls tdecls in
  let locs = List.map (fun decl -> decl.typ_loc) decls in
  (* Check constraints *)
  List.iter2 (check_constraints new_env) locs tdecls;
  iter3 (check_coherence new_env) ids locs tdecls;
  (* Compute variance *)
  let first = ref true in
  let is_first () = if !first then (first := false; Trec_first) else Trec_next in
  map3 (fun id orig tdecl ->
      print_debug (Format.asprintf "orig: type %a = %a\n \
                                            new:type %a = \n %a\n%!\
                                            first: %b\n%!"
                             Printtyp.ident id
                             Typecheck_pretty.Types.type_declaration orig.typ_type
                             Printtyp.ident id
                             Typecheck_pretty.Types.type_declaration tdecl !first);
      id, tdecl, is_first ())
    ids decls tdecls, new_env


let type_constraint_decl env orig_id id orig_decl decl =
  begin_def();
  let ctx = create_context env in
  let tyvars, vars = List.fold_left (fun (tys, vars) (cty, variance) ->
      let ty, vars =
        transl_ctype_aux ctx vars Extensible true cty in
      (ty, variance) :: tys, vars)
      ([], get_current_vars ())
      decl.typ_params in
  let tyvars = List.rev tyvars in
  let arity_ok = List.length tyvars = orig_decl.type_arity in
  (* Typing constraints (not verifying) and generating *)
  let cstrs, vars = List.fold_left (fun (cstrs, vars) (cty, cty', _) ->
      let ty, vars =
        transl_ctype_aux ctx vars Extensible false cty in
      let ty', vars =
        transl_ctype_aux ctx vars Extensible true cty' in
      (ty, ty') :: cstrs, vars) ([], vars) decl.typ_cstrs in
  let subst = verify_constraints env orig_decl.type_loc cstrs in
  let _no_row = not (is_fixed_type decl) in
  (* Typing the manifest *)
  let man = match decl.typ_manifest with
      None -> None
    | Some cty ->
      let no_row = if not (is_fixed_type decl) then Fixed else Extensible in
      let ty = fst @@
        transl_ctype_aux ctx vars no_row false cty in
      Some (Typecheck_typing.apply_subst ty subst) in
  let priv =
    if decl.typ_private = Private then Private else
    if arity_ok && orig_decl.type_kind <> Type_abstract
    then orig_decl.type_private else decl.typ_private
  in
  let decl' = {
    type_params = List.map (fun (tyvar, _) ->
        Typecheck_typing.apply_subst tyvar subst) tyvars;
    type_arity = List.length tyvars;
    type_kind =
      if arity_ok && man <> None then orig_decl.type_kind else Type_abstract;
    type_private = priv;
    type_manifest = man;
    type_variance = [];
    type_newtype_level = None;
    type_loc = decl.typ_loc;
    type_attributes = decl.typ_attributes;
  } in
  begin match id with None -> ()
                    | Some p -> set_fixed_row env decl.typ_loc p decl'
  end;
  begin match Ctype.closed_type_decl decl' with
      None -> ()
    | Some ({ desc = (Tunivar (Some v) | Tvar (Some v))} as ty) ->
      begin
        try ignore @@ find_var ~generate:false decl.typ_loc v ty vars
        with Not_found ->
          raise(Typedecl.Error(decl.typ_loc,
                             Typedecl.Unbound_type_var(ty,decl')))
      end
    | Some ty ->
      raise(Typedecl.Error(decl.typ_loc,
                           Typedecl.Unbound_type_var(ty,decl')))
  end;
  let decl' = name_recursion decl orig_id decl' in
  end_def();
  generalize_decl decl';
  decl'

let transl_extension_constructor ctx loc type_path type_params typext_params
    vars tdecl extc =
  let args, ret =
    match extc.ext_kind with
      Text_decl (args, ret) ->
      make_constructor ctx extc.ext_loc type_path vars args ret
    | Text_rebind (p, lid) ->
      let constr =
        try Env.lookup_constructor lid.txt ctx.env
        with Not_found -> raise (Typedecl_error (Unbound_constructor p, loc))
      in
      let args, ret = Ctype.instance_constructor constr in
      let res, cstr_ret =
        if constr.cstr_generalized then
          let res = Ctype.newconstr type_path type_params in
          res, Some res
        else Ctype.newconstr type_path typext_params, None in
      begin
        match Typecheck_typing.instance ctx ret res TyMap.empty with
          Ok _ -> ()
        | Error e -> raise (Typecheck_typing.Typing_error (e, loc))
      end;
      assert false
  in
  { extc.ext_type with ext_type_path = type_path;
                        ext_type_params = typext_params;
                        ext_args = args;
                        ext_ret_type = ret;
  }

let rec is_extensible env man = function
    Type_open -> true
  | Type_abstract ->
    (* check manifest -> normalize -> try again *)
    begin
      match man with
        Some { desc = Tconstr (p, _, _); } ->
        let decl = Env.find_type p env in
        is_extensible env decl.type_manifest decl.type_kind
      | _ -> false
    end
  | _ -> false

let type_typext env te =
  Ctype.begin_def();
  let ctx = create_context env in
  let type_decl = Env.find_type te.tyext_path env in
  if not @@ is_extensible env type_decl.type_manifest type_decl.type_kind then
    raise_error te.tyext_txt.Location.loc (Unextensible_type te.tyext_path);

  let ids = List.map (fun ext -> ext.ext_id) te.tyext_constructors in

  (* Extract the bounded variables and translate the core type into an OCaml
     internal type. *)
  let tyvars, vars = List.fold_left (fun (tys, vars) (cty, variance) ->
      let ty, vars =
        transl_ctype_aux
          ctx Variables.empty_variables ~decl:true Extensible true cty
      in
      (ty, variance) :: tys, vars)
      ([], Variables.empty_variables) te.tyext_params in

  (* Check for variance *)
  let tyext_params = List.map fst tyvars in
  let type_variance =
    List.map (fun v ->
                let (co, cn) = Variance.get_upper v in
                  (not cn, not co, false))
      type_decl.type_variance in
  List.iter2 (fun (_, v) v' -> (* check variance are equals *)
      ()) tyvars type_variance;
  let constructors =
    List.map (transl_extension_constructor ctx te.tyext_txt.loc te.tyext_path
                type_decl.type_params tyext_params vars te)
      te.tyext_constructors in
  Ctype.end_def ();

  (* Generalization *)
  List.iter Ctype.generalize tyext_params;
  List.iter
    (fun ext ->
       List.iter Ctype.generalize ext.ext_args;
       may Ctype.generalize ext.ext_ret_type)
    constructors;
  List.iter
    (fun ext ->
       match Ctype.closed_extension_constructor ext with
         Some ty ->
         raise(Typedecl.Error(ext.ext_loc, Typedecl.Unbound_type_var_ext(ty, ext)))
       | None -> ())
    constructors;
  let env = List.fold_left2 (fun ext id ext ->
      Env.add_extension id ext ~check:true env) env ids constructors in
  let constructors =
    let first = ref true in
    let is_first () = if !first then (first := false; Text_first) else Text_next in
    List.map2 (fun id cstr -> id, cstr, is_first ())
      ids constructors in
  constructors, env

let type_value_decl ctx vd =
  let ty = Typecheck_typexpr.transl_ctype ctx vd.val_desc in
  begin
    match Typecheck_typing.eq ctx ty vd.val_val.val_type with
      Ok _ -> ()
    | Error _ ->
      raise_error vd.val_loc @@
      Value_declaration_mismatch (ty, vd.val_val.val_type)
  end;
  let newenv = Env.add_value vd.val_id vd.val_val ctx.env in
  Sig_value (vd.val_id, vd.val_val), { ctx with env = newenv }


let print_cstrs fmt cstrs =
  match cstrs with
    [] -> ()
  | (tvar, tcstr) :: cstrs' ->
    Format.fprintf fmt "%a = %a"
      Printtyp.type_expr tvar Printtyp.type_expr tcstr;
    List.iter (fun (tvar', tcstr') ->
    Format.fprintf fmt "&& %a = %a"
      Printtyp.type_expr tvar' Printtyp.type_expr tcstr') cstrs'

let print_error fmt = function
    Incoherent_constraints cstrs ->
    Format.fprintf fmt "The following set of constraints is incoherent:\n%a"
      print_cstrs cstrs
  | Unextensible_type p ->
    Format.fprintf fmt "Type %a is not extensible"
      Typecheck_pretty.path p
  | No_row_variable ->
    Format.fprintf fmt "This type has no row variable."
  | Generalized_incorrect_return_path (res, ret) ->
    Format.fprintf fmt
      "This generalized constructor return a type constructor %a,\n\
       while it is expected to be %a."
      Printtyp.path ret Printtyp.path res
  | Generalized_incorrect_return_type (res, ty) ->
    Format.fprintf fmt
      "This generalized constructor has return type %a\n\
       while it is expected to be an instance of %a."
      Printtyp.type_expr ty Printtyp.path res
  | Typecheck_inconsistence msg ->
    Format.fprintf fmt "%s" msg
  | Cyclic_abbreviation ->
    Format.fprintf fmt "This abbreviation is cyclic."
  | Inconsistent_constraint ty ->
    Format.fprintf fmt "The following constraint canot be enforced:\n%a."
      Printtyp.type_expr ty
  | Redefinition_mismatch
  | Definition_mismatch ->
    Format.fprintf fmt "This redefinition of type differs from the original."
  | Unbound_type_constructor p ->
    Format.fprintf fmt "Unbound type constructor %a." Printtyp.path p
  | Value_declaration_mismatch (ty, ty') ->
    Format.fprintf fmt "This value declaration has a different type in \
                        inference and after type checking."
  | Extension_arity_mismatch ->
    Format.fprintf fmt
      "Arity of the extension is different from the type declaration."
  | Unbound_constructor p ->
    Format.fprintf fmt
      "Constructor %a is not bound." Printtyp.path p

let print_error fmt (e, loc) =
  Format.fprintf fmt "%a\n%a\n"
    Location.print_loc loc
    print_error e
