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
open Typecheck_utils
open Typedtree
open Types
open Typecheck_ctype
open Typecheck_types
open Typecheck_result

let typemod_transl_modtype = ref (fun _ _ -> assert false)

let transl_modtype :
  context -> OCaml.Typedtree.module_type -> OCaml.Types.module_type =
  fun ctx mty -> !typemod_transl_modtype ctx mty

type error =
    Row_cannot_inherit of type_expr
  | Type_variable_different of type_expr * type_expr
  | Type_variable_expected of type_expr
  | Univar_expected of type_expr
  | Unbound_variable of string
  | Tyapp_invalid_constraints of type_expr
  | Row_inconsistent_conjunction
  | Row_tag_untyped of string
  | Incorrect_pack_type of module_type * module_type
  | Package_fields_duplicate

exception Typexpr_error of (error * Location.t)

let raise_error loc e =
  raise (Typexpr_error (e, loc))

let repr = Btype.repr

(* current workaround for first class modules *)
let current_vars = ref Variables.empty_variables

let set_current_vars v = current_vars := v
let reset_current_vars () = current_vars := Variables.empty_variables
let get_current_vars () = !current_vars
(* --- *)

let print_vars vars =
  SMap.iter (fun key _ -> Format.printf "%s; " key) vars.Variables.vars;
  Format.printf "\n%!"

type policy = Fixed | Extensible | Univars

let print_policy fmt = function
    Fixed -> Format.fprintf fmt "Fixed"
  | Extensible -> Format.fprintf fmt "Extensible"
  | Univars -> Format.fprintf fmt "Univars"

(* First call: status set to Trec_first, then always called with Trec_next *)
let rec map_rec ?(status=Trec_next) = function
  | [] -> []
  | (id, vd) :: rem ->
    let status =
      if Btype.is_row_name (Ident.name vd.typ_id) then Trec_not
      else status in
    (id, vd, status) :: map_rec rem


let rec swap_list = function
    x :: y :: l -> y :: x :: swap_list l
  | l -> l

let newvar_none ?(decl = false) loc ty variables =
  match (repr ty).desc with
    Tvar (Some name) ->
    Variables.{ variables
                    with vars = SMap.add name ty variables.Variables.vars }
  | Tvar None ->
    variables
  | _ ->
    variables (* Unification might change an 'a for a type *)
    (* raise_error loc @@ Type_variable_expected ty *)

let newvar' name ty variables =
  Variables.{ variables
              with vars = SMap.add name ty variables.Variables.vars }

(* let new_pre_univar ?name variables = *)
(*   let v = ty (\* new_global_var ?name () *\) in *)
(*   (\* v.desc <- Tunivar name; *\) *)
(*   v, Variables.{ variables with pre_univars = v :: variables.pre_univars } *)

let new_univar ?name loc ty variables =
  begin
    match (repr ty).desc with
      Tunivar _ -> ()
    | _ -> raise_error loc @@ Univar_expected ty
  end;
  match name with
    None -> variables
  | Some n ->
    Variables.{ variables with
                univars = SMap.add n ty variables.univars }

let find_var ?(generate=true) ?(policy=Extensible) loc name ty vars =
  print_debug (Format.asprintf "find_var: %s" name);
  let ty', vars =
    try SMap.find name vars.Variables.univars, vars
    with Not_found ->
      print_debug "Not in univars";
      try SMap.find name vars.Variables.vars, vars
      with Not_found ->
        if generate then
          let vars = if policy = Univars then new_univar ~name loc ty vars
            else newvar' name ty vars
          in
          ty, Variables.{ vars with vars = SMap.add name ty vars.vars }
        else raise_error loc (Unbound_variable name)
  in
  print_debug (
    Format.asprintf "enf of find_var: %a" Variables.print vars);
  let ty = repr ty and ty' = repr ty' in
  if ty != ty' then
    raise (Typexpr_error (Type_variable_different (ty, ty'), loc))
  else
    ty', vars

let force_poly ty =
  match ty.ctyp_desc with
    Ttyp_poly _ -> ty
  | _ -> { ty with ctyp_desc = Ttyp_poly ([], ty);
           ctyp_type = newty (Tpoly (ty.ctyp_type, [])); }

let generate_abstract_type env name id =
  let ty = newvar () in (* used to replace the generated abstract type *)
  print_debug (Format.asprintf "newvar: %a"
    Printtyp.raw_type_expr ty);
  begin_def ();
  let level = get_current_level () in
  let decl = {
    type_params = [];
    type_arity = 0;
    type_kind = Type_abstract;
    type_private = Asttypes.Public;
    type_manifest = None;
    type_variance = [];
    type_newtype_level = Some (level, level);
    type_loc = Location.none;
    type_attributes = [];
  } in
  Ident.set_current_time ty.level;
  (* let id = ref None in *)
  (* let module Iter = TypedtreeIter.MakeIterator(struct *)
  (*     include TypedtreeIter.DefaultIteratorArgument *)
  (*     let rec enter_core_type ct = *)
  (*       match ct.ctyp_type.desc with *)
  (*         Tconstr (p, _, _) when Path.head p |> Ident.name = name -> *)
  (*         id := ref Some (Path.head p) *)
  (*       | _ -> () *)
  (*   end) in *)
  let new_env = Env.add_type ~check:false id decl env in
  Typecheck_ctype.init_def (Ident.current_time());
  Typecheck_types.add_newtype (Path.Pident id) decl;
  ty, new_env, (* Iter.iter_expression, *) (fun env t ->
      let seen = Hashtbl.create 8 in
      let rec replace t =
        if Hashtbl.mem seen t.id then ()
        else begin
          Hashtbl.add seen t.id ();
          match t.desc with
          (* if the type corresponds to the newtype, we "replace" it by the
             generated type variable *)
          | Tconstr (Path.Pident id', _, _) ->
            print_debug
              (Format.asprintf "id: %a, id': %a" Ident.print id Ident.print id');
            if Ident.equal id' id then Btype.link_type t ty
            else Btype.iter_type_expr replace t
          | _ -> Btype.iter_type_expr replace t
        end
      in
      let ety = instance env t in
      replace ety;
      print_debug (Format.asprintf "ety: %a; ty: %a"
        Printtyp.raw_type_expr ety
        Printtyp.raw_type_expr ty);
      end_def ();
      generalize ety;
      ety)


let extract_sig env loc mty =
  match Env.scrape_alias env mty with
    Mty_signature sg -> sg
  | _ -> raise(Typemod.Error(loc, env, Typemod.Signature_expected))


let rec transl_ctype_aux ctx vars ?(decl=false) policy gen cty =
  (* Technically, we just need to assume that the "form" of the type is
     coherent against the infered type
     i.e.: transl_ctype_desc is unifiable with cty.ctyp_type

     Policy is set to Univars to type polymorphic method.

     Due to Explicit polymorphic types, we need delay the unification test,
     because vars are replaced by univars only when the entire type has been
     processed.
  *)
  print_debug
    (Format.asprintf "Typing %a"
       Typecheck_pretty.core_type cty);
  let vars =
    transl_type_desc
      ctx vars cty.ctyp_loc ~decl policy gen cty.ctyp_desc cty.ctyp_type in
  (* print_debug *)
  (*   (Format.asprintf "Result: %a" Printtyp.raw_type_expr ty); *)
  cty.ctyp_type, vars


(* decl: true if translating an argument of a type declaration. A Tvar None is
   then replace by a Tvar (Some "_") for consistency. It does not even need
   propagation. *)
and transl_type_desc ctx vars loc ?(decl=false) policy gen ctyd ty :
   Variables.variables =
  match ctyd, (Ctype.repr ty).desc with
    Ttyp_any, _ ->
    (* env |- _ :: t *)
    begin match policy with
        Fixed -> raise_error loc (Unbound_variable "_")
      | Extensible -> newvar_none ~decl loc ty vars
      | Univars -> new_univar loc ty vars
    end
  | Ttyp_var name, (Tvar (Some name') | Tunivar (Some name')) ->
    (* if s in used_vars && => env |- s : used_vars(s)
       else env |- s :: 'a *)
    assert (name = name');
    snd @@ find_var ~generate:gen ~policy loc name ty vars
  | Ttyp_var name, _ ->
    (* Happens when the variable:
       - is an alias
       - is a constraint
       - has been unified with another type. However, in that case one may
       wonder why the core_type type has been unified with the concrete type,
       while the type inference could have taken an instance.
    *)
    print_warning loc @@
    Format.asprintf "This core_type variable '%s has type %a.\n%!"
      name Printtyp.type_expr ty;
    snd @@ find_var ~generate:gen ~policy loc name ty vars
    (* raise (Typexpr_error (Type_variable_expected ty, loc)) *)
  | Ttyp_arrow (l, dom, cdom), Tarrow (l', tydom, tycdom, _) ->
           (* env |- dom :: ty1 && env |- cdom :: ty2
       ==> env |- ty :: l:dom -> cdom *)
    let dom, vars = transl_ctype_aux ctx vars policy gen dom in
    let cdom, vars = transl_ctype_aux ctx vars policy gen cdom in
    begin
      match Typecheck_typing.eq ctx dom tydom with
        Error e -> assert false;
      | Ok _ ->
        match Typecheck_typing.eq ctx cdom tycdom with
          Error e -> assert false
        | Ok _ -> vars
    end
  | Ttyp_tuple ctys, Ttuple tys ->
    (* \/ct in tys, env |- cti :: ti
       ==> env |- ty :: (t0 * .. * tn *)
    List.fold_left2 (fun vars cty ty ->
        let ty', vars = transl_ctype_aux ctx vars policy gen cty in
        match Typecheck_typing.eq ctx ty ty' with
            Ok _ -> vars
          | Error e -> assert false)
      vars ctys tys
  | Ttyp_constr (path, lid, args), Tconstr (typath, tys, _) ->
    (* env |- path :: ('a0, .., 'an) t
       && \/ct in args, env |- cti :: ti
       && |args| = n
       && args t coherent with constraints
       ==> env | constr :: (t0, .., tn) t
    *)
    print_debug (Format.asprintf "Not_found? %a\n%!" Printtyp.path path);
    let td = Env.find_type path ctx.env in
    assert (snd @@ PathEq.eq ctx.paths path typath);
    (* print_debug (Format.asprintf "found: %a\n%!" *)
    (*   (Printtyp.type_declaration @@ Path.head path) ty); *)
    assert (List.length args = td.type_arity);
    let vars = List.fold_left2 (fun vars cty ty ->
        let ty', vars = transl_ctype_aux ctx vars policy gen cty in
        match Typecheck_typing.eq ctx ty ty' with
            Ok _ -> vars
          | Error e -> assert false)
        vars args tys in
    begin match
        Typecheck_typing.instance_types ctx tys td.type_params TyMap.empty with
      | Ok _ -> vars
      | Error _ -> raise_error loc (Tyapp_invalid_constraints ty)
    end
  | Ttyp_poly (vs, cty), Tpoly (polyty, params) ->
    print_debug "Ttyp_poly";
    let new_vars = List.fold_left2 (fun vars name ty ->
        new_univar ~name loc ty vars) vars vs params in
    let polyty', vars = transl_ctype_aux ctx new_vars policy gen cty in
    print_debug (
      Format.asprintf "result of translating: %a\n===>\n%a"
        Typecheck_pretty.core_type cty
        Printtyp.raw_type_expr polyty'
    );
    begin
      match Typecheck_typing.eq ctx polyty polyty' with
        Error e -> assert false
      | Ok _ -> vars
    end
  | _, Tpoly (polyty, []) -> (* happens with objects, since they are always
                                    typed as polymorphic *)
    print_debug (
      Format.asprintf "Typing %a as tpoly"
        Typecheck_pretty.core_type_desc ctyd);
    transl_type_desc ctx vars loc policy gen ctyd polyty
  | Ttyp_alias (cty, name), _ ->
    let t_prev, vars = find_var ~generate:gen ~policy loc name ty vars in
    let ty', vars = transl_ctype_aux ctx vars policy gen cty in
    begin match Typecheck_typing.eq ctx ty ty' with
        Error e -> assert false
      | Ok _ -> match Typecheck_typing.eq ctx t_prev ty' with
          Error e -> assert false
        | Ok _ -> vars
    end
  | Ttyp_variant (fields, closed, present), Tvariant rd ->
    let { row_fields; row_more; row_closed; row_name } = Btype.row_repr rd in
    let known = Hashtbl.create 17 in
    let _row_name' = match fields with
        Tinherit { ctyp_type = { desc = Tconstr(p, tl, _)}} :: [] -> Some(p, tl)
      | _ -> None in

    (* Checks that inherited variants are compatible *)
    let add_typed_field l f =
      let h = Btype.hash_variant l in
      try
        let l', f' = Hashtbl.find known h in
        assert (l = l');
        let ty = create_field l f false true in
        let ty' = create_field l' f' false true in
        match Typecheck_typing.eq ctx ty ty' with
          Ok _ -> ()
        | Error _ -> failwith "Incompatibility"
      with Not_found ->
        Hashtbl.add known h (l, f)
    in

    (* Checks that the field corresponds to the type expected *)
    let check_field (vars : Variables.variables) = function
        Ttag (l, _, cst, ctys) ->
        let rf = try List.assoc l row_fields
          with Not_found -> failwith "Tag not in variant type" in

        (* If the tag is not in the "present tags", it must be of kind Reither
        *)
        let vars =
          match present with
            Some present when not @@ List.mem l present ->
            let vars =
              match rf with
                Reither (cst', tys, _, _) when cst = cst' ->
                List.fold_left2 (fun vars cty ty ->
                    let ty', vars =
                      transl_ctype_aux ctx vars policy gen cty in
                    match Typecheck_typing.eq ctx ty ty' with
                      Ok _ -> vars
                    | Error e -> assert false) vars ctys tys
              | _ -> failwith "Inconsistency"
            in
            vars
          | _ ->
            if List.length ctys > 1 || cst && ctys <> [] then
              raise_error loc Row_inconsistent_conjunction
            else match ctys, rf with
                [], Rpresent None -> vars
              | cty :: _, Rpresent (Some ty) ->
                let ty', vars = transl_ctype_aux ctx vars policy gen cty in
                begin
                  match Typecheck_typing.eq ctx ty ty' with
                    Error e -> assert false
                  | Ok _ -> vars
                end
              | _, _ -> failwith "Inconsistency"
        in
        add_typed_field l rf;
        vars
      | Tinherit cty ->
        let ty, vars = transl_ctype_aux ctx vars policy gen cty in
        let rec get_fields ty = match ty.desc with
            Tvariant row when Btype.static_row row ->
            (Btype.row_repr row).row_fields
          | Tconstr _ ->
            (try Typecheck_types.expand_abbrev ctx ty |> get_fields
             with Ctype.Cannot_expand -> assert false)
          | _ ->
            print_debug
              (Format.asprintf "Type: %a" Printtyp.raw_type_expr ty);
            raise_error loc (Row_cannot_inherit ty) in
        let fields = get_fields ty in
        List.iter (fun (l, f) ->
            let f = match present with
                Some present when not (List.mem l present) ->
                begin match f with
                    Rpresent(Some ty) ->
                    Reither(false, [ty], false, ref None)
                  | Rpresent None ->
                    Reither(true, [], false, ref None)
                  | _ ->
                    assert false
                end
              | _ -> f
            in
            add_typed_field l f) fields;
        vars
    in
    let vars = List.fold_left check_field vars fields in
    let fields = Hashtbl.fold (fun _ p l -> p :: l) known [] in
    begin
      match present with
        Some present ->
        List.iter (fun l -> if not @@ List.mem_assoc l fields then
                      raise_error loc (Row_tag_untyped l)) present
      | _ -> ()
    end;
    assert (row_closed = (closed = Asttypes.Closed));
    (* let row = *)
    (*   { row_fields = List.rev fields; row_more = Typecheck_ctype.newvar (); *)
    (*     row_bound = (); row_closed = (closed = Asttypes.Closed); *)
    (*     row_fixed = false; row_name; *)
    (*   } in *)
    let static = Btype.static_row rd in
    begin match static, (repr row_more).desc with
        true, Tnil | false, (Tvar _ | Tunivar _) -> ()
      | _, _ -> failwith "Inconsistency"
    end;
    if static then vars
    else if policy <> Univars then vars
    else new_univar loc row_more vars
  | Ttyp_package pack, Tpackage (p, lids, tys) ->
    (* *)
    type_package ctx vars policy gen pack (p, lids, tys) ty
  | Ttyp_object (fields, opened), Tobject (tyf, abbrev) ->
    let ty_fields, rv =
      Ctype.flatten_fields tyf in
    let ty_fields =
      List.filter (fun (_, k, _) -> k = Fpresent) ty_fields in
    print_debug (
      Format.asprintf "typing %a with type %a"
        Typecheck_pretty.core_type_desc ctyd
        Printtyp.raw_type_expr ty);
    let rec fold_fields f acc l1 l2 =
      match l1, l2 with
      | [], _ -> acc (* By unification, the type might have more fields
                                than the core_type *)
      | x :: l1, y :: l2 ->
        fold_fields f (f acc x y) l1 l2
      | _, _ -> invalid_arg "fold_fields"
    in
    let vars =
      fold_fields (fun vars (s, attrs, cty) (s', k, ty) ->
          print_debug (Format.asprintf "%s =?= %s" s s');
          assert (s = s');
          let ty', vars = transl_ctype_aux ctx vars policy gen cty in
          match Typecheck_typing.eq ctx ty ty' with
            Error e -> assert false
          | Ok _ -> vars)
        vars fields ty_fields in
    type_fields loc ctx vars policy opened [] rv fields
  | _ ->
    print_debug (
      Format.asprintf "Not managed yet::  typing %a with type %a"
        Typecheck_pretty.core_type_desc ctyd
        Printtyp.raw_type_expr ty);
    assert false
  (* | Ttyp_class of Path.t * Longident.t loc * core_type list *)

and type_fields loc ctx vars policy opened seen rv = function
    [] -> begin match opened, policy, (repr rv).desc with
        Open, Univars, Tunivar _ -> new_univar loc rv vars
      | Open, _, Tvar _ -> newvar_none loc rv vars
      | Open, _, _ | Closed, _, Tnil -> vars
      | Closed, _, _ -> failwith (
          Format.asprintf "Inconsistency: %a, %a, %a"
            Typecheck_pretty.closed_flag opened
            print_policy policy
            Printtyp.raw_type_expr rv)
    end
  | (s, _, ty) :: rem ->
    if List.mem s seen then failwith "Repetition"
    else
      type_fields loc ctx vars policy opened (s :: seen) rv rem

and type_package ctx vars policy gen pack (p, lids, tys) typack =
  let rec check_duplicates = function
      _, [] -> true
    | None, (lid, cty) :: rem -> check_duplicates (Some lid, rem)
    | Some lid, ((lid', _) :: rem as l) ->
      (not @@ List.exists (fun (lid'', _) -> lid.txt = lid''.txt) l)
      && check_duplicates (Some lid', rem)
  in
  let fields = List.combine lids tys in
  let rec gen_with_constr env lid ty cty =
    let p, td = Env.lookup_type lid.txt env in
    let d = {
      typ_id = Path.last p |> Ident.create;
      typ_name = Longident.last lid.txt |> Location.mknoloc;
      typ_params = [];
      typ_type = { td with type_manifest = Some ty };
      typ_cstrs = [];
      typ_kind = Ttype_abstract;
      typ_private = Public;
      typ_manifest = Some cty;
      typ_loc = Location.none;
      typ_attributes = [];
    } in
    p, lid, Twith_type d
  in
  let gen_tmty desc typ env loc attrs =
    { mty_desc = desc;
      mty_type = typ;
      mty_env = env;
      mty_loc = loc;
      mty_attributes = attrs } in
  (* Checks for possible duplicates *)
  if not @@ check_duplicates (None, pack.pack_fields) then
    raise_error pack.pack_txt.Location.loc Package_fields_duplicate;
  let mty = Env.find_modtype pack.pack_path ctx.env in
  let l, ctys = List.split pack.pack_fields in

  assert (Path.same pack.pack_path p);

  (* We type the constraints *)
  let vars = List.fold_left2
      (fun vars (l, cty) (l', ty) ->
         assert (l.txt = l');
         let ty', vars = transl_ctype_aux ctx vars policy gen cty in
         match Typecheck_typing.eq ctx ty ty' with
           Error e -> assert false
         | Ok _ -> vars) vars pack.pack_fields fields in
  set_current_vars vars;
  let path = pack.pack_path in
  let tmty_desc =
    (Tmty_ident (path, Location.mknoloc @@ longident_of_path path)) in
  let tmty =
    gen_tmty tmty_desc (Btype.default_mty mty.mtd_type) ctx.env mty.mtd_loc
      mty.mtd_attributes in

  (* We generate the new modtype with the constraints *)
  let mty' =
    try
      let sg =
        extract_sig ctx.env pack.pack_txt.loc (Btype.default_mty mty.mtd_type) in
      let env' = Env.add_signature sg ctx.env in
      let constraints = map3 (gen_with_constr env') l tys ctys in
      print_debug (
        Format.asprintf "pack, sig:\n%a" Printtyp.signature sg
      );
      Mty_signature
        (List.fold_left (fun sg (p, _, cstr) ->
             !Typecheck_types.apply_constraint ctx pack.pack_txt.loc sg p cstr)
            sg constraints)
    with Typemod.Error (_, _, Typemod.Signature_expected) ->
      (* The signature cannot be extracted if the modtype is a functor,
         however it is acceptable if there is no constraint *)
      if pack.pack_fields = [] then transl_modtype ctx tmty
      else
        raise (Typemod.Error
                 (pack.pack_txt.loc, ctx.env, Typemod.Signature_expected)) in
  begin
    match Typecheck_typing.eq_mty ctx mty' pack.pack_type with
      Ok _ -> ()
    | Error _ ->
      raise_error pack.pack_txt.Location.loc
        (Incorrect_pack_type (mty', pack.pack_type))
  end;
  reset_current_vars ();
  print_debug "package ok";
  vars

let transl_multiple_ctype ctx vars tys =
  List.fold_left (fun vars cty ->
      let _, vars =
        transl_ctype_aux
          ctx vars ~decl:true Extensible true cty in
      vars)
    vars tys

let transl_ctype ctx cty =
  let ty, _ =
    transl_ctype_aux ctx Variables.empty_variables Extensible true cty in
  (* let ty_exp = instance env cty.ctyp_type in *)
  (* print_debug (Format.asprintf "Generated: %a" Printtyp.raw_type_expr ty_exp); *)
  (* unify env ty ty_exp; *)
  ty

let print_error fmt = function
    Row_tag_untyped l ->
    Format.fprintf fmt "The tag %s has no declared type." l
  | Row_cannot_inherit ty ->
    Format.fprintf fmt "The variant type %a is not static, \n\
                        another variant type cannot inherit from it."
      Printtyp.type_expr ty
  | Row_inconsistent_conjunction ->
    Format.fprintf fmt "The following conjunction is invalid."
  | Tyapp_invalid_constraints _ ->
    Format.fprintf fmt "The type application is invalid due to the following
    contraint:\n???."
  | Unbound_variable s ->
    Format.fprintf fmt "Unbound type variable '%s." s
  | Incorrect_pack_type (mty, pack) ->
    Format.fprintf fmt "The module type\n %a \n\
                        \nis incompatible with the package type\n %a"
      Printtyp.modtype mty Printtyp.modtype pack
  | Package_fields_duplicate ->
    Format.fprintf fmt "This package type has duplicate types."
  | Type_variable_different (ty, ty') ->
    Format.fprintf fmt "Type variables are not equal:\n%a\n&&\n%a."
      Printtyp.raw_type_expr ty Printtyp.raw_type_expr ty'
  | Type_variable_expected ty ->
    Format.fprintf fmt "This core type is a type variable, whereas its infered \
                        type is %a."
      Printtyp.type_expr ty
  | Univar_expected _ ->  assert false

let print_error fmt (e, loc) =
  Format.fprintf fmt "%a\n%a\n"
    Location.print_loc loc
    print_error e

let _ =
  Typecheck_types.transl_core_type := transl_ctype
