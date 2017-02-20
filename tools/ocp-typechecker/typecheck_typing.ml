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

open Types
open Btype
open Typecheck_flags
open Typecheck_utils
open Typecheck_types
open Typecheck_result

(** Utility functions *)

type error =
    Incompatible_types of type_expr * type_expr
  | Label_mismatch of string * string
  | Incompatible_rows of row_desc * row_desc
  | Type_argument_mismatch
  | Tag_type_mismatch of string
  | Incoherent_instantiation of type_expr * type_expr * type_expr
  | Incoherent_polymorphic_instantiation of type_expr * type_expr
  | Incompatible_modtypes_decl of module_type option * module_type option
  | Incompatible_modtypes of module_type * module_type
  | Incompatible_type_decls of
      (Ident.t * type_declaration) * (Ident.t * type_declaration)
  (* | Incompatible_module_decls of *)
  (*     (Ident.t * module_type) * (Ident.t * module_type) *)
  | Unbound_item of signature_item
  | Unbound_type_constructor of Path.t
  | Illformed_type_application of type_expr
  | Unbound_universal_variable of type_expr
  | Illformed_package_type of type_expr
  | Variant_inherits_abstract of Path.t
  | Variant_inconsistent_inheritance of type_expr
  | Variant_inherited_not_static
  | Variant_tag_mismatch of string * row_field * row_field
  | Duplicate_variant_tag of string
  | Variant_tag_missing of string
  | Duplicate_field of string
  | Unordered_fields
  | Illformed_field of type_expr
  | Unbound_field of string
  | Incompatible_class_types of class_type * class_type
  | Types_error of Typecheck_types.error
  | Can_generalize of Types.type_expr
  | Cannot_generalize of type_expr * type_expr
  | Error_msg of string

exception Typing_error of (error * Location.t)

let raise_error loc t1 t2 =
  raise (Typing_error (Incompatible_types (t1, t2), loc))

let typemod_mty_with =
  ref ((fun _ _ _ -> assert false) :
         Env.t -> module_type -> Typedtree.with_constraint list -> signature)

let occur ctx ty ty' = false
  (* let seen = ref TySet.empty in *)
  (* let rec occur ty' = *)
  (*   begin try TySet.find ty seen with *)
  (*   let ty' = repr ty' in *)
  (*   if ty == ty' then true *)
  (*   else *)
  (*     match ty'.desc with *)
  (*     | Tarrow (_, t1, t2, _) -> *)
  (*       occur t1 || occur t2 *)
  (*     | Ttuple tys | Tconstr (_, tys, _) | Tpackage (_, _, tys) -> *)
  (*       List.exists occur tys *)
  (*     | Tpoly (ty', tys) -> *)
  (*       occur ty' || List.exists occur tys *)
  (*     | Tvariant rd -> *)
  (*       let rd = Btype.row_repr rd in *)
  (*       List.exists (fun (_, f) -> *)
  (*           match f with *)
  (*             Rpresent (Some ty') -> occur ty' *)
  (*           | Reither (_, tys, _, _) -> List.exists occur tys *)
  (*           | _ -> false) rd.row_fields *)
  (*     | Tobject (ty, _) -> *)
  (*       occur ty *)
  (*     | Tpackage (_, _, tys) -> List.exists occur tys *)
  (*     | _ -> false *)
  (* in *)
  (* occur ty' *)

let eq_newtype (ctx : context) p tv =
  match find_repr tv ctx with
    Some (Newtype p') ->
    if Path.same p p' then Ok ctx
    (* else if false (\* check ambivalences *\) then () *)
    else
      Error (Error_msg "eq_newtype: different repr")
  | None ->
    Ok { ctx with names = TyMap.add tv (Newtype p) ctx.names }
  | _ -> Error (Error_msg "eq_newtype")

let rec eq_row_fields ctx (l1, f1) (l2, f2) =
  if l1 <> l2 then
    Error (Variant_tag_mismatch (l1, f1, f2))
  else
    match f1, f2 with
      Rpresent None, Rpresent None -> Ok ctx
    | Rpresent (Some t1), Rpresent (Some t2) ->
      eq ctx t1 t2
    | Reither (c1, ts1, p1, rfopt1), Reither (c2, ts2, p2, rfopt2) ->
      if c1 = c2 then
        List.fold_left2 (fun prev t1 t2 ->
            prev >>= fun ctx -> eq ctx t1 t2) (Ok ctx) ts1 ts2
      else
        Error (Variant_tag_mismatch (l1, f1, f2))
    | Rabsent, Rabsent -> Ok ctx
    | _, _ ->
      Error (Variant_tag_mismatch (l1, f1, f2))

(* Assume rows are sorted? *)
and eq_row ctx r1 r2 =
  let r1 = Btype.row_repr r1 and r2 = Btype.row_repr r2 in
  if List.length r1.row_fields = List.length r2.row_fields then
    (let res = List.fold_left2 (fun prev r1 r2 ->
         prev >>= fun ctx -> eq_row_fields ctx r1 r2)
         (Ok ctx)
         r1.row_fields
         r2.row_fields in
    print_debug (Format.asprintf "eq r1=%a\n &&\n r2=%a"
      Typecheck_pretty.Types.row_desc r1 Typecheck_pretty.Types.row_desc r2);
    if r1.row_closed = r2.row_closed && r1.row_fixed = r2.row_fixed then
      res >>= fun ctx -> Ok ctx
    else Error (Incompatible_rows (r1, r2)))
  else Error (Incompatible_rows (r1, r2))

and eq_types ctx ts1 ts2 =
  try List.fold_left2 (fun prev t1 t2 ->
      prev >>= fun ctx -> eq ctx t1 t2) (Ok ctx) ts1 ts2
  with Invalid_argument str ->
    print_debug (Format.asprintf "EQ_types, error: %s" str);
    Error Type_argument_mismatch

and eq ctx ty1 ty2 : (context, error) result =
  if ty1 == ty2 then Ok ctx
  else
    let ty1' = Btype.repr ty1 in
    let ty2' = Btype.repr ty2 in
    print_debug
      (Format.asprintf "%a\n ??\n%a"
         Printtyp.raw_type_expr ty1'
         Printtyp.raw_type_expr ty2');
    match ty1'.desc, ty2'.desc with
      (* Tvar None, _ | _, Tvar None -> true *)
    | (Tvar _ | Tunivar _), (Tvar _ | Tunivar _)->
      print_debug "Tvar | Tunivar case";
      begin
        match find_repr' ~strict:true ctx ty1' ty2' with
          v, ctx' ->
          print_debug (Format.asprintf "Repr of %a & %a: %a\n%!"
            Printtyp.raw_type_expr ty1'
            Printtyp.raw_type_expr ty2'
            print_kind v);
          Ok ctx'
        | exception No_repr (v1, v2) ->
          print_debug (Format.asprintf "Repr of %a: %a & %a: %a\n%!"
            Printtyp.raw_type_expr ty1' print_kind v1
            Printtyp.raw_type_expr ty2' print_kind v2);
          Error (Incompatible_types (ty1', ty2'))
        | exception Not_found ->
          Error (Incompatible_types (ty1', ty2'))
      end
    (* | Tvar _, Tconstr (p, [], _) when is_newtype p -> *)
    (*   eq_newtype ctx p ty1' *)
    (* | Tconstr (p, [], _), Tvar _ when is_newtype p -> *)
    (*   eq_newtype ctx p ty2' *)
    | Tarrow (l1, t11, t12, _), Tarrow (l2, t21, t22, _) ->
      print_debug "Tarrow case";
      if l1 = l2 then
        eq ctx t11 t21 >>= fun ctx ->
        eq ctx t12 t22
      else Error (Label_mismatch (l1, l2))
    | Ttuple tl1, Ttuple tl2 ->
      print_debug "Ttuple case";
      List.fold_left2 (fun prev t1 t2 ->
      prev >>= fun ctx -> eq ctx t1 t2) (Ok ctx) tl1 tl2
    | Tpoly (ty, []), _ ->
      print_debug "Tpoly case";
      eq ctx ty ty2
    | _, Tpoly (ty, []) ->
      print_debug "Tpoly case";
      eq ctx ty1 ty
    | Tconstr (p, [], _), _ | _, Tconstr (p, [], _) when gadt_mode ctx p ->
      print_debug "Tconstr gadt_mode case";
      begin
        print_debug "Finding ambty";
        try
          let _, amb1 = find_equiv_ambi ctx ty1' []
          and _, amb2 = find_equiv_ambi ctx ty2' [] in
          if amb1.uniq == amb2.uniq then Ok ctx
          else Error (Incompatible_types (ty1', ty2'))
        with Not_found ->
          print_debug "Ambty: not_found...";
          Error (Incompatible_types (ty1', ty2'))
      end
    (* | Tconstr (p, [], _), _ when gadt_mode ctx p -> *)
    (*   print_debug *)
    (*     (Format.asprintf "%a\n ??\n%a" *)
    (*        Printtyp.raw_type_expr ty1' *)
    (*        Printtyp.raw_type_expr ty2'); *)
    (*   (Ok ctx) *)
    (* | _, Tconstr (p, [], _) when gadt_mode ctx p -> *)
    (*   eq ctx ty2' ty1' *)
    | Tconstr (p1, v1, _), Tconstr (p2, v2, _) ->
      (* apply_constrs eq p1 v1 p2 v2 *)
      print_debug "Tconstr case";
      let h, res = PathEq.eq ctx.paths p1 p2 in
      let ctx = { ctx with paths = h } in
      if res then eq_types ctx v1 v2
      else
        begin
          print_debug (Format.asprintf
            "Paths maybe need some normalization:\n- %a\n- %a\n%!"
            Typecheck_pretty.path p1
            Typecheck_pretty.path p2);
          try let ty1exp = expand_abbrev ctx ty1' in
            match eq ctx ty1exp ty2' with
              Ok ctx -> Ok ctx
            | Error _ -> raise Ctype.Cannot_expand
          with Ctype.Cannot_expand ->
            begin
              try let ty2exp = expand_abbrev ctx ty2' in
                match eq ctx ty1' ty2exp with
                  Ok ctx -> Ok ctx
                | Error _ -> raise Ctype.Cannot_expand
              with Ctype.Cannot_expand ->
                Error (Incompatible_types (ty1', ty2'))
            end
             | Ctype.Cannot_apply ->
               Error (Incompatible_types (ty1', ty2'))
        end
    (* | Tconstr (p, [], _), _ when gadt_mode ctx p -> *)
    (*   let ambs = *)
    (*     try TyMap.find ty1 ctx.ambivalents *)
    (*     with Not_found -> snd @@ find_equiv_ambi ctx p [] in *)
    (*   print_debug ( *)
    (*     Format.fprintf "GADT mode: %a" *)
    (*   TySet.fold (fun ty prev -> *)
    (*       match prev with *)
    (*         Ok _ -> prev *)
    (*       | Error _ -> eq ctx ty ty2) *)
    (*     ambs.value *)
    (*     (Error (Incompatible_types (ty1', ty2'))) *)
    | Tconstr (_, _, _), _ ->
      print_debug "Tconstr, any case";
      (try eq ctx (expand_abbrev ctx ty1') ty2'
       with Ctype.Cannot_expand | Ctype.Cannot_apply ->
         Error (Incompatible_types (ty1', ty2')))
    | _, Tconstr (_, _, _) ->
      print_debug "Any Tconstr case";
      (try eq ctx ty1' (expand_abbrev ctx ty2')
      with Ctype.Cannot_expand | Ctype.Cannot_apply ->
         Error (Incompatible_types (ty1', ty2')))
    | Tpoly (ty1, vars1), Tpoly (ty2, vars2) ->
      (*  Idea: generate a repr for each couple v1 * v2 from vars 1 and vars2.
          When typing a univar, if no repr yet, use the one generated and
          associate the univar with the repr. Two univars are equal if their
          repr is the same, i.e. if they are typed by the same binder. *)
      let ctx = allocate_univars ctx vars1 vars2 in
      eq ctx ty1 ty2
    | Tnil, Tnil -> Ok ctx
    | Tvariant r1, Tvariant r2 -> eq_row ctx r1 r2
    | Tpackage (p1, lids1, tys1), Tpackage (p2, lids2, tys2) ->
      eq_packages ctx (p1, lids1, tys1) (p2, lids2, tys2)
    | Tobject (f1, _), Tobject (f2, _) ->
      eq ctx f1 f2
    | Tfield (n1, k1, t1, rem1), Tfield (n2, k2, t2, rem2) ->
      print_debug
        (Format.asprintf "Tfields, %s && %s" n1 n2);
      let rec eq_kinds k1 k2 ctx = match k1, k2 with
          Fpresent, Fpresent | Fabsent, Fabsent -> Ok ctx
        | Fvar kopt, k | k, Fvar kopt ->
          (match !kopt with
             Some k' -> eq_kinds k k' ctx | None -> Ok ctx)
        | _, _ -> Error (Tag_type_mismatch n1) in
      eq ctx t1 t2 >>= fun ctx ->
      eq ctx rem1 rem2 >>= fun ctx ->
      eq_kinds k1 k2 ctx
    | d1, d2 ->
      print_debug (Format.asprintf "Not handled:\n %a =?= %a\n%!"
        Typecheck_pretty.Types.print_type_simple d1
        Typecheck_pretty.Types.print_type_simple d2);
      Error (Incompatible_types (ty1', ty2'))

and eq_packages ctx (p1, l1, t1) (p2, l2, t2) =
  let f1, f2 = List.combine l1 t1, List.combine l2 t2 in
  let f1 = List.sort (fun (l1, _) (l2, _) -> compare l1 l2) f1 in
  let f2 = List.sort (fun (l1, _) (l2, _) -> compare l1 l2) f2 in
  eq_mty ctx (Mty_ident p1) (Mty_ident p2) >>= fun ctx ->
  List.fold_left2 (fun prev (l1, t1) (l2, t2) ->
      if l1 = l2 then prev >>= fun ctx -> eq ctx t1 t2
      else Error (Error_msg "eq_packages")) (Ok ctx) f1 f2


and eq_opt ctx topt1 topt2 =
  match topt1, topt2 with
    None, None -> Ok ctx
  | Some t1, Some t2 -> eq ctx t1 t2
  | _, _ -> Error (Error_msg "eq_opt")

and eq_type_decl ctx ?(strict = false) id1 td1 id2 td2 =
  (* we assume that the first declaration can be transparent while the second is
     abstract in case strict = false *)
  print_debug (Format.asprintf "eq_type_decl: (%a) %a :> (%a) %a"
    Typecheck_pretty.ident id1
    (Printtyp.type_declaration id1) td1
    Typecheck_pretty.ident id2
    (Printtyp.type_declaration id2) td2);
  let ctx = allocate_vars ctx td1.type_params td2.type_params in
  let man = match td1.type_manifest, td2.type_manifest with
      None, None -> Ok ctx
    | Some t, None ->
      if not strict then
        Ok { ctx with
             env = Env.add_type ~check:false id1 td1 @@
               (* Workaround to add an "equation" between the abstract
                         type and the manifest of the concrete type *)
               Env.add_type ~check:false id2 td1 ctx.env }
      else Error (Incompatible_type_decls ((id1, td1), (id2, td2)))
    | Some t1, Some t2 ->
      eq ctx t1 t2 >>= fun ctx ->
      Ok { ctx with
           env = Env.add_type ~check:false id1 td1 @@
             Env.add_type ~check:false id2 td2 ctx.env }
    | _ -> Error (Incompatible_type_decls ((id1, td1), (id2, td2))) in
  man >>= fun ctx ->
  (match td1.type_private, td2.type_private with
      Asttypes.Public, Asttypes.Public | Asttypes.Private, _ -> Ok ctx
    | _ -> Error (Error_msg "Privacy mismatch")) >>= fun ctx ->
  try eq_kind (* new *)ctx td1.type_kind td2.type_kind
  with Not_found -> Error (Incompatible_type_decls ((id1, td1), (id2, td2)))


and eq_kind ctx k1 k2 =
  match k1, k2 with
    Type_abstract, _ -> Ok ctx
  | Type_open, Type_open -> Ok ctx
  | Type_record (ldl1, repr1), Type_record (ldl2, repr2) ->
    List.fold_left2 (fun prev ld1 ld2 ->
        if Ident.name ld1.ld_id = Ident.name ld2.ld_id &&
           ld1.ld_mutable = ld2.ld_mutable then
          prev >>= fun ctx -> eq ctx ld1.ld_type ld2.ld_type
        else Error (Error_msg "eq_kind"))
      (Ok ctx) ldl1 ldl2
  | Type_variant cdl1, Type_variant cdl2 ->
    List.fold_left2 (fun prev cd1 cd2 ->
        if Ident.name cd1.cd_id = Ident.name cd2.cd_id then
          prev >>= fun ctx ->
          List.fold_left2 (fun prev t1 t2 ->
              prev >>= fun ctx -> eq ctx t1 t2)
            (Ok ctx) cd1.cd_args cd2.cd_args >>= fun ctx ->
          eq_opt ctx cd1.cd_res cd2.cd_res
        else Error (Error_msg "eq_kind"))
      (Ok ctx) cdl1 cdl2
  | _, _ -> Error (Error_msg "eq_kind")

and eq_typext ctx (id1, te1) (id2, te2) =
  (* Needs to be treated as a special case, since extensions of a same type can
     happen at multiple location, and it won't simply suffice to simply check
     with the first found *)
  let ctx = allocate_vars ctx te1.ext_type_params te2.ext_type_params in
  if te1.ext_private = te2.ext_private then
    eq_types ctx te1.ext_args te2.ext_args >>= fun ctx ->
    eq_opt ctx te1.ext_ret_type te2.ext_ret_type
  else Error (Error_msg "eq_typext")

and eq_class_type ctx ctyp1 ctyp2 =
  match ctyp1, ctyp2 with
    Cty_signature sg1, Cty_signature sg2 ->
    eq_class_signature ctx sg1 sg2
  | Cty_arrow (l1, ty1, cty1), Cty_arrow (l2, ty2, cty2) ->
    if l1 = l2 then
      eq ctx ty1 ty2 >>= fun ctx ->
      eq_class_type ctx cty1 cty2
    else Error (Error_msg "eq_class_type")
  | Cty_constr (p1, tys1, cty1), Cty_constr (p2, tys2, cty2) ->
    let paths, eq_paths = PathEq.eq ctx.paths p1 p2 in
    if eq_paths then
      eq_types { ctx with paths } tys1 tys2
    else
      eq_class_type ctx cty1 cty2
  | Cty_constr (_, _, cty1), cty2 | cty1, Cty_constr (_, _, cty2) ->
    eq_class_type ctx cty1 cty2
  | _, _ ->
    print_debug
      (Format.asprintf "Incompatible class types: \n%a\nand\n%a."
         Printtyp.class_type ctyp1 Printtyp.class_type ctyp2);
    Error (Error_msg "eq_class_type")

and eq_class_signature ctx csg1 csg2 =
  let self_eq = eq ctx csg1.csig_self csg2.csig_self in
  let vars_eq = Vars.fold (fun n (mut, virt, ty) prev ->
      try
        let (mut', virt', ty') = Vars.find n csg2.csig_vars in
        if mut = mut' && virt = virt' then prev >>= fun ctx -> eq ctx ty ty'
        else Error (Error_msg "eq_class_signature")
      with Not_found -> Error (Error_msg "eq_class_signature"))
      csg1.csig_vars self_eq in
  let concr_eq = Concr.equal csg1.csig_concr csg2.csig_concr in
  let inher_eq = List.fold_left2 (fun prev (p, tys) (p', tys') ->
      let h, res = PathEq.eq ctx.paths p p' in
      if res then
        prev >>= fun ctx ->
        let ctx = { ctx with paths = h } in
        eq_types ctx tys tys'
      else Error (Error_msg "eq_class_signature"))
      (vars_eq) csg1.csig_inher csg2.csig_inher in
  if concr_eq then inher_eq
  else Error (Error_msg "eq_class_signature")

and eq_mty_opt strict ctx mty1 mty2 =
  match mty1, mty2 with
    None, None -> Ok ctx
  | None, Some _ -> if not strict then Ok ctx (* for abstract module types *)
    else Error (Error_msg "eq_mty_opt")
  | Some mty1, Some mty2 -> eq_mty ctx mty1 mty2
  | _, _ -> Error (Error_msg "eq_mty_opt")

and eq_mty ctx mty1 mty2 =
  print_debug (
    Format.asprintf "eq_mty:\n%a =?= %a"
      Printtyp.modtype mty1 Printtyp.modtype mty2);
  match mty1, mty2 with
    Mty_ident p1, Mty_ident p2 | Mty_alias p1, Mty_alias p2 ->
    let paths, are_eq = PathEq.eq ctx.paths p1 p2 in
    if are_eq then Ok { ctx with paths }
    else
      eq_mty ctx mty1 mty2 >>= fun ctx ->
      Ok { ctx with paths = PathEq.union paths p1 p2 }
  | Mty_ident p, mty | mty, Mty_ident p ->
    print_debug (Format.asprintf "Looking for %a"
      Typecheck_pretty.path p);
    begin
      match (Env.find_modtype p ctx.env).mtd_type with
        exception Not_found -> raise Not_found
      | Some mtd -> eq_mty ctx mty mtd
      | None -> Error (Error_msg "eq_mty")
      (* An abstract signature can only be equal to itself, and
                         then it corresponds to the previous case *)
    end
  | (Mty_alias _) as mtal, mty | mty, ((Mty_alias _) as mtal) ->
    Env.scrape_alias ctx.env mtal |> eq_mty ctx mty
  | Mty_signature sg1, Mty_signature sg2 -> eq_sg ctx sg1 sg2
  | Mty_functor (id1, arg_mty1, mty1), Mty_functor (id2, arg_mty2, mty2) ->
    let env' = Env.add_module ~arg:true id1 (Btype.default_mty arg_mty1) @@
      Env.add_module ~arg:true id2 (Btype.default_mty arg_mty2) ctx.env in
    let res_arg =
      eq_mty_opt true ctx arg_mty1 arg_mty2 in
    if Ident.name id1 = Ident.name id2 then
      res_arg >>= fun ctx ->
      let paths =
        PathEq.union ctx.paths (Path.Pident id1) (Path.Pident id2) in
      eq_mty { ctx with paths; env = env' } mty1 mty2
    else Error (Error_msg "eq_mty ident names")
  | _, _ -> Error (Error_msg "eq_mty ???")

and eq_sg ctx sg1 sg2 =
  (* TODO:
     Do we need both signatures to be in the correct order? If yes, this
     algorithm can only typecheck signatures that comes from the type inference
     engine. Otherwise:
     * for each item i2 of sig2:
       * pick the corresponding item i1 on sig1, remove it from sig1,
         if Not_found -> false
       * test i1 = i2, else -> false
     * repeat until sig1 || sig2 = []
     * if sig1 = sig2 -> true, else false
  *)
  let partition_one f extr l =
    let p1, p2 = List.partition f l in
    match p1 with
      v :: [] -> extr v, p2
    | _ -> raise Not_found
  in
  let rec find ctx sg2 value =
    match value with
      Sig_value (id, vd) ->
      let vd2, rem =
        partition_one (is_sig_value id) (extract_value Val) sg2 in
      eq ctx vd.val_type vd2.val_type >>= fun ctx ->
      Ok (rem, ctx)
    | Sig_type (id, td, _) ->
      let (id2, td2), rem =
        partition_one (is_sig_type id) (extract_value Type) sg2 in
      eq_type_decl ctx id td id2 td2 >>= fun ctx ->
      let ctx = { ctx with
                  paths = PathEq.union ctx.paths
                      (Path.Pident id) (Path.Pident id2) } in
      Ok (rem, ctx)
    (* td2 might be abstract while td transparent *)
    | Sig_typext (id, ec, _) ->
      let ec2, rem =
        partition_one (is_sig_typext id(* , ec.ext_type_path) *))
          (extract_value Ext) sg2 in
      eq_typext ctx (id, ec) ec2 >>= fun ctx ->
      Ok (rem, ctx)
    | Sig_module (id, md, _) ->
      let (id2, md2), rem =
        partition_one (is_sig_module id) (extract_value Mod) sg2 in
      eq_mty ctx md.md_type md2.md_type >>= fun ctx ->
      let ctx = { ctx with
                  paths = PathEq.union ctx.paths
                      (Path.Pident id) (Path.Pident id2) } in
      Ok (rem, ctx)
    | Sig_modtype (id, mtd) ->
      let (id2, mtd2), rem =
        partition_one (is_sig_modtype id) (extract_value Modtype) sg2 in
      eq_mty_opt false ctx mtd.mtd_type mtd2.mtd_type >>= fun ctx ->
      let ctx = { ctx with
                  paths = PathEq.union ctx.paths
                      (Path.Pident id) (Path.Pident id2) } in
      Ok (rem, ctx)
    | Sig_class (id, cd, _) ->
      let (_id2, _cd2), _rem =
        partition_one (is_sig_class id) (extract_value Class) sg2 in
      assert false
    | Sig_class_type (id, ctd, _) ->
      let (_id2, _ctd2), _rem =
        partition_one (is_sig_class_type id) (extract_value Classtype) sg2 in
      assert false
  in
  let rec pick ctx sg1 sg2 =
    match sg1 with
      sv :: rem -> begin
        match find ctx sg2 sv with
          Error e -> Error e
        | Ok (sg2', ctx') -> pick ctx' rem sg2'
        | exception Not_found -> Error (Unbound_item sv)
      end
    | [] -> Ok ctx
  in
  print_debug (Format.asprintf "Testing with %a <: %a"
    Printtyp.signature sg1 Printtyp.signature sg2);
  pick ctx sg1 sg2

exception Inconsistency

let find_ambivalence ctx ty =
  try Some (TyMap.find ty ctx.ambivalents), ctx
  with Not_found ->
  try let _, amb = find_equiv_ambi ctx ty [] in
    Some amb, { ctx with ambivalents = TyMap.add ty amb ctx.ambivalents}
  with Not_found ->
    print_debug "Not_found...";
    None, ctx

let union_ambivalences ctx (ty1, ambty1) (ty2, ambty2) =
  match ambty1, ambty2 with
    Some ambty1, Some ambty2 -> ambty1, ambty2, ctx
  | Some ambty1, None ->
    ambty1.value <- TySet.add ty2 ambty1.value;
    ambty1, ambty1,
    { ctx with ambivalents = TyMap.add ty2 ambty1 ctx.ambivalents}
  | None, Some ambty2 ->
    ambty2.value <- TySet.add ty1 ambty2.value;
    ambty2, ambty2,
    { ctx with ambivalents = TyMap.add ty1 ambty2 ctx.ambivalents}
  | None, None ->
    let ambty = create_tyset () in
    ambty.value <- TySet.add ty2 @@ TySet.add ty1 ambty.value;
    ambty, ambty, { ctx with ambivalents =
                               TyMap.add ty2 ambty @@
                               TyMap.add ty1 ambty ctx.ambivalents }

let equiv_ambivalences ctx ty1 ty2 =
  let ambty1, ctx = find_ambivalence ctx ty1 in
  let ambty2, ctx = find_ambivalence ctx ty2 in
  let check amb ty_a ty_c =
    print_debug "Checking for eqauivalent type in ambivalence";
    TySet.fold (fun ty ok ->
        print_debug
          (Format.asprintf "ty_a: %a; ty: %a"
             Printtyp.raw_type_expr ty_a Printtyp.raw_type_expr ty);
        if ty == ty_a || ok then ok else
          match eq ctx ty ty_c with
            Ok _ -> true
          | Error _ -> ok (* equivalent to "I don't know" *)) amb false
  in
  match ambty1, ambty2 with
    Some a1, Some a2 -> a1.value == a2.value
  | Some a, None -> check a.value ty1 ty2          
  | None, Some a -> check a.value ty2 ty1    
  | _, _ -> false

let inconsistent ctx ambty ty =
  TySet.exists (fun ty_a ->
      print_debug "Are ty and t2 not compatible?";
      if ty_a == ty then false else
        match Btype.repr ty_a with
          { desc = Tconstr (p, [], _) } when gadt_mode ctx p -> false
        | { desc = Tvar _ } -> false (* /!\ Hack *)
        | ty_a ->
          match eq ctx ty_a ty with Ok _ -> false | _ ->
            print_debug (
              Format.asprintf "%a and %a are not equal"
                Printtyp.raw_type_expr ty_a Printtyp.raw_type_expr ty);
            true) ambty.value

let add_equation ctx t1 t2 ret =
  let ambty1, ctx = find_ambivalence ctx t1 in
  let ambty2, ctx = find_ambivalence ctx t2 in
  let ambty1, ambty2, ctx = union_ambivalences ctx (t1, ambty1) (t2, ambty2) in
  print_debug
    (Format.asprintf "id1: %d, id2: %d" ambty1.uniq ambty2.uniq);
  let res = Ok (ret ctx t1 t2) in
  let print fmt a =
    TySet.iter (fun ty ->
        Format.fprintf fmt "%a; " Printtyp.type_expr ty) a.value in
  print_debug (
    Format.asprintf "ambty t1: [%a];\nambty t2: [%a]" 
      print ambty1 print ambty2);
  if TySet.mem t2 ambty1.value || ambty1.uniq == ambty2.uniq then res
  else if inconsistent ctx ambty1 t2
  then (print_debug "ambivalent_add: inconsistent";
        Error (Incompatible_types (t1, t2)))
  else begin
    let ambty_res = TySet.union ambty1.value ambty2.value in
    ambty1.value <- ambty_res;
    ambty2.value <- ambty_res;
    res
  end

let add_equations (subst, ctx) t1 t2 =
  print_debug "add_equations";
  let fold acc t1 t2 =
    print_debug "add_equations.fold";
    print_debug (
      Format.asprintf "%a and %a?"
        Printtyp.type_expr t1 Printtyp.type_expr t2);
    acc >>= fun (subst, ctx) ->
    let t1' = repr t1 and t2' = repr t2 in
    match t1', t2' with
      ({ desc = Tconstr (p, [], _) } as tn), ty
    | ty, ({desc = Tconstr (p, [], _) } as tn)
      when gadt_mode ctx p ->
      print_debug (
        Format.asprintf "Adding an equation between %a and %a"
          Printtyp.type_expr tn Printtyp.type_expr ty);
      add_equation ctx tn ty (fun ctx t1 t2 -> TyMap.add t2 t1 subst, ctx)
    | _, _ -> Ok (subst, ctx)
  in
  Iterate.fold_type2 (fun _ _ -> false) fold (Ok (subst, ctx)) t1 t2

(** Instantiation *)

let is_none = function None -> true | Some _ -> false
let get_opt = function Some v -> v | None -> assert false

(* let substs : type_expr TyTbl.t = TyTbl.create 17 *)

(* let reset_subst () = TyTbl.clear substs *)

let find_subst ty subst =
  try Some (TyMap.find ty subst)
  with Not_found -> None

let add_subst ty ty' subst =
  TyMap.add ty ty' subst

let i = ref 0

let rec instance_types ctx ts1 ts2 subst =
  let count = incr i; !i in
  print_debug (Format.asprintf "instance_types: %d" count);
  try
    let res = List.fold_left2 (fun s t1 t2 ->
      print_debug
        (Format.asprintf "instance_types (%d), typing : %a <: %a"
           count Printtyp.type_expr t1 Printtyp.type_expr t2);
      match s with
        Ok (subst, ctx) -> instance ctx t1 t2 subst
      | Error e -> s) (Ok (subst, ctx)) ts1 ts2 in
    print_debug (Format.asprintf "End of instance_types: %d" count);
    res
  with exn ->
    print_debug (Format.asprintf "Error, got: %s" @@ Printexc.to_string exn);
    Error Type_argument_mismatch

and instance_row ctx r1 r2 subst =
  let r1 = row_repr r1 and r2 = row_repr r2 in
  if r2.row_closed && not r1.row_closed then
    Error (Incompatible_rows (r1, r2))
  else instance_row_desc ctx r1 r2 r2.row_closed subst

and instance_row_desc ctx d1 d2 closed subst =
  List.fold_left (fun subst (l1, f1) ->
      match subst with
        Error _ -> subst
      | Ok (subst, ctx) ->
        try
          let rf = List.assoc l1 d2.row_fields in
          instance_row_field ctx l1 f1 rf subst
        with Not_found ->
          if closed then Error (Incompatible_rows (d1, d2))
          else Ok (subst, ctx))
    (Ok (subst, ctx)) d1.row_fields

and instance_row_field ctx l f1 f2 subst =
  match f1, f2 with
    Rpresent topt1, Rpresent topt2 ->
    instance_opt ctx l topt1 topt2 subst
  | Reither (_, ts1, _, _), Reither (_, ts2, _, _) ->
    instance_types ctx ts1 ts2 subst
  | Rpresent t1, Reither (_, ts2, _, _) ->
    begin
      (* Variant types can be complex with cunjunctions, not typed yet *)
      match t1, ts2 with
        None, [] -> Ok (subst, ctx)
      | Some t1, _ :: _ ->
        let ts1 = List.map (fun _ -> t1) ts2 in
        instance_types ctx ts1 ts2 subst
      | _, _ -> Error (Tag_type_mismatch l)
    end
  | Rabsent, Rabsent -> Ok (subst, ctx)
  | _, _ -> Error (Tag_type_mismatch l)

and instance_opt ctx l topt1 topt2 subst =
  match topt1, topt2 with
    None, None -> Ok (subst, ctx)
  | Some t1, Some t2 -> instance ctx t1 t2 subst
  | _, _ -> Error (Tag_type_mismatch l)

and instance_class_decl _ _ _ _ = assert false

and instance ctx t1 t2 subst : ('a, error) result =
  print_debug (Format.asprintf "instance: gadt_mode: %b. \n\
                                    Testing with %a <: %a"
    ctx.gadt Printtyp.raw_type_expr t1 Printtyp.raw_type_expr t2);
  let t1' = repr t1 and t2' = repr t2 in
  let err_incomp = Error (Incompatible_types (t1, t2)) in
  match t1'.desc, t2'.desc with
  | _, Tvar _ ->
    begin
      print_debug
        (Format.asprintf "instance_tvar, %a on the right."
           Printtyp.type_expr t2');
      match find_subst t2' subst with
        Some t ->
        print_debug
          (Format.asprintf "subst_found: %a" Printtyp.raw_type_expr t);
        begin
          match eq ctx t t1' with
            Ok ctx' -> Ok (subst, ctx')
          | Error _ ->
            print_debug "Incoherent instantiation";
            Error (Incoherent_instantiation (t2, t, t1))
        end
      | None -> print_debug "no_subst"; Ok (add_subst t2' t1' subst, ctx)
    end
  | Tconstr (p, [], _), ty
  | ty, Tconstr (p, [], _)
    when gadt_mode ctx p ->
    if equiv_ambivalences ctx t1' t2' then Ok (subst, ctx) else err_incomp
  | Tconstr (p1, v1, _), Tconstr (p2, v2, _) ->
    begin
      let h, res = PathEq.eq ctx.paths p1 p2 in
      let ctx = { ctx with paths = h } in
      if res then instance_types ctx v1 v2 subst
      else
        try let t1exp = expand_abbrev ctx t1' in
          match instance ctx t1exp t2' subst with
            Error _ -> raise Ctype.Cannot_expand
          | Ok (subst, ctx) as s-> s (* instance_types ctx v1 v2 subst *)
        with Ctype.Cannot_expand ->
          begin
            try let t2exp = expand_abbrev ctx t2' in
              match instance ctx t1' t2exp subst with
                Error _ -> raise Ctype.Cannot_expand
              | Ok (subst, ctx) as s -> s (* instance_types ctx v1 v2 subst *)
            with Ctype.Cannot_expand -> err_incomp
          end
           | Ctype.Cannot_apply -> print_debug "Cannot_apply"; err_incomp
    end
  | Tconstr (p, v, _), _ ->
    begin
      try
        let t' = expand_abbrev ctx t1' in
        instance ctx t' t2' subst
      with Ctype.Cannot_expand | Ctype.Cannot_apply -> err_incomp
    end
  | _, Tconstr (p, v, _) ->
    begin
      try
        let t' = expand_abbrev ctx t2' in
        instance ctx t1' t' subst
      with Ctype.Cannot_expand | Ctype.Cannot_apply -> err_incomp
    end
  | Tarrow (l1, t11, t12, _), Tarrow (l2, t21, t22, _) ->
    begin
      match instance ctx t11 t21 subst with
        Ok (subst, ctx) when l1 = l2 -> instance ctx t12 t22 subst
      | _ -> err_incomp
    end
  | Ttuple ts1, Ttuple ts2 ->
    instance_types ctx ts1 ts2 subst
  | Tpoly (ty1, vars1), Tpoly (ty2, vars2) ->
    let ctx = allocate_univars ctx vars1 vars2 in
    instance ctx ty1 ty2 subst
  | Tpoly (poly, vars), _ ->
    let vars', poly' =
      Ctype.instance_poly ~keep_names:true true vars poly in
    instance ctx poly' t2' subst
  | _, Tpoly (poly, vars) ->
    let vars', poly' =
      Ctype.instance_poly ~keep_names:true true vars poly in
    instance ctx t1' poly' subst
  | Tnil, Tnil -> Ok (subst, ctx)
  | Tvariant r1, Tvariant r2 ->
    instance_row ctx r1 r2 subst
  | Tunivar _, Tunivar _ ->
    (try
       if equiv_univars ctx t1' t2' then Ok (subst, ctx) else
         Error (Incoherent_polymorphic_instantiation (t1', t2'))
     with Not_found -> Ok (subst, allocate_univars ctx [t1'] [t2']))
  | Tpackage (p1, l1, t1), Tpackage (p2, l2, t2) ->
    instance_package ctx (p1, l1, t2) (p2, l2, t2) subst

  | Tobject (t1, _), Tobject (t2, _) ->
    instance_object ctx t1 t2 subst
  (* | Tfield (f1, k1, t1, rem1), Tfield (f2, k2, t2, rem2) -> *)
  (*   assert false *)
  |  d1, d2 ->
    print_debug "instance: incompatible types";
      Error (Incompatible_types (t1', t2'))

(* !!!!! TODO: The instance package is incorrect. We need to generate the
   correct signature to have a correct instance *)
and instance_package ctx (p1, l1, t1) (p2, l2, t2) subst =
  let mty1 =
    Typecheck_types.create_package_mty ctx.env (Mty_ident p1) l1 t1 in
  let mty2 =
    Typecheck_types.create_package_mty ctx.env (Mty_ident p2) l2 t2 in
  coercible_mty ctx mty1 mty2 subst

and instance_object ctx t1 t2 susbt =
  print_debug
    (Format.asprintf "Instance_object: %a :> %a"
       Printtyp.raw_type_expr t1 Printtyp.raw_type_expr t2);
  let rec step ctx (k : type_expr -> type_expr) t1 t2 subst =
    let t1 = repr t1 and t2 = repr t2 in
    match t1.desc, t2.desc with
      Tfield (f, _, ty, rem), Tfield (f', _, ty', rem') when f = f' ->
      print_debug "case 1";
      instance ctx ty ty' subst >>= fun (subst, ctx) ->
      step ctx (fun ty -> ty) (k rem) rem' subst
    | Tfield (f, ki, ty, rem), Tfield (f', _, _, _) ->
      begin
        match step ctx
                (fun rem -> k (Ctype.newty @@ Tfield (f, ki, ty, rem)))
                rem t2 subst with
          (Ok _) as ok -> ok
        | Error _ -> Error (Unbound_field f')
      end
    | _, _ -> instance ctx t1 t2 subst
  in
  step ctx (fun rem -> rem) t1 t2 susbt

and coercible_mty_opt ~strict ctx mty1 mty2 subst =
  match mty1, mty2 with
    None, None -> Ok (subst, ctx)
  | Some _, None -> if not strict then Ok (subst, ctx) else
      Error (Incompatible_modtypes_decl (mty1, mty2))
  (* for abstract module types *)
  | Some mty1, Some mty2 -> coercible_mty ctx mty1 mty2 subst
  | _, _ -> Error (Incompatible_modtypes_decl (mty1, mty2))

and coercible_mty ctx mty1 mty2 subst =
  print_debug
    (Format.asprintf "coercible_mty: %a :> %a"
       Printtyp.modtype mty1 Printtyp.modtype mty2);
  let err_incomp = Error (Incompatible_modtypes (mty1, mty2)) in
  match mty1, mty2 with
    (Mty_ident p1, Mty_ident p2 | Mty_alias p1, Mty_alias p2)
    when snd @@ PathEq.eq ctx.paths p1 p2 ->
      Ok (subst, ctx)
  | Mty_ident p1, Mty_ident p2 | Mty_alias p1, Mty_alias p2 ->
    (* debug_expand_modtype_path ctx p1; *)
    (* debug_expand_modtype_path ctx p2; *)
    (try ignore @@ Env.find_modtype p1 ctx.env
    with Not_found -> print_debug "Not_found p1");
    (try ignore @@ Env.find_modtype p2 ctx.env
    with Not_found -> print_debug "Not_found p2");
    let mty1' = try_expand_mty_path ctx mty1 in
    print_debug
      (Format.asprintf "before_scrape:\n%a\n\
                        after scrape:\n%a"
         Printtyp.modtype mty1 Printtyp.modtype mty1');
    let mty2' = try_expand_mty_path ctx mty2 in
    print_debug
      (Format.asprintf "before_scrape:\n%a\n\
                        after scrape:\n%a"
         Printtyp.modtype mty2 Printtyp.modtype mty2');
    if mty1' == mty1 && mty2' == mty2 then err_incomp
    else begin
      match coercible_mty ctx mty1' mty2' subst with
        Error _ as e -> e
      | Ok (subst, ctx) ->
        Ok (subst, { ctx with paths = PathEq.union ctx.paths p1 p2 })
    end
  | (Mty_alias _) as mtal, mty ->
    let mty' = Env.scrape_alias ctx.env mtal in
    coercible_mty ctx mty' mty subst
  | mty, ((Mty_alias _) as mtal) ->
    let mty' = Env.scrape_alias ctx.env mtal in
    coercible_mty ctx mty mty' subst
  | Mty_ident p, _ ->
    print_debug "Ident, ??:";
    (* debug_expand_modtype_path ctx p; *)
    let mty1' = Mtype.scrape ctx.env mty1 in
    if mty1' == mty1 then err_incomp
    else coercible_mty ctx mty1' mty2 subst
  | mty, Mty_ident p ->
    print_debug "??, Ident:";
    print_debug (Format.asprintf "Looking for %a"
      Typecheck_pretty.path p);
    (* debug_expand_modtype_path ctx p; *)
    let mty2' = Mtype.scrape ctx.env mty2 in
    if mty2' == mty2 then err_incomp
    else coercible_mty ctx mty1 mty2' subst
  | Mty_signature sg1, Mty_signature sg2 -> coercible ctx sg1 sg2 subst
  | Mty_functor (id1, arg_mty1, mty1), Mty_functor (id2, arg_mty2, mty2) ->
    print_debug "Functor";
    let env' = Env.add_module ~arg:true id1 (Btype.default_mty arg_mty2) @@
      Env.add_module ~arg:true id2 (Btype.default_mty arg_mty2) ctx.env in
    let ctx' = {
      ctx with
      env = env';
      paths = PathEq.union ctx.paths (Path.Pident id1) (Path.Pident id2)} in
    (* !! TODO: Generate a substitution for id1 and id2 *)
    (* if Ident.name id1 = Ident.name id2 then *)
      coercible_mty_opt ~strict:true ctx arg_mty1 arg_mty2 subst >>=
      (* subtyping *)
      (fun (subst, _) ->
         print_debug "Typing arg";
         coercible_mty ctx' mty1 mty2 subst)
    (* else None *)
  | _, _ ->
    print_debug "Unknown case";
    err_incomp

and coercible ctx sg coerce subst =
  (* TODO:
     Do we need both signatures to be in the correct order? If yes, this
     algorithm can only typecheck signatures that comes from the type inference
     engine. Otherwise:
     * for each item i2 of sig2:
       * pick the corresponding item i1 on sig1, remove it from sig1,
         if Not_found -> false
       * test i1 = i2, else -> false
     * repeat until sig1 || sig2 = []
     * if sig1 = sig2 -> true, else false
  *)
  let rec find ctx coerce value subst =
    let apply : type a. (signature_item -> bool) ->
      (context -> a -> a -> substs -> (substs * context, error) result)
      -> a -> a Typecheck_types.sig_kind ->
      (substs * values * context, error) result =
      fun is_sig_v inst v2 kind ->
        match partition_one is_sig_v coerce kind with
          Some (v, rem), kind' ->
          try_instance inst v2 v ctx subst rem kind'
        | None, kind' ->
          print_debug "partition failed"; gen_res subst coerce v2 kind' ctx
    in
    match value with
      Sig_value (id, vd) ->
      apply (is_sig_value id)
        (fun ctx vd1 vd2 substs ->
           instance ctx vd2.val_type vd1.val_type subst)
        vd Val
    | Sig_type (id, td, _) ->
      print_debug (Format.asprintf "in_sig_type %a:"
        Typecheck_pretty.ident id);
      apply (is_sig_type id)
        (fun ctx (id1, td1) (id2, td2) substs ->
          match eq_type_decl ctx id1 td1 id2 td2 with
              Ok ctx ->
              print_debug "eq";
              let ctx = { ctx with
                          paths =
                            PathEq.union ctx.paths
                              (Path.Pident id1) (Path.Pident id2); } in
              Ok (subst, ctx)
            | Error _ -> print_debug "non eq";
              Error (Incompatible_type_decls ((id1, td1), (id2, td2))))
        (id, td) Type
    (* td2 might be abstract while td transparent *)
    | Sig_typext (id, ec, _) ->
      apply (is_sig_typext (id(* , ec.ext_type_path *)))
        (fun ctx (id1, ec1) (id2, ec2) substs ->
           match eq_typext ctx (id1, ec1) (id2, ec2) with
             Ok ctx -> Ok (subst, ctx)
           | Error _ -> Error (Error_msg "Type extensions not compatible."))
        (id, ec) Ext
    | Sig_module (id, md, _) ->
      apply (is_sig_module id)
        (fun ctx (id1, md1) (id2, md2) substs ->
           match coercible_mty ctx md1.md_type md2.md_type subst with
             Ok (subst, ctx) ->
             let env = Env.add_module_declaration id1 md1 @@
               Env.add_module_declaration id2 md2 ctx.env in
             let ctx = {
               ctx with
               paths =
                 PathEq.union ctx.paths (Path.Pident id1) (Path.Pident id2);
               env; } in
              Ok (subst, ctx)
           | Error _ as e -> e)
        (id, md) Mod
    | Sig_modtype (id, mtd) ->
      apply (is_sig_modtype id)
        (fun ctx (id1, mtd1) (id2, mtd2) substs ->
           match coercible_mty_opt ~strict:false
                   ctx mtd1.mtd_type mtd2.mtd_type subst
           with
             Ok (subst, ctx) ->
             let env = Env.add_modtype id1 mtd1 @@
               Env.add_modtype id2 mtd2 ctx.env in
             let ctx = {
               ctx with
               paths =
                 PathEq.union ctx.paths (Path.Pident id1) (Path.Pident id2);
               env; } in
             Ok (subst, ctx)
           | Error _ as e -> e)
        (id, mtd) Modtype
    | Sig_class (id, cd, _) ->
      apply (is_sig_class id)
        (fun ctx (id1, cl1) (id2, cl2) substs ->
           assert false)
        (id, cd) Class
    | Sig_class_type (id, ctd, _) ->
      apply (is_sig_class_type id)
        (fun ctx (id1, ct1) (id2, ct2) substs ->
           assert false)
        (id, ctd) Classtype
  in
  let rec pick ctx sg coerce subst =
    match sg, coerce with
    | _, [] ->
      print_debug "Finished";
      Ok (subst, ctx)
    | sv :: rem, coerce -> begin
        print_debug "coercible-pick: Testing with sig_item";
        match find ctx coerce sv subst with
          Error _ as e -> e
        | Ok (subst, coerce', ctx) -> pick ctx rem coerce' subst
        | exception Not_found ->
          Error (Error_msg "Not_found")
      end
    | [], item :: _ -> print_debug "coercion non empty";
      Error (Unbound_item item)
  in
  print_debug (Format.asprintf "coercible: Testing with %a :> %a"
    Printtyp.signature sg Printtyp.signature coerce);
  pick ctx sg coerce subst

and coercible_class ctx cty1 cty2 subst = assert false

let instance' ?(gadt=false) env t1 t2 =
  print_debug (Format.asprintf "instance': Testing for %a <: %a"
    Printtyp.raw_type_expr t1 Printtyp.raw_type_expr t2);
  instance (create_context env) t1 t2 TyMap.empty

let substitute t subst =
  match find_subst t subst with
    None -> t
  | Some t' -> t'

let rec apply_types tys subst =
  let tys' = List.map (fun ty ->
      apply_subst ty subst) tys in
  if List.for_all2 (==) tys tys' then tys else tys'

and apply_opt tyopt subst =
  match tyopt with
    None -> tyopt
  | Some t ->
    let t' = apply_subst t subst in
    if t == t' then tyopt else Some t'

and apply_row r subst =
  let more' = apply_subst r.row_more subst in
  let rf' = List.map (fun rf ->
      apply_row_fields rf subst) r.row_fields in
  if List.for_all2 (==) r.row_fields rf' && r.row_more == more' then r
  else { r with row_fields = rf'; row_more = more' }

and apply_row_fields ((l, f) as rf) subst =
  match f with
    Rpresent (Some t) ->
    let t' = apply_subst t subst in
    if t == t' then rf
    else l, Rpresent (Some t')
  | Reither (cst, tys, p, r) ->
    let tys' = apply_types tys subst in
    if tys == tys' then rf else l, Reither (cst, tys', p, r)
  | _ -> rf

and apply_kind k subst =
  match k with
    Type_abstract | Type_open -> k
  | Type_variant cstrs ->
    let cstrs' = List.map (fun cstr ->
        let args' = apply_types cstr.cd_args subst in
        let res' = apply_opt cstr.cd_res subst in
        if List.for_all2 (==) args' cstr.cd_args &&
           res' == cstr.cd_res then cstr
        else { cstr with cd_args = args'; cd_res = res'}) cstrs in
    if List.for_all2 (==) cstrs cstrs' then k else Type_variant cstrs'
  | Type_record (ls, repr) ->
    let ls' = List.map (fun l ->
        let ty' = apply_subst l.ld_type subst in
        if l.ld_type == ty' then l else { l with ld_type = ty' }) ls in
    if List.for_all2 (==) ls ls' then k else Type_record (ls', repr)

(* Tries to keep sharing as much as possible *)
and apply_subst t subst =
  let t = repr t in
  let res = match t.desc with
      Tvar _ -> let t' = substitute t subst in
      print_debug (Format.asprintf "subst for %a: %a"
                             Printtyp.type_expr t
                             Printtyp.type_expr t');
      t'
    | Tarrow (l, t1, t2, c) ->
      print_debug ("In arrow type");
    let t1' = apply_subst t1 subst in
    let t2' = apply_subst t2 subst in
    if t1 == t1' && t2 == t2' then t
    else Ctype.newty (Tarrow (l, t1', t2', c))
  | Ttuple tys ->
    let tys' = apply_types tys subst in
    if tys != tys' then Ctype.newty (Ttuple tys')
    else t
  | Tconstr (p, tys, a) ->
    let tys' = apply_types tys subst in
    if tys != tys' then Ctype.newconstr p tys'
    else t
  | Tvariant r ->
    let r' = apply_row r subst in
    if r == r' then t
    else Ctype.newty (Tvariant r')
  | Tunivar _ -> t
  | Tpoly (p, v) ->
    let p' = apply_subst p subst in
    if p == p' then t else Ctype.newty (Tpoly (p', v))
  | Tpackage (p, lids, tys) ->
    let tys' = apply_types tys subst in
    if tys != tys' then Ctype.newty (Tpackage (p, lids, tys'))
    else t
  | Tnil -> t
  | Tobject (fields, name) ->
    let fields' = apply_subst fields subst in
    let name' = match !name with
        None -> !name
      | Some (p, tys) ->
        let tys' = apply_types tys subst in
        if tys == tys' then !name
        else Some (p, tys') in
    if fields == fields' && !name == name' then t
    else Ctype.newty (Tobject (fields', ref name'))
  | Tfield (n, k, ty, rem) ->
    let ty' = apply_subst ty subst in
    let rem' = apply_subst rem subst in
    if ty == ty' && rem == rem' then t
    else Ctype.newty (Tfield (n, k, ty', rem'))
  | _ ->
    print_debug (Format.asprintf "apply_subst: not handled -> %a"
      Printtyp.raw_type_expr t);
    assert false
  in
  print_debug (
    Format.asprintf "after_apply: %a" Printtyp.raw_type_expr res);
  (* if t == res then t else  *)res
  (* | Tobject of type_expr * (Path.t * type_expr list) option ref *)
  (* | Tfield of string * field_kind * type_expr * type_expr *)

and apply_class_type cty subst =
  let res = match cty with
      Cty_constr (p, tys, ctyc) ->
      let tys' = apply_types tys subst in
      let ctyc' = apply_class_type ctyc subst in
      if tys == tys' && ctyc == ctyc' then cty
      else Cty_constr (p, tys', ctyc')
    | Cty_arrow (l, ty, cty_res) ->
      let ty' = apply_subst ty subst in
      let cty_res' = apply_class_type cty_res subst in
      if ty == ty' && cty_res == cty_res' then cty
      else Cty_arrow (l, ty', cty_res')
    | Cty_signature csig ->
      let csig' = apply_class_sig csig subst in
      if csig == csig' then cty else Cty_signature csig'
  in
  if res == cty then cty else res

and apply_class_sig csig subst =
  let self' = apply_subst csig.csig_self subst in
  let vars' =
    let changed = ref false in
    let vars' =
      Vars.map (fun ((mut, virt, ty) as res) ->
          let ty' = apply_subst ty subst in
          if ty == ty' then res else ((changed := true); (mut, virt, ty')))
        csig.csig_vars
    in
    if !changed then vars' else csig.csig_vars
  in
  let inher' =
    let changed = ref false in
    let inher' =
      List.map (fun ((p, tys) as res) ->
          let tys' = apply_types tys subst in
          if tys == tys' then res else (changed := true; (p, tys')))
        csig.csig_inher
    in
    if !changed then inher' else csig.csig_inher
  in
  if csig.csig_self == self'
  && csig.csig_vars == vars'
  && csig.csig_inher == inher' then
    csig
  else
    { csig with csig_self = self'; csig_vars = vars'; csig_inher = inher' }

let less_gen loc env ty1 ty2 =
  print_debug (Format.asprintf "less_gen: %a || %a"
    Printtyp.type_expr ty1
    Printtyp.type_expr ty2);
  match instance' env ty1 ty2 with
    Error _ ->
    begin match instance' env ty2 ty1 with
        Error e -> raise (Typing_error (e, loc))
      | Ok _ -> ty2
    end
  | Ok _ -> ty1

let rec wellformed_type ~poly ctx ty visited =
  print_debug
    (Format.asprintf "wellformed? %a"
       Printtyp.type_expr ty);
  let ty = repr ty in
  match TyMap.mem ty visited with
    true -> Ok visited
  | false ->
    let visited' = TyMap.add ty () visited in
    match ty.desc with
      Tvar _ -> Ok visited'
    | Tarrow (l, t1, t2, _) ->
      Ok visited'
      >>= wellformed_type ~poly ctx t1
      >>= wellformed_type ~poly ctx t2
    | Ttuple tys ->
      wellformed_type_list ~poly ctx tys visited'
    | Tconstr (p, args, _) ->
      begin
        try
          let ty_args = (Env.find_type p ctx.env).type_params in
          let visited'' = wellformed_type_list ~poly ctx args visited' in
          instance_types ctx args ty_args TyMap.empty >>=
          fun _ -> visited''
        with Not_found -> Error (Unbound_type_constructor p)
           | Invalid_argument _ -> Error (Illformed_type_application ty)
      end
    | Tpoly (ty, vars) ->
      let visited'' =
        List.fold_left (fun v t -> v >>= wellformed_type ~poly ctx t)
          (Ok visited') vars in
      print_debug "Quantifiers wellformed";
      visited'' >>= wellformed_type ~poly:true ctx ty
    | Tunivar v ->
      (* in case of polymorphic type, the univar has already been visited when
         veryfing quatifiers. This case would never be reached. *)
      print_debug
        (Format.asprintf "Wellformed univar (in_poly:%b)?: \n%a %a\n%!"
           poly Typecheck_pretty.Types.type_expr ty Printtyp.raw_type_expr ty);
      if poly then Error (Unbound_universal_variable ty) else Ok visited'
    (* | Tobject of type_expr * (Path.t * type_expr list) option ref *)
    (* | Tfield of string * field_kind * type_expr * type_expr *)
    | Tvariant row ->
      wellformed_row ~poly ctx row visited
    | Tpackage (p, ls, tys) ->
      begin
        try
          let mty = Env.find_modtype p ctx.env in
          wellformed_package
            ~poly ctx (Btype.default_mty mty.mtd_type) (p, ls, tys) visited'
        with _ -> Error (Illformed_package_type ty)
      end
    | Tobject (tyfields, abbrev) ->
      let abbrev = match !abbrev with
          None -> Ok visited'
        | Some (p, tys) ->
          let ty_class = Ctype.newconstr p tys in
          match eq ctx ty ty_class with
            Ok ctx ->
            wellformed_type ~poly ctx ty_class visited'
          | Error _ -> Error (Incompatible_types (ty, ty_class)) in
      abbrev >>= wellformed_object ~poly ctx tyfields []
    | _ -> assert false

and wellformed_package ~poly ctx mty (p, lids, tys) visited =
  let sg = extract_sig ctx.env Location.none mty in
  let tds = find_types_in_sig lids sg in
  let visited' =
        List.fold_left (fun v t -> v >>= wellformed_type ~poly ctx t)
          (Ok visited) tys in
  match visited' with
    Error _ -> visited'
  | Ok _ -> let tds' = List.map2 (gen_typedecl true ctx.env) tds tys in
    List.fold_left2 (fun res (p, td) newtd ->
        match res with
          Error _ -> res
        | Ok ctx ->
          let id = Ident.create @@ Path.last p in
          match eq_type_decl ctx id newtd id td with
          | Ok ctx -> Ok ctx
          | Error _ -> Error (Incompatible_type_decls ((id, newtd), (id, td))))
      (Ok ctx) tds tds' >>=
    fun _ -> visited'

and wellformed_row ~poly ctx row visited =
  let inherited, visited = match row.row_name with
      None -> [], Ok visited
    | Some (p, tys) ->
      let inh = Env.find_type p ctx.env in
      (* Checks that the manifest exists (cannot be abstract), tests it for
         welformedness, and checks its arguments *)
      let inh =
        (match inh.type_manifest with
           None -> Error (Variant_inherits_abstract p)
         | Some ty -> Ok (ty, visited)) >>= fun (ty, visited) ->
        wellformed_type ~poly ctx ty visited >>=
        wellformed_type_list ~poly ctx tys >>= fun v ->
        Ok (ty, v) in
      (* Verifies that the row_name is a variant type *)
      let rec fields (ty, v) : ('a * 'b, error) result  =
        match (repr ty).desc with
          Tvariant rd -> Ok (rd, v)
        | Tconstr _ ->
          (try expand_abbrev ctx ty |> fun t -> fields (t, v)
           with Ctype.Cannot_expand ->
             Error (Variant_inconsistent_inheritance ty))
        | _ -> Error (Variant_inconsistent_inheritance ty)
      in
      (* Takes all the fields from the row_name *)
      match inh >>= fields with
        (Ok (rd, v)) when Btype.static_row (row_repr rd) ->
        rd.row_fields, Ok v
      | Error e -> [], Error e
      | _ -> [], Error Variant_inherited_not_static in
  (* Check every field + returns None if duplicate *)
  visited >>= fun visited ->
  List.fold_left (fun acc (l, f) ->
      acc >>= fun (seen, visited) ->
      if SMap.mem l seen then Error (Duplicate_variant_tag l)
      else
        wellformed_field ~poly ctx f visited >>= fun v ->
        Ok (SMap.add l f seen, v))
    (Ok (SMap.empty, visited))
    row.row_fields >>= fun (seen, v) ->
  (* For each inherited tag, verifies that it appear in the variant and with the
     same type *)
  List.fold_left (fun v (l, f) ->
      try let f' = SMap.find l seen in
        match eq_row_fields ctx (l, f) (l, f') with
          Ok _ -> v
        | Error _ -> Error (Variant_tag_mismatch (l, f, f'))
      with Not_found -> Error (Variant_tag_missing l)) (Ok v) inherited



and wellformed_field ~poly ctx field visited =
  match Btype.row_field_repr field with
    Rpresent ty -> wellformed_type_opt ~poly ctx ty visited
  | Reither (cst, tys, _, _) -> wellformed_type_list ~poly ctx tys visited
  | Rabsent -> Ok visited


and wellformed_type_opt ~poly ctx ty visited =
  match ty with
    Some ty -> wellformed_type ~poly ctx ty visited
  | None -> Ok visited

and wellformed_type_list ~poly ctx tys visited =
  List.fold_left (fun v t -> v >>= wellformed_type ~poly ctx t)
    (Ok visited) tys

and wellformed_object ~poly ctx ty prev visited =
  let ty = repr ty in
  match TyMap.mem ty visited with
    true -> Ok visited
  | false ->
    let visited' = TyMap.add ty () visited in
    match ty.desc, prev with
      Tfield (s, k, ty, tyrem), [] ->
      wellformed_type ~poly ctx ty visited'
      >>= wellformed_object ~poly ctx tyrem [s]
    | Tfield (s, k, ty, tyrem), s' :: _ ->
      let dup = List.exists ((=) s) prev in
      let order = String.compare s s' in
      if order > 0 && not dup then
        wellformed_type ~poly ctx ty visited'
        >>= wellformed_object ~poly ctx tyrem (s :: prev)
      else if order = 0 || dup then
        Error (Duplicate_field s)
      else Error Unordered_fields
    | Tvar _, _ -> Ok visited'
    | Tnil, _ -> Ok visited'
    | _ -> Error (Illformed_field ty)

let wellformed_type ctx ty =
  wellformed_type ~poly:false ctx ty TyMap.empty

let wellformed_type ctx ty =
  match wellformed_type ctx ty with
    Ok _ -> Ok ()
  | Error e -> Error e

exception Not_complete

let rec generalizable ctx ty vars =
  let ty = repr ty in
  match ty.desc with
    Tvar _ ->
    if TySet.mem ty ctx.generalized_vars then vars
    else TySet.add ty vars
  | Tunivar _ | Tnil -> vars
  | Tarrow (_, t1, t2, _) | Tfield (_, _, t1, t2) ->
    let v1 = generalizable ctx t1 vars in
    generalizable ctx t2 v1
  | Ttuple tys | Tconstr (_, tys, _) | Tpackage (_, _, tys) ->
    List.fold_left (fun vars ty -> generalizable ctx ty vars) vars tys
  | Tobject (ty, _) | Tlink ty | Tsubst ty | Tpoly (ty, _) ->
    generalizable ctx ty vars
  | Tvariant { row_fields } ->
    List.fold_left (fun vars (l, rf) ->
        match rf with
          Rpresent (Some ty) -> generalizable ctx ty vars
        | Reither (_, tys, _, _) ->
          List.fold_left (fun vars ty -> generalizable ctx ty vars) vars tys
        | _ -> vars) vars row_fields

let rec generalizable_nonvalue ctx ty pos vars =
  let open Asttypes in
  let ty = repr ty in
  (* print_debug ( *)
  (*   Format.asprintf "generalizable_nonvalue: %a" *)
  (*     Printtyp.raw_type_expr ty); *)
  match ty.desc with
    Tvar _ ->
    if TySet.mem ty ctx.generalized_vars ||
       (TyMap.mem ty vars && pos <> Contravariant)  then vars
    else TyMap.add ty pos vars
  | Tarrow (_, t1, t2, _) ->
    let vars = generalizable_nonvalue ctx t1 Contravariant vars in
    generalizable_nonvalue ctx t2 pos vars
  | Tconstr (p, tys, _) ->
    let tdecl = Env.find_type p ctx.env in
    List.fold_left2 (fun vars v ty ->
        let pos =
          if Variance.(mem May_weak v) then Contravariant
          else Covariant in
        generalizable_nonvalue ctx ty pos vars)
      vars tdecl.type_variance tys
  | Ttuple tys ->
    List.fold_left (fun vars ty ->
        generalizable_nonvalue ctx ty pos vars) vars tys
  | Tunivar _ | Tnil -> vars
  | Tobject (ty, _) | Tlink ty | Tsubst ty | Tpoly (ty, _) ->
    generalizable_nonvalue ctx ty pos vars
  | Tfield (_, _, t1, t2) ->
    let v1 = generalizable_nonvalue ctx t1 pos vars in
    generalizable_nonvalue ctx t2 pos v1
  | Tpackage (_, _, tys) ->
    List.fold_left (fun vars ty ->
        generalizable_nonvalue ctx ty Contravariant vars) vars tys
  | Tvariant { row_fields } ->
    List.fold_left (fun vars (l, rf) ->
        match rf with
          Rpresent (Some ty) -> generalizable_nonvalue ctx ty pos vars
        | Reither (_, tys, _, _) ->
          List.fold_left (fun vars ty ->
              generalizable_nonvalue ctx ty pos vars) vars tys
        | _ -> vars) vars row_fields

let check_gen ctx loc is_val ty_expr =
  try
    if is_val then
      begin
        let vars = generalizable ctx ty_expr TySet.empty in
        TySet.iter (fun ty ->
            if ty.level <> Btype.generic_level then
              raise (Typing_error (Can_generalize ty, loc))
          ) vars;

        print_debug (
          Format.asprintf "Variables from check_gen:\n%!%a"
            (fun fmt vars ->
               ignore @@ TySet.fold (fun ty fmt ->
                   Format.fprintf fmt "%a: %a\n%!"
                     Printtyp.type_expr ty
                     Printtyp.raw_type_expr ty;
                   fmt) vars fmt) vars)
      end
    else
      begin
        let open Asttypes in
        let vars =
          generalizable_nonvalue ctx ty_expr Covariant TyMap.empty in
        TyMap.iter (fun ty v ->
            match v with
              Covariant ->
              if ty.level <> Btype.generic_level then
                raise (Typing_error (Can_generalize ty, loc))
            | Contravariant | Invariant ->
              if ty.level = Btype.generic_level then
              raise (Typing_error (Cannot_generalize (ty_expr, ty), loc)))
          vars;
        print_debug (
          Format.asprintf "Variables from check_gen:\n%!%a"
            (fun fmt vars ->
               ignore @@ TyMap.fold (fun ty v fmt ->
                 Format.fprintf fmt "%a [%a]: %a\n%!"
                   Printtyp.type_expr ty
                   Typecheck_pretty.variance v
                   Printtyp.raw_type_expr ty;
                 fmt) vars fmt) vars)
      end
  with Not_complete ->
    Format.printf "Generalization checker not complete yet, assume OK.\n%!"

let gadt_split_existentials ctx ty_args ty_res =
  let tys = List.fold_left extract_vars_set TySet.empty ty_args in
  TySet.partition (fun ty -> occur ctx ty ty_res) tys

(* let gen_existential_decl ctx ty =  *)

let print_error_desc fmt = function
    Incompatible_types (t1, t2) ->
    Format.fprintf fmt "Types are incompatible: %a and %a."
      Printtyp.type_expr t1 Printtyp.type_expr t2
  | Incompatible_rows (r1, r2) ->
    Format.fprintf fmt "Both rows are incompatible:\n%a\nand\n%a."
      Printtyp.type_expr (newgenty @@ Tvariant r1)
      Printtyp.type_expr (newgenty @@ Tvariant r2)
  | Label_mismatch (l1, l2) ->
    Format.fprintf fmt
      "Label %s and %s mismatches" l1 l2
  | Type_argument_mismatch ->
    Format.fprintf fmt "Number of arguments applied to the type constructor is different."
  | Tag_type_mismatch l ->
    Format.fprintf fmt "The tag `%s has a different type in the expected type." l
  | Incoherent_instantiation (v, ty, ty') ->
    Format.fprintf fmt
      "The type variable %a was previously instantiated with the type:\n%a\n\
       It is not compatible with:\n%a."
      Printtyp.type_expr v
      Printtyp.type_expr ty
      Printtyp.type_expr ty'
  | Incoherent_polymorphic_instantiation (ty, ty') ->
    Format.fprintf fmt
      "The universal variable %a cannot be made equivalent with %a.\n\
       The polymorphic type is not an instance valid."
      Printtyp.type_expr ty Printtyp.type_expr ty'
  | Incompatible_modtypes_decl (mty1, mty2) ->
    Format.fprintf fmt
      "The module type:\n%a\ncannot be coerced into\n%a."
      (fun fmt mty ->
         match mty with None -> Format.fprintf fmt "<abstract>"
                      | Some mty1 -> Printtyp.modtype fmt mty1) mty1
      (fun fmt mty ->
         match mty with None -> Format.fprintf fmt "<abstract>"
                      | Some mty2 -> Printtyp.modtype fmt mty2) mty2
  | Incompatible_modtypes (mty1, mty2) ->
    Format.fprintf fmt
      "The module type:\n%a\ncannot be coerced into\n%a."
      Printtyp.modtype mty1 Printtyp.modtype mty2
  | Incompatible_type_decls ((id1, td1), (id2, td2)) ->
    Format.fprintf fmt
      "Type declarations are not compatible:\n%a\nand\n%a."
      (Printtyp.type_declaration id1) td1
      (Printtyp.type_declaration id2) td2
  | Unbound_item item ->
    Format.fprintf fmt
      "The item %a is not available in the signature to be coercible."
      Printtyp.signature [item]
  | Unbound_type_constructor p ->
    Format.fprintf fmt
      "The type constructor %a is unbound in the current context, \
       it might be escaping its scope."
      Printtyp.path p
  | Illformed_type_application ty ->
    Format.fprintf fmt
      "This type application is illformed: %a." Printtyp.type_expr ty
  | Unbound_universal_variable ty ->
    Format.fprintf fmt
      "The universal type variable %a has not been quantified."
    Printtyp.type_expr ty
  | Illformed_package_type ty ->
    Format.fprintf fmt "The package type %a is illformed."
      Printtyp.type_expr ty
  | Variant_inherits_abstract p ->
    Format.fprintf fmt "This variant type inherits from the tyep constructor \
                        %a,\n which is abstract."
      Printtyp.path p
  | Variant_inconsistent_inheritance ty ->
    Format.fprintf fmt "This variant type inherits from type %a. It must inherit \
                        from a variant."
      Printtyp.type_expr ty
  | Variant_inherited_not_static ->
    Format.fprintf fmt "The variant inherit is not static."
  | Variant_tag_mismatch (s, r1, r2) ->
    Format.fprintf fmt
      "The tag %s has type ??,\n\
       but was expected with type ??."
      s
  | Duplicate_variant_tag s ->
    Format.fprintf fmt
      "The tag %s appears multiple time." s
  | Variant_tag_missing s ->
    Format.fprintf fmt
      "The tag %s is missing." s
  | Duplicate_field f ->
    Format.fprintf fmt
      "The field %s appears multiple time." f
  | Unordered_fields ->
    Format.fprintf fmt "The fields of this object type are not correctly
    ordered."
  | Illformed_field ty ->
    Format.fprintf fmt
      "This object contains a type %a, but it must contain either a method or a \
       row variable."
      Printtyp.type_expr ty
  | Unbound_field f ->
    Format.fprintf fmt
      "The field %s is missing." f
  | Incompatible_class_types (cty1, cty2) ->
    Format.fprintf fmt
      "The class types are incompatible:\n%a\nand\n%a."
      Printtyp.class_type cty1 Printtyp.class_type cty2
  | Can_generalize ty ->
    Format.fprintf fmt "The type variable %a should have been generalized."
      Printtyp.type_expr ty
  | Cannot_generalize (ty, var) ->
    Format.fprintf fmt
      "This expression has type %a.\n\
       The type variable %a cannot be generalized."
      Printtyp.type_expr ty
      Printtyp.type_expr var
  | Types_error e -> Typecheck_types.print_error fmt e
  | Error_msg s ->
    Format.fprintf fmt "%s" s

let print_error fmt (e, loc) =
  Format.fprintf fmt "%a\n%a\n"
    Location.print_loc loc
    print_error_desc e

let _ =
  Typecheck_types.instance_types_ref :=
    (fun ctx tys1 tys2 s ->
      match instance_types ctx tys1 tys2 s with
        Ok ctx -> Ok ctx
      | Error e -> Error (Typing_error (e, Location.none)));
  Typecheck_types.apply_subst_ref := apply_subst;
  Typecheck_ctype.eq := (fun env t1 t2 ->
    match eq (create_context env) t1 t2 with
      Ok _ -> true | Error _ -> false)
