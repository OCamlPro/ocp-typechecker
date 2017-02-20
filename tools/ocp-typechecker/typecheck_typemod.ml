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

open OCaml
open Typedtree
open Types
open Btype
open Env
open Typecheck_utils
open Typecheck_flags
open Typecheck_expr
open Typecheck_types
open Typecheck_result
open Typecheck_class

module Ctype = Typecheck_ctype

type error =
    Cannot_coerce of module_type * module_type
  | Incorrect_functor_application of module_type * module_type
  | Incorrect_substitution
  | Cannot_apply_with_constraint
  | Unbound_modtype of Path.t
  | Unbound_module of Path.t | Generative_application
  | Modtype_generated_functor_body
  | Not_a_functor of module_type
  | Not_a_package of type_expr
  | Incompatible_package_types of type_expr * module_type
  | Typechecked_modtype_different of module_type * module_type
  | Typechecked_signature_different of signature * signature
  | Typecheck_incorrect_constraint of module_type * module_type
  | Typecheck_inconsistence of string

exception Typemod_error of (error * Location.t)

let raise_error loc error =
  raise (Typemod_error (error, loc))

(* From OCaml.Typemod *)
exception Not_a_path

let rec path_of_module mexp =
  let open Path in
  match mexp.mod_desc with
    Tmod_ident (p,_) -> p
  | Tmod_apply(funct, arg, coercion) when !Clflags.applicative_functors ->
      Papply(path_of_module funct, path_of_module arg)
  | Tmod_constraint (mexp, _, _, _) ->
      path_of_module mexp
  | _ -> raise Not_a_path

let is_empty_struct = function
  Tmod_structure { str_items = []; } -> true | _ -> false

let make_next_first rs l =
  if rs = Trec_not then l else
    match l with
      Sig_type (id, decl, Trec_next) :: rem ->
      Sig_type (id, decl, Trec_first) :: rem
    | Sig_module (id, decl, Trec_next) :: rem ->
      Sig_module (id, decl, Trec_first) :: rem
    | _ -> l

(* Adapted from typemod *)
exception Exit
let get_typesubst_path decl =
  try
    match decl.type_manifest with
    | Some { desc = Tconstr (p, args, _) }
      when List.length args = List.length decl.type_params ->
      List.iter2 (fun x y ->
          match x, y with
            { desc = Tvar x }, { desc = Tvar y } when x = y -> ()
          | _ -> raise Exit) args decl.type_params;
      p
    | _ -> raise Exit
  with Exit ->
    raise_error decl.type_loc Incorrect_substitution
    (* failwith "With substitutions needs a type constructor" *)

(* For recursive modules *)
let anchor_submodule p id =
  let open Path in
  match p with
    None -> p
  | Some p -> Some (Pdot (p, Ident.name id, -1))

(** Typing module types/signatures *)

(* Context -> loc -> signature to substitue -> path of the type -> constraint to
   apply *)
let apply_constraint ctx loc sg p constr =
  let rec step ctx constr names row_id sg =
    print_debug
    (Format.asprintf "Current constraint: %a"
      Typecheck_pretty.with_constraint (p, Location.mknoloc (Longident.Lident
                                                               ".."), constr));
    match sg, names, constr with
    | [], _, _ -> raise_error loc Cannot_apply_with_constraint
    | (Sig_type (id, decl, rs) :: rem, [s],
      Twith_type ({typ_kind = Ttype_abstract} as decl')) when
        Ident.name id = s && Typecheck_typedecl.is_fixed_type decl' ->
      assert false
    | (Sig_type (id, orig_decl, rs) :: rem, [s], Twith_type decl)
      when Ident.name id = s ->
      print_debug "Found type decl";
      let decl' =
        Typecheck_typedecl.type_constraint_decl ctx.env id None orig_decl decl in
      (* check_type_decl *)
      Sig_type (id, decl', rs) :: rem
    | (Sig_type(id, decl, rs) :: rem, [s], (Twith_type _ | Twith_typesubst _))
      when Ident.name id = s ^ "#row" ->
      step ctx constr names (Some id) rem
    | (Sig_type (id, orig_decl, rs) :: rem, [s], Twith_typesubst decl)
      when Ident.name id = s ->
      let decl' =
        Typecheck_typedecl.type_constraint_decl ctx.env id None orig_decl decl in
      (* check_type_decl *)
      let sg = make_next_first rs rem in
      (* Apply substitution *)
      let p = get_typesubst_path decl' in
      Subst.signature (Subst.add_type id p Subst.identity) sg
    | (Sig_module (id, md, rs) :: rem, [s], Twith_module (p, _)) when
        Ident.name id = s ->
      let md' = Env.find_module p ctx.env in
      let md' = { md' with md_type = Mtype.remove_aliases ctx.env md'.md_type } in
      let md' = Mtype.strengthen_decl ctx.env md' p in
      (* replaces all abstract types t by type t = p.t, allows equality over
         abstract types *)
      begin
        (* Does the previous type matches the new one? I.e., can the new module
           type can be constrained by the old type *)
        match Typecheck_typing.coercible_mty
                ctx
                md'.md_type md.md_type
                Typecheck_types.TyMap.empty with
          Ok _ -> Sig_module (id, md', rs) :: rem
        | Error _ -> raise_error loc @@ Cannot_coerce (md'.md_type, md.md_type)
      end
    | (Sig_module (id, md, rs) :: rem, [s], Twith_modsubst (p, _))
      when Ident.name id = s ->
      let md' = Env.find_module p ctx.env in
      let md' = Mtype.strengthen_decl ctx.env md' p in
      print_debug (Format.asprintf "orig: %a\nnewmty: %a"
                             Printtyp.modtype md.md_type Printtyp.modtype md'.md_type);
      let sg =
        (* Does the previous type matches the new one? I.e., can the new module
           type can be constrained by the old type *)
        match Typecheck_typing.coercible_mty
                ctx md'.md_type md.md_type
                Typecheck_types.TyMap.empty with
          Ok _ -> make_next_first rs rem
        | Error _ -> raise_error loc @@ Cannot_coerce (md'.md_type, md.md_type)
      in
      Subst.signature (Subst.add_module id p Subst.identity) sg
    | (Sig_module (id, md, rs) :: rem, s :: names, _) when Ident.name id = s ->
      let sg' = step ctx constr names row_id @@
        extract_sig ctx.env md.md_loc md.md_type in
      Sig_module (id, { md with md_type = Mty_signature sg'}, rs) :: rem
    | (item :: rem, _, _) ->
      print_debug "In remaining case";
      item :: step
        { ctx with env = Env.add_item item ctx.env }
        constr names row_id rem
  in
  let names = path_flatten p in
  step ctx constr names None sg

let enrich_module_type : Path.t option -> string -> Types.module_type -> Env.t ->
  Types.module_type =
  fun anchor (name : string) mty env ->
  let open Path in
  match anchor with
    None -> mty
  | Some p -> assert false (* Mtype.enrich_modtype env (Pdot(p, name, nopos)) mty *)

let rec transl_modtype (ctx : context) tmty =
  let dbmode = debug_mode tmty.mty_attributes in
  transl_modtype_desc ctx tmty.mty_loc tmty.mty_desc tmty.mty_type;
  dbmode ();
  tmty.mty_type


and transl_modtype_desc (ctx : context) loc tmty mty =
  match tmty, mty with
    Tmty_ident (p, lid), Mty_ident p' when PathEq.eq ctx.paths p p' |> snd ->
    begin
      try ignore @@ Env.find_modtype p ctx.env
      with Not_found -> raise_error lid.Location.loc @@ Unbound_modtype p
    end
  | Tmty_alias (p, lid), Mty_alias p' when PathEq.eq ctx.paths p p' |> snd ->
    begin
      try ignore @@ Env.find_module p ctx.env
      with Not_found -> raise_error lid.Location.loc @@ Unbound_module p
    end
  | Tmty_signature sg, Mty_signature sg' ->
    let sg'', _ = transl_signature ctx sg in
    begin
      match Typecheck_typing.eq_sg ctx sg' sg'' with
        Error e -> assert false
      | Ok _ -> ()
    end
  | Tmty_functor (p, _, arg, res), Mty_functor (p', arg', res')
    when Ident.same p p' ->
    let arg'' = may_map (transl_modtype ctx) arg in
    begin
      match Typecheck_typing.eq_mty_opt true ctx arg' arg'' with
        Error e -> assert false
      | Ok _ -> ()
    end;
    let env' = Env.add_module ~arg:true p (Btype.default_mty arg') ctx.env in
    let ctx' = { ctx with env = env' } in
    let res'' = transl_modtype ctx' res in
    begin
      match Typecheck_typing.eq_mty ctx' res' res'' with
        Error e -> assert false
      | Ok _ -> ()
    end
  | Tmty_with (body, cstrs), Mty_signature sg ->
    let mty = transl_modtype ctx body in
    let sg' = type_mty_with ctx loc mty cstrs in
    begin match Typecheck_typing.eq_sg ctx sg sg' with
        Error e -> assert false
      | Ok _ -> ()
    end
  | Tmty_typeof md, mty ->
    let mty', _ = type_module ctx false None md in
    begin
      match Typecheck_typing.eq_mty ctx mty mty' with
        Error e -> assert false
      | Ok _ -> ()
    end
  | _, _ -> assert false

and type_mty_with ctx loc mty cstrs =
  let sg = extract_sig ctx.env loc mty in
  print_debug (Format.asprintf "Original sig: %a"
    Printtyp.signature sg);
  let sg' = List.fold_left (fun sg (p, _, constr) ->
      apply_constraint ctx loc sg p constr) sg cstrs in
  print_debug (Format.asprintf "Generated: %a"
    Printtyp.signature sg');
  sg'

and transl_signature ctx sg =
  let ctx, sg' = List.fold_left (fun (ctx, sgis) sgi ->
      let sgi', ctx' = transl_signature_item_desc ctx sgi.sig_desc in
      ctx', sgi' @ sgis) (ctx, []) sg.sig_items in
  let sg' = List.rev sg' in
  match Typecheck_typing.eq_sg ctx sg' sg.sig_type with
    Ok _ -> sg', ctx
  | Error _ -> raise_error (signature_location sg.sig_items) @@
    Typechecked_signature_different (sg.sig_type, sg')

and transl_signature_item_desc ctx = function
    Tsig_value vd ->
    let v, ctx = Typecheck_typedecl.type_value_decl ctx vd in
    [v], ctx
  | Tsig_type decls ->
    let vds, env = Typecheck_typedecl.type_tydecl ctx.env decls in
    List.map (fun (id, vd, rs) -> Sig_type (id, vd, rs)) vds, { ctx with env }
  | Tsig_typext te ->
    let cstrs, env = Typecheck_typedecl.type_typext ctx.env te in
    List.map (fun (id, ext, rs) -> Sig_typext (id, ext, rs)) cstrs, { ctx with env }
  | Tsig_exception ext ->
    let tsg = Tsig_typext {
        tyext_path = Predef.path_exn;
        tyext_txt = Location.mkloc (longident_of_path Predef.path_exn) ext.ext_loc;
        tyext_params = [];
        tyext_constructors = [ ext ];
        tyext_private = Asttypes.Public;
        tyext_attributes = []; } in
    let sg_items, ctx = transl_signature_item_desc ctx tsg in
    List.map (function
          Sig_typext (id, ext, rs) -> Sig_typext (id, ext, Text_exception)
        | _ -> assert false) sg_items, ctx
  | Tsig_module md ->
    let mdty = transl_modtype ctx md.md_type in
    let decl = { md_type = mdty; md_attributes = md.md_attributes;
                 md_loc = md.md_loc } in
    let env = Env.add_module_declaration md.md_id decl ctx.env in
    [Sig_module (md.md_id, decl, Trec_not)], { ctx with env }
  | Tsig_modtype mtd ->
    let mty = may_map (transl_modtype ctx) mtd.mtd_type in
    let decl = { mtd_type = mty; mtd_attributes = mtd.mtd_attributes;
                 mtd_loc = mtd.mtd_loc } in
    let env = Env.add_modtype mtd.mtd_id decl ctx.env in
    [Sig_modtype (mtd.mtd_id, decl)], { ctx with env }
  | Tsig_open op ->
    let md = Env.find_module op.open_path ctx.env in
    let sg = extract_sig_open ctx.env op.open_loc md.md_type in
    let env = Env.open_signature op.open_override op.open_path sg ctx.env in
    [], { ctx with env }
  | Tsig_include incl ->
    let mty = transl_modtype ctx incl.incl_mod in
    let sg = Subst.signature Subst.identity @@
      extract_sig_open ctx.env incl.incl_loc mty in
    let env = Env.add_signature sg ctx.env in
    sg, { ctx with env }
  | _ -> assert false


(** Typing modules and structure *)

and type_module ?(alias=false) ctx sttn path md =
  print_debug (
    Format.asprintf "Typechecking module:\n%a\n%!"
      Typecheck_pretty.module_expression md);
  let dbmode = debug_mode md.mod_attributes in
  let ctx =
    type_module_desc alias ctx false path md.mod_loc md.mod_desc md.mod_type in
  dbmode ();
  md.mod_type, ctx

and type_module_desc alias ctx sttn (path:Path.t option) loc desc mty : context =
  match desc, mty with
    Tmod_structure str, _ ->
    let sg = match Env.scrape_alias ctx.env mty with
        Mty_signature sg -> sg
      | _ -> assert false
    in
    let sg', ctx' = type_structure ctx path str in
    begin
      match Typecheck_typing.eq_sg ctx sg sg' with
        Error e ->
        raise Typecheck_typing.(Typing_error (e, loc))
      | Ok _ -> ctx'
    end

  | Tmod_ident (path, lid), Mty_alias p
    when alias && not (Env.is_functor_arg path ctx.env) -> ctx

  | Tmod_ident (path, lid), _ ->
    let mty' =
      try (Env.find_module path ctx.env).md_type
      with Not_found ->
        raise_error lid.Location.loc @@ Unbound_module path in
    (* Some work to do in case of aliases *)
    let mty' =
      match mty' with
        Mty_alias p when not alias ->
        let p' = Env.normalize_path None ctx.env p in
        let mty' = (Env.find_module p' ctx.env).md_type in
        Mtype.strengthen ctx.env mty' p'
      | _ -> Mtype.strengthen ctx.env mty path in
    (* Should the strengthening be done here as in the compiler (which is
       required for correct nodes) or only at module bindind? *)
    begin
      match Typecheck_typing.eq_mty ctx mty mty' with
        Error e -> assert false
      | Ok _ -> ctx
    end

  | Tmod_functor (id, _, arg_mty, body), _ ->
    let id', arg_mty', mty_body =
      match Env.scrape_alias ctx.env mty with
        Mty_functor (id', arg_mty', mty_body) -> id', arg_mty', mty_body
      | _ -> assert false
    in
    assert (Ident.same id id');
    let ctx' =
      match arg_mty, arg_mty' with
        None, None -> ctx (* case of purely generative functors,
                             i.e. functor() -> ... *)
      | Some mty, Some mty' ->
        print_debug
          (Format.asprintf "body of: Tmod_functor (%a, ...)"
             Typecheck_pretty.ident id);
        let mty'' = transl_modtype ctx mty in
        (match Typecheck_typing.eq_mty ctx mty' mty'' with
          Error e ->
          raise Typecheck_typing.(Typing_error (e, loc))
        | Ok _ ->
          { ctx with env = Env.add_module ~arg:true id mty' ctx.env })
      | _, _ -> assert false
    in
    let tbody, _ = type_module ctx' true path body in
    begin
      match Typecheck_typing.eq_mty ctx' tbody mty_body with
        Error e ->
        raise Typecheck_typing.(Typing_error (e, loc))
      | Ok _ -> ctx
    end
  | Tmod_apply (funct, arg, c), _ ->
    let arg_mty, ctx = type_module ctx sttn path arg in
    let arg_path = try Some (path_of_module arg) with Not_a_path -> None in
    let f_mty, ctx = type_module ctx (sttn && arg_path <> None) path funct in
    begin
      match Env.scrape_alias ctx.env f_mty with
        Mty_functor (id, param, body) ->
        let generative, param =
          (param = None, Btype.default_mty param) in
        if generative then begin (* purely generative case verifications *)
          if not @@ is_empty_struct arg.mod_desc  then
            raise_error loc Generative_application;
          if (* in functor body && the functor contains modtypes *) false then
            raise_error loc Modtype_generated_functor_body
        end;
        (* We need to verify that the arg type is included in the module type *)
        let ctx =
          match Typecheck_typing.coercible_mty
                  ctx arg_mty param
                  Typecheck_types.TyMap.empty with
            Error _ -> raise_error arg.mod_loc @@
            Incorrect_functor_application (arg_mty, param)
          | Ok (_, ctx) -> ctx
        in
        let mty_res = match arg_path with
            Some path ->
            Subst.modtype (Subst.add_module id path Subst.identity) body
          | None ->
            if generative then body
            else try
                  Mtype.nondep_supertype
                    (Env.add_module ~arg:true id arg.mod_type ctx.env)
                    id body
              with Not_found -> failwith "Cannot eliminate dependency" in
        begin
          match Typecheck_typing.eq_mty ctx mty mty_res with
            Error e ->
            raise Typecheck_typing.(Typing_error (e, loc))
          | Ok _ -> ctx
        end
      | mty -> raise_error funct.mod_loc @@ Not_a_functor mty
    end
  | Tmod_constraint (md, mtyc, cstr, _), _ ->
    (* module_expr, module type of the constraint, constraint, _ *)
    let mdt, ctx = type_module ~alias ctx true path md in
    let cstr_mty = match cstr with
        Tmodtype_implicit -> mtyc
      | Tmodtype_explicit mtd ->
        let mty' = transl_modtype ctx mtd in
        match Typecheck_typing.eq_mty ctx mtyc mty' with
          Ok _ -> mty'
        | Error _ ->
          raise_error mtd.mty_loc @@
          Typecheck_incorrect_constraint (mtyc, mty')
    in
    print_debug (Format.asprintf "orig: %a\nconstrained: %a"
                           Printtyp.modtype mdt Printtyp.modtype cstr_mty);
    if !Typecheck_flags.debug then
      begin try ignore @@ Includemod.modtypes ctx.env mdt cstr_mty; (* mdt includes
                                                                       cstr_mty *)
          print_debug "Is included"
        with _ -> print_debug "Not included" end;
    begin
      match Typecheck_typing.coercible_mty
              ctx mdt cstr_mty
              Typecheck_types.TyMap.empty with
        Error _ -> raise_error loc (Cannot_coerce (mdt, cstr_mty))
      | Ok _ ->
        match Typecheck_typing.eq_mty ctx mty cstr_mty with
          Error e -> assert false
        | Ok _ -> ctx
    end
  | Tmod_unpack (expr, mty_p), _ ->
    let ty, env = Typecheck_expr.type_expr_aux ctx expr expr.exp_type in
    let mty_pack = match Ctype.expand_head ctx.env ty with
        { desc = Tpackage (p, nl, tl) }->
        Typecheck_types.create_package_mty ctx.env (Mty_ident p) nl tl
      | ty -> raise_error expr.exp_loc @@ Not_a_package ty in
    begin
      Typecheck_typing.coercible_mty ctx mty_p mty_pack TyMap.empty |> function
      Error _ -> raise_error loc @@
      Incompatible_package_types (ty, mty)
    | Ok _ ->
      match Typecheck_typing.eq_mty ctx mty mty_pack with
        Error e -> assert false
      | Ok _ -> ctx
    end


and type_structure ctx (path : Path.t option) strc =
  print_debug "type_structure:";
  (* type structure, then verify the type is a subtype (actually should be the
     same) of the annotated signature *)
  let ctx', sg = type_structure_items ctx path strc.str_items in
  print_debug (Format.asprintf "before-includemod: \n sig:\n%a\n"
                         Printtyp.signature sg);
  print_debug (Format.asprintf "Original sig: %a"
                         Printtyp.signature strc.str_type);
  (* let coerce = try *)
  (*     Includemod.signatures ctx'.env sg strc.str_type *)
  (*   with Includemod.Error *)
  (*           ((_, _, *)
  (*            Includemod.Type_declarations (id, d1, d2, errs)) :: _) as exn -> *)
  (*     Format.eprintf "%a\n%a\n%!" *)
  (*       Typecheck_pretty.Types.type_declaration d1 *)
  (*       Typecheck_pretty.Types.type_declaration d2 *)
  (*     ; *)
  (*     raise exn *)
  (* in *)
  let coerce = Tcoerce_none in
  print_debug "after-includemod";
  print_debug (Format.asprintf "Coercion:\n%a" Includemod.print_coercion coerce);
  if not (coerce = Tcoerce_none) then
    raise_error (structure_location strc.str_items) @@
    Typechecked_signature_different (sg, strc.str_type);
  Typemod.simplify_signature sg, ctx'

and type_structure_items ctx (path : Path.t option) its =
  List.fold_left (fun (ctx, acc) it ->
      let vals, ctx = type_structure_item_desc ctx path it.str_desc in
      ctx, acc @ vals) (ctx, []) its

and type_structure_item_desc ctx (path : Path.t option) = function
    Tstr_eval (expr, attrs) -> let _ = type_top_expr ctx expr in [], ctx
  | Tstr_value (flag, vbs) ->
    let tys, ctx = type_bindings ctx vbs flag in
    (* generate Sig_value list from tys *)
    List.map (fun (id, vd, _) -> Sig_value (id, vd)) tys, ctx
  | Tstr_primitive vd ->
    let v, ctx = Typecheck_typedecl.type_value_decl ctx vd in
    [v], ctx
  | Tstr_type decls ->
    let vds, env = Typecheck_typedecl.type_tydecl ctx.env decls in
    List.map (fun (id, vd, rs) -> Sig_type (id, vd, rs)) vds, { ctx with env }
  | Tstr_typext te ->
    let cstrs, env = Typecheck_typedecl.type_typext ctx.env te in
    List.map (fun (id, ext, rs) -> Sig_typext (id, ext, rs)) cstrs, { ctx with env }
  | Tstr_exception ext ->
    let tstr = Tstr_typext {
        tyext_path = Predef.path_exn;
        tyext_txt = Location.mkloc (longident_of_path Predef.path_exn) ext.ext_loc;
        tyext_params = [];
        tyext_constructors = [ ext ];
        tyext_private = Asttypes.Public;
        tyext_attributes = []; } in
    let sg_items, ctx = type_structure_item_desc ctx path tstr in
    List.map (function
          Sig_typext (id, ext, rs) -> Sig_typext (id, ext, Text_exception)
        | _ -> assert false) sg_items, ctx
  | Tstr_module mb ->
    let mty, ctx = type_module ~alias:true ctx
        true (anchor_submodule path mb.mb_id) mb.mb_expr in
    let md = {
      md_type = enrich_module_type path (Ident.name mb.mb_id) mty ctx.env;
      md_attributes = mb.mb_attributes;
      md_loc = mb.mb_loc;
    } in
    let env = Env.add_module_declaration mb.mb_id md ctx.env in
    print_debug
      (Format.asprintf "module_type of %a: %a"
         Typecheck_pretty.ident mb.mb_id
         Printtyp.modtype md.md_type);
    let paths = match mty, mb.mb_expr.mod_desc with
        (Mty_alias p | Mty_ident p), _ | _, Tmod_ident (p, _) ->
        print_debug
          (Format.asprintf "module_type of %a: is an ident of %a"
             Typecheck_pretty.ident mb.mb_id
             Typecheck_pretty.path p);
        PathEq.union ctx.paths (Path.Pident mb.mb_id) p
      | _ -> ctx.paths in
    [Sig_module(mb.mb_id,
                {md_type = mty;
                 md_attributes = mb.mb_attributes;
                 md_loc = mb.mb_loc; }, Trec_not)], { ctx with env; paths }
  | Tstr_modtype mtyd ->
    print_debug (Format.asprintf "Translating modtype binding %a"
      Typecheck_pretty.ident mtyd.mtd_id);
    let mty = may_map (transl_modtype ctx) mtyd.mtd_type in
    let decl = { mtd_type = mty; mtd_attributes = mtyd.mtd_attributes;
                 mtd_loc = mtyd.mtd_loc } in
    print_debug (Format.asprintf "Adding modtype %a"
      Typecheck_pretty.ident mtyd.mtd_id);
    let env = Env.add_modtype mtyd.mtd_id decl ctx.env in
    [Sig_modtype (mtyd.mtd_id, decl)], {ctx with env }
  | Tstr_open op ->
    [], type_open op.open_override ctx op.open_path
  | Tstr_include incl ->
    let mty, ctx = type_module ctx true None incl.incl_mod in
    let sg = Subst.signature Subst.identity @@
      extract_sig_open ctx.env incl.incl_loc mty in
    let sg' =
      match incl.incl_mod.mod_desc with
        Tmod_ident (p, _) when not @@ Env.is_functor_arg p ctx.env ->
        (* transforms module declarationss into aliases *)
        let pos = ref 0 in
        List.map
          (function
            | Sig_module (id, md, rs) ->
              let n = !pos in incr pos;
              Sig_module (id,
                          {md with md_type =
                                     Mty_alias (Path.Pdot(p,Ident.name id,n))},
                          rs)
            | Sig_value (_, {val_kind=Val_reg})
            | Sig_typext _ | Sig_class _ as it ->
              incr pos; it
            | Sig_value _ | Sig_type _ | Sig_modtype _
            | Sig_class_type _ as it ->
              it)
          sg
      | _ -> sg in
    let env = Env.add_signature sg' ctx.env in
    sg', { ctx with env }
  | Tstr_recmodule _ -> assert false
  | Tstr_class cds ->
    type_class_decl ctx cds
  | Tstr_class_type ctds ->
    type_class_types ctx ctds
  | Tstr_attribute attr ->
    ignore @@ Typecheck_flags.debug_mode [ attr ];
    [], ctx
  (* | _ -> assert false *)

and type_open fl ctx p =
  let md = Env.find_module p ctx.env in
  let sg = extract_sig_open ctx.env md.md_loc md.md_type in
  let env = Env.open_signature fl p sg ctx.env in
  { ctx with env }

let _ = Typecheck_expr.typemod_type_module :=
    (fun ctx md -> type_module ctx true None md);
  Typecheck_expr.type_open := type_open


let print_error fmt = function
    Cannot_coerce (mty1, mty2) ->
    Format.fprintf fmt "The module type\n%a\nis not included in\n%a"
      Printtyp.modtype mty1 Printtyp.modtype mty2
  | Incorrect_substitution ->
    Format.fprintf fmt "The following type substitution in incorrect.\n\
      Substitued type must be a type constructor, and all arguments must be
    applied."
  | Cannot_apply_with_constraint ->
    Format.fprintf fmt "This `with constraint` cannot be applied, the binded
    type does not belong to the original signature or sub-subgnature"
  | Unbound_modtype p ->
    Format.fprintf fmt "Unbound module type %a."
      Printtyp.path p
  | Unbound_module p ->
    Format.fprintf fmt "Unbound module %a."
      Printtyp.path p
  | Generative_application ->
    Format.fprintf fmt "This functor has type `functor () -> ...`,\n\
                        It must be applied to `()` or the empty structure."
  | Modtype_generated_functor_body ->
    Format.fprintf fmt "This application will generate a module type. This \
      is not allowed in functor's body."
  | Incorrect_functor_application (arg, param) ->
    Format.fprintf fmt "The functor cannot be applied to\n%a.\n\
                        It is expected to have type\n%a."
      Printtyp.modtype arg Printtyp.modtype param
  | Not_a_functor mty ->
    Format.fprintf fmt "This module cannot be applied, it has type\n%a\n\
      while it is expected to have a functor type."
      Printtyp.modtype mty
  | Not_a_package ty ->
    Format.fprintf fmt "This expression is expected to a have a package type,\
                       while it is:\n%a."
      Printtyp.type_expr ty
  | Incompatible_package_types (pack, mty) ->
    Format.fprintf fmt "Package type\n%a\nis incompatible with the module\
                        type expected:\n%a."
      Printtyp.type_expr pack Printtyp.modtype mty

  (* Errors specific to the typechecker. *)
  | Typechecked_modtype_different (orig, checked) ->
    Format.fprintf fmt "The module type infered:\n%a\n\
                        is not equal with the one typechecked:\n%a"
      Printtyp.modtype orig Printtyp.modtype checked
  | Typechecked_signature_different (orig, checked) ->
    Format.fprintf fmt "The signature infered:\n%a\n\
                        is not equal with the one typechecked:\n%a"
      Printtyp.signature orig Printtyp.signature checked
  | Typecheck_incorrect_constraint (orig, checked) ->
    Format.fprintf fmt "The explicit constraint infered:\n%a\n is not compatible\
                        with the one typechecked:\n%a."
      Printtyp.modtype orig Printtyp.modtype checked
  | Typecheck_inconsistence msg ->
    Format.fprintf fmt "%s." msg

let print_error fmt (e, loc) =
  Format.fprintf fmt "%a\n%a\n"
    Location.print_loc loc
    print_error e

let _ =
  Typecheck_typexpr.typemod_transl_modtype := transl_modtype;
  Typecheck_types.apply_constraint := apply_constraint;
  Typecheck_expr.type_object := Typecheck_class.type_object
