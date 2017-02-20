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
open Typecheck_ctype
open Env
open Typecheck_utils
open Typecheck_flags
open Typecheck_typing
open Typecheck_types
open Typecheck_result

type pass = Infered | Checked (* For wellformedness and better error reporting *)

type error =
    Incompatible_types of type_expr * type_expr
  | Illformed_type of type_expr * pass
  | Pattern_package_expected of type_expr
  | Pattern_already_bound_var of Ident.t
  | Pattern_type_clash of string * type_expr
  | Pattern_unexpected_variant of string * type_expr
  | Pattern_unexpected_variant_type of string * type_expr
  | Pattern_or_unbound_variable of string
  | Pattern_or_variable_clash of string * type_expr * type_expr
  | Pattern_or_ident_clash of Ident.t * Ident.t
  | Unbound_variable of Path.t
  | Type_unexpected of string * type_expr
  | Tag_absent_in_variant of string * type_expr
  | Variant_inconsistency of type_expr
  | Record_field_immutable
  | Typecheck_inconsistency of string
  | Module_not_packable of module_type * type_expr
  | Not_a_function of type_expr
  | Not_in_a_class
  | Immutable_instance_variable of Path.t
  | Unbound_instance_variable of Path.t
  | Constraint_not_applicable of type_expr * type_expr
  | Error_msg of string

exception Expr_error of (error * Typecheck_typing.error option * Location.t)

let raise_error ?(reason=None) loc error =
  raise (Expr_error (error, reason, loc))

let check loc ctx ty1 ty2 =
  match Typecheck_typing.eq ctx ty2 ty1 with
    Ok _ -> ()
  | Error r ->
    raise (Expr_error (Incompatible_types (ty1, ty2), Some r, loc))

let check_instance loc ctx ty1 ty2 =
  match Typecheck_typing.instance ctx ty1 ty2 TyMap.empty with
    Ok _ -> ()
  | Error r ->
    raise (Expr_error (Incompatible_types (ty1, ty2), Some r, loc))
(* (\* let instance _ ty = ty *\) *)

(* Check that all univars are safe in a type *)
let check_univars env expans kind exp ty_expected vars =
  let open Typecore in
  if expans && not (is_nonexpansive exp) then
    generalize_expansive env exp.exp_type;
  (* need to expand twice? cf. Ctype.unify2 *)
  let vars = List.map (expand_head env) vars in
  let vars = List.map (expand_head env) vars in
  let vars' =
    List.filter
      (fun t ->
        let t = repr t in
        generalize t;
        match t.desc with
          Tvar name when t.level = generic_level ->
            log_type t; t.desc <- Tunivar name; true
        | _ -> false)
      vars in
  if List.length vars = List.length vars' then () else
  let ty = newgenty (Tpoly(repr exp.exp_type, vars'))
  and ty_expected = repr ty_expected in
  raise (Error (exp.exp_loc, env,
                Typecore.Less_general(kind, [ty, ty; ty_expected, ty_expected])))


let add_pattern_variables env binded =
  SMap.fold (fun _ (ty, id, _) env ->
      let vd = { val_type = ty; val_kind = Val_reg; val_attributes = [];
                 val_loc = Location.none } in
      Env.add_value id vd env)
    binded env

let typemod_type_module =
  ref ((fun env md -> assert false) :
       context -> Typedtree.module_expr -> Types.module_type * context)

let type_module ctx md = !typemod_type_module ctx md

(* Forward declaration, to be filled in by Typecheck_typemod.type_open *)

let type_open =
  ref ((fun _ _ _ -> assert false) :
         Asttypes.override_flag -> context -> Path.t -> context)

(* (\* Forward declaration, to be filled in by Typecheck_typemod.type_package *\) *)

(* let type_package = *)
(*   ref (fun _ -> assert false) *)

(* (\* Forward declaration, to be filled in by Typecheck_typeclass.class_structure *\) *)
let type_object =
  ref (fun ctx loc s -> assert false :
       context -> Location.t -> Typedtree.class_structure ->
        Types.class_signature)

let rec type_pattern' ctx binded p ty_exp =
  let dbmode = debug_mode p.pat_attributes in
  print_debug "type_pattern':";
  (* Typing environment for patterns is a bit different. When typing a pattern,
     we must ensure that every variable is not binded twice, and in case of OR
     pattern, that a variable is binded on both branch.
     As a result, pattern typing judgement uses a "binded" argument, which
     simply binds the already typed variables.
     The pattern judgement is :
     env; binded P|- p : ty

     Binded is a Map using strings as keys (to efficiently retrieve variables
     with the same name but not the same ident, and type * ident as value (the
     ident is stored to type or_pattern, since two variables with the same name
     in two patterns of he or case must be exactly the same) *)
  (* ty, env *)
  print_debug (Format.asprintf "pat: %a; extras nb: %d"
    Typecheck_pretty.pattern p (List.length p.pat_extra));

  let ty, binded', ctx' =
    type_pattern_extra ctx binded p.pat_loc p.pat_extra p.pat_desc p.pat_type in
  print_debug (Format.asprintf "infered_type: %a\n\
                                        typecheck: %a\n====="
                         Printtyp.raw_type_expr p.pat_type
                         Printtyp.raw_type_expr ty);
  begin
    match wellformed_type { ctx' with gadt = false } ty with
      Ok () -> ()
    | Error r ->
      raise_error ~reason:(Some r) p.pat_loc @@ Illformed_type (ty, Checked)
  end;
  begin
    match wellformed_type { ctx' with gadt = false } p.pat_type with
      Ok () -> ()
    | Error r ->
      raise_error ~reason:(Some r) p.pat_loc
      @@ Illformed_type (p.pat_type, Infered)
  end;
  print_debug "end of:\n  type_pattern'";
  search_a ctx'.env;
  dbmode ();
  ty, binded', ctx'


and type_pattern_extra ctx binded loc extras expr tyexp =
  match extras, expr with
    [], expr -> type_pattern_desc ctx binded loc expr tyexp
  | (Tpat_constraint cty, _, _) :: l, expr ->
    print_debug "Pat constraint:";
    begin_def();
    let vars, gen = !(Variables.curr_vars) in
    let ty, _ =
      Typecheck_typexpr.transl_ctype_aux
        ctx vars Typecheck_typexpr.Extensible gen cty in
    end_def ();
    print_debug (Format.asprintf "Resulting constraint: %a"
      Printtyp.raw_type_expr ty);
    generalize_structure ty;
    print_debug
      (Format.asprintf "constraint: %a"
         Printtyp.raw_type_expr ty);
    print_debug "Determining the expected type";
    let ty = less_gen loc ctx.env ty tyexp in
    print_debug "Found a less general";
    let typat, binded, ctx = type_pattern_extra ctx binded loc l expr ty in
    print_debug
      (Format.asprintf "pattern: %a\n\
                        constraint: %a"
         Printtyp.raw_type_expr typat
         Printtyp.raw_type_expr ty);
    check loc ctx ty typat;
    typat, binded, ctx

  | (Tpat_unpack, _, _) :: l, expr ->
    let typat, binded, ctx = type_pattern_extra ctx binded loc l expr tyexp in
    print_debug
    (Format.asprintf "Unpack type: %a" Printtyp.raw_type_expr typat);
    if not @@ Typecheck_types.has_package_type typat then
      raise_error loc @@ Pattern_package_expected typat;
    typat, binded, ctx
  | _ -> assert false
(* we suppose the following functions:
   - vars(p) the set of variables binded by p

   The function returns the binded variables and the type of the
   pattern. Actually, only Tpat_var and Tpat_alias will explicitely bind a
   variable, whereas ohter constructs simply propagates the "binded" argument.

   The function needs the expected type as argument : it is actually necessary
   due to unification according to polymorphic types. As a matter of fact a type
   variable and a type variable explicitely polymorphic cannot be
   unified. However, it is unpredictable when a variable needs to be typed as
   explicitely polymophic (we cannot generate a fresh type variable and unify it
   with the expected type). As as result, we must propagate the type annotations.
*)
and type_pattern_desc ctx binded loc p tyexp =
  print_debug "type_pattern_desc:";
  match p with
    Tpat_any ->
    (* env; binded P|- _ : t *)
    tyexp, binded, ctx
  | Tpat_var (i, str) ->
    (* i # binded
       ==> env; binded P|- i : t; binded U { i : t } *)
    if SMap.mem (Ident.name i) binded then
      raise_error loc @@ Pattern_already_bound_var i;
    let ty = tyexp in
    ty, SMap.add (Ident.name i) (ty, i, SMap.cardinal binded) binded, ctx
  | Tpat_alias (p, i, str) ->
    (* i # binded
       && env; binded P|- p : ty
       ==> env; binded P|- p as i : ty
           && binded U vars(p) U { i : ty} *)
    let ty, binded', ctx' = type_pattern' ctx binded p tyexp in
    if SMap.mem (Ident.name i) binded then
      raise_error loc @@ Pattern_already_bound_var i;
    ty, SMap.add (Ident.name i) (ty, i, SMap.cardinal binded') binded', ctx'
  | Tpat_constant c ->
    (* c in builtin
       ==> env; binded P|- c : type(c) *)
    let ty = Typecheck_typecore2.type_constant c in
    ty, binded, ctx
  | Tpat_tuple pats ->
    (* \/p in pats,
         env; binded_i P|- p : tyi
           where binded_i = binded_(i-1) U vars(p(i-1)) && binded0 = binded
       ==> env; binded_n P|- (p0, .., pn) : (ty0 * .. * tyn); binded U vars(pats)
    *)
    print_debug (Format.asprintf "Type of Tpat_tuple:\n  %a"
      Printtyp.raw_type_expr tyexp);
    let tys = match Extract.extract_tuple_info ctx tyexp with
        Ok tys -> tys
      | Error e -> raise Typecheck_typing.(Typing_error (Types_error e, loc))
    in
    let tys, binded', ctx = List.fold_left2 (fun (tys, binded, ctx) p ty ->
        let ty', b', ctx = type_pattern' ctx binded p ty in
        ty' :: tys, b', ctx) ([], binded, ctx) pats tys in
    (* newty (Ttuple (List.rev tys)) *)tyexp, binded', ctx
  | Tpat_construct (lid, desc, pats) ->
    (* lid in desc.cstr_res
       \/p in pats && \/ty' in desc.cstr_args,
          env; binded_i P|- p : tyi
           where binded_i = binded_(i-1) U vars(p(i-1)) && binded0 = binded
          && unify tyi tyi'
       ==> env; binded P|- constr : tyres; binded U vars(pats) (* instantiated *)
    *)

    (* We get the constructor description of the longident *)
    let desc' = Env.lookup_constructor lid.Asttypes.txt ctx.env in
    print_debug (Format.asprintf "List of existentials: [%a]"
      (fun fmt exs -> List.iter (Format.fprintf fmt "%a;"
                                   Printtyp.raw_type_expr) exs)
      desc'.cstr_existentials);

    let tyargs, tyres = instance_constructor desc in
    let tyexp_args = desc'.cstr_args in
    let tyexp_res = desc'.cstr_res in

    print_debug (Format.asprintf "args: %a\nres: %a"
      (fun fmt -> List.iter (Format.fprintf fmt "%a; " Printtyp.type_expr))
      tyexp_args
      Printtyp.raw_type_expr tyexp_res);

    print_debug (Format.asprintf "args': %a\nres': %a"
      (fun fmt -> List.iter (Format.fprintf fmt "%a; " Printtyp.type_expr))
      tyargs
      Printtyp.raw_type_expr tyres);

    if !Typecheck_flags.debug then
      (let binded, exs =
        Typecheck_typing.gadt_split_existentials ctx tyexp_args tyexp_res in
       Format.printf "GADT_result: %a. Binded: %!"
         Printtyp.type_expr tyexp_res;
       TySet.iter (Format.eprintf "%a; %!" Printtyp.type_expr) binded;
       Format.printf "Existentials: %!";
       TySet.iter (Format.eprintf "%a; %!" Printtyp.type_expr) exs;
       Format.printf "\n%!");

    (* We set the flag in ctx to tell the typechecker that it will type a gadt *)
    let ctx = { ctx with gadt = desc'.cstr_generalized } in

    (* We check the infered type is an instance of the result type in the
       declaration of the constructor. *)
    begin
      match Typecheck_typing.instance ctx tyexp_res tyres TyMap.empty with
        Ok (_, _) -> ()
      | Error e -> raise (Typing_error (e, loc))
    end;

    let print_subst s =
      TyMap.fold (fun k v s ->
          Format.asprintf "%s (%a -> %a);"
            s Printtyp.raw_type_expr k Printtyp.type_expr v) s "Subst: " in   

    (* We extract every type variable in the expected type of arguments *)
    let vars = List.fold_left extract_vars_set TySet.empty tyexp_args in
    print_debug (
      Format.asprintf "vars: %a"
        (fun fmt ->
           TySet.iter (Format.fprintf fmt "%a; " Printtyp.type_expr))
        vars);
    let tyargs, binded, ctx, subst, vars =
      List.fold_left2 (fun (tys, binded, ctx, subst, vars) p tyexp ->
          print_debug (Format.asprintf "subpattern: %a of type %a \
                                                with expected type %a"
                                 Typecheck_pretty.pattern p
                                 Printtyp.type_expr p.pat_type
                                 Printtyp.type_expr tyexp);

          (* Generates a substitution between the type of the argument and the
             infered type *)
          let ty, ctx, subst =
            (((subst >>= fun subst ->
            print_debug "generation of equations";
            (* Ok (subst, ctx) *)
            add_equations (subst, ctx) p.pat_type tyexp) >>=
            fun (subst, ctx) ->

            print_debug (print_subst subst);
            instance ctx p.pat_type tyexp subst) >>=
            fun (subst, ctx) ->
            print_debug (print_subst subst);
            Ok (apply_subst tyexp subst, ctx, subst))
            |>
            get ~fail:(fun e -> raise (Typing_error (e, loc))) in
          print_debug (print_subst subst);
          
          (* For each type variable:
             * if its substitution exists and is a type constructor for an
             existentially quantified type, we adds its constructor into the
             environment to allow checking the wellformedness of the type in the
             branch of the pattern matching.
             * otherwise, do nothing
          *)
          let ctx, vars = TySet.fold (fun ty (ctx, vars) ->
              print_debug (Format.asprintf "looking for subst of %a"
                                     Printtyp.raw_type_expr ty);
              match TyMap.find ty subst with
                { desc = Tconstr ((Path.Pident ex) as p, [], _) }
                when is_existential p ->
                { ctx with
                  env = Env.add_type ~check:false ex exist_typedecl ctx.env
                }, TySet.remove ty vars
              | _ -> ctx, vars
              | exception Not_found -> print_debug "not_found"; ctx, vars
            ) vars (ctx, vars)
          in
          print_debug (Format.asprintf "tyexp for subpat: %a"
                                 Printtyp.raw_type_expr ty);
          (* Types the subpattern with the infered type which is equal to the
             type declared with the substitution applied on *)
          let tyarg, b, ctx = type_pattern' ctx binded p ty in
          print_debug (Format.asprintf "tyarg of subpat: %a"
                                 Printtyp.type_expr tyarg);

          (* Returns:
             * the type of the sub argument
             * the binded variables,
             * the new context that might contain new ambivalences,
             * the substitution with the already substituted variables which is
               necessary to check that shared variables in the arguments are
               binded by the same existential type
             * the remaining free type variables for future extracted
               existentials *)
          tyarg :: tys, b, ctx, Ok subst, vars)
        ([], binded, ctx, Ok TyMap.empty, vars) pats tyexp_args in
    
    (* Generates the result type of the constructor using the possibly extracted
       existential types *)
    let tyres' = apply_subst tyexp_res @@
      get ~fail:(fun e -> raise (Typing_error (e, loc))) subst in

    print_debug (Format.asprintf "Resulting type of gadt: %a"
                           Printtyp.type_expr tyexp);

    (* If we are typing a gadt, we check that the resulting type infered is an
       instance of the extracted type. This instance check will generate the
       ambivalences necessary to type the branch associated with the pattern. *)
    let ctx = if desc'.cstr_generalized then
        (print_debug "is_generalized";
         let check =
           subst >>= fun subst ->
           add_equations (subst, ctx) tyexp tyres' >>= fun (subst, ctx) ->
           instance ctx tyexp tyres' subst in
         match check with
           Error r ->
           raise (Expr_error (Incompatible_types (tyexp, tyexp_res), Some r, loc))
         | Ok (_, ctx) -> ctx)
      else ctx in
    tyres', binded, ctx

  | Tpat_variant (label, patopt, desc) ->
    (* label in desc.row_fields (-> l, field)
         && env; binded P|- patopt : ty
         && unify_variant ty field
         where unify_variant tries to unify the type with one of those possible
         in the field
       ==> env; binded |- variant : desc; binded U vars(variant)
    *)

    (* row_field: no mutation on the type given *)
    let desc =
      match Extract.extract_variant_info ctx tyexp with
        Ok rd -> rd
      | Error e -> raise Typecheck_typing.(Typing_error (Types_error e, loc))
    in
    let tyarg =
      match Btype.row_field label desc with
        Rpresent tyopt -> tyopt
      | Reither (cst, choice, p, rf) ->
        assert (cst && choice = [] || not cst && List.length choice > 0);
        (* assert p; *) (* since p = a tag present in a pattern matching *)
        (* List.iter (unify_opt ctx patopt) choice; *)
        if cst then None else Some (List.hd choice)
      | Rabsent ->
        raise_error loc @@ Pattern_unexpected_variant (label, tyexp)
    in
    let tyopt, binded, ctx = match patopt, tyarg with
        Some p, Some ty ->
        let ty, binded, ctx = type_pattern' ctx binded p ty in
        Some ty, binded, ctx
      | None, None -> None, binded, ctx
      | _, _ -> raise_error loc @@
        Pattern_unexpected_variant_type (label, tyexp) in
    check loc ctx tyexp (newty (Tvariant desc));
    tyexp, binded, ctx

  | Tpat_or (p1, p2, desc) ->
    (* Desc is for the case patterns include variants *)
    (* env; binded |- p1 : t1 && env; binded |- p2 : t2 && check t1 t2
       && binded1 = binded U vars(p1) && binded2 = binded U vars(p2)
       && binded1 - binded2 = {} // the same exact variables are binded on both
       sides
       ==> env; binded |- p1 | p2 : t1; binded1
    *)
    let ty1, binded1, ctx1 = type_pattern' ctx binded p1 tyexp in
    let ty2, binded2, ctx = type_pattern' ctx1 binded p2 tyexp in
    SMap.iter (fun v (ty, id, _) ->
        let (ty', id', _) =
          try SMap.find v binded2
          with Not_found -> raise_error loc @@
            Pattern_or_unbound_variable v in
        let ty, ty' = ty, ty' in
        (try check loc ctx ty ty'
         with Expr_error (Incompatible_types (_,_), r, _) ->
           raise_error ~reason:r loc @@
           Pattern_or_variable_clash (v, ty', ty));
        if not @@ Ident.equal id id' then
          raise_error loc @@ Pattern_or_ident_clash (id', id)) binded1;
    let ty1', ty2' = ty1, ty2 in
    check loc ctx ty1' ty2';
    tyexp, binded1, ctx
  | Tpat_record (fields, closed) ->
    let binded, ctx =
      List.fold_left (fun (binded, ctx) (lid, desc, pat) ->
        let desc, b, ctx =
          type_field_pattern ctx binded (lid, desc, pat) tyexp in
        let tyres = desc.lbl_res in
        check pat.pat_loc ctx tyexp tyres;
        b, ctx)
        (binded, ctx) fields in
    tyexp, binded, ctx
      (* !!! TODO: Check that a label only occur once, and that every label is
         present if closed *)

  | Tpat_array pl ->
    let tyval = match safe_expand_abbrev_max ctx tyexp with
        { desc = Tconstr (p, [tyval], _); }
        when snd @@ PathEq.eq ctx.paths p Predef.path_array -> tyval
      | _ -> raise_error loc @@ Pattern_type_clash ("array", tyexp) in
    let ty, binded, ctx = List.fold_left (fun (ty, binded, ctx) p ->
        let ty', b, ctx = type_pattern' ctx binded p tyval in
        check p.pat_loc ctx ty ty';
        ty, b, ctx) (tyexp, binded, ctx) pl in
    let array_ty = (Predef.type_array ty) in
    begin
      match Typecheck_typing.eq ctx array_ty tyexp with
        Ok ctx -> tyexp, binded, ctx
      | Error r -> raise @@
        Expr_error ((Incompatible_types (tyexp, array_ty)), Some r, loc)
    end

  | Tpat_lazy p ->
    let tyval = match Typecheck_types.safe_expand_abbrev_max ctx tyexp with
        { desc = Tconstr (p, [tyval], _); }
        when snd @@ PathEq.eq ctx.paths p Predef.path_lazy_t -> tyval
      | _ -> raise_error loc @@ Pattern_type_clash ("lazy", tyexp) in
    let ty, binded, ctx =  type_pattern' ctx binded p tyval in
    let lazy_ty = (Predef.type_lazy_t ty) in
    begin
      match Typecheck_typing.eq ctx lazy_ty tyexp with
        Ok ctx -> tyexp, binded, ctx
      | Error r -> raise @@
        Expr_error ((Incompatible_types (tyexp, lazy_ty)), Some r, loc)
    end

and type_field_pattern ctx binded (lid, desc, pat) _ =
  print_debug "type_field_pattern";
  let loc = pat.pat_loc in
  if desc.lbl_repres = Record_float then
    check loc ctx desc.lbl_arg Predef.type_float;
  let ty, binded, ctx = type_pattern' ctx binded pat desc.lbl_arg in
  let desc' = Env.lookup_label lid.Asttypes.txt ctx.env in
  let vars, ty_arg, ty_res = instance_label false desc in
  let vars_exp, tyexp_arg, tyexp_res = instance_label false desc' in
  check loc ctx ty_res tyexp_res;
  check loc ctx ty_arg tyexp_arg;
  check loc ctx ty tyexp_arg;
  { desc with lbl_res = ty_res; lbl_arg = ty_arg }, binded, ctx

let type_pattern env p =
  type_pattern' (Typecheck_types.create_context env) SMap.empty p p.pat_type

let type_self_pattern cl_num (cl_env: class_env) p =
  let ty, binded, ctx = type_pattern' cl_env.ctx SMap.empty p p.pat_type in
  let meths = ref Meths.empty in
  let vars = ref Vars.empty in
  let cl_env = SMap.fold (fun n (ty, id, _) cl_env ->
      print_debug (
        Format.asprintf "self_pat, val: %a" Printtyp.ident id);
      let valdesc = { val_type = ty;
                      val_kind = Val_unbound;
                      val_attributes = [];
                      Types.val_loc = p.pat_loc; } in
      { cl_env with
        val_env = Env.add_value id valdesc cl_env.val_env;
        meth_env = Env.add_value id
            { valdesc with val_kind = Val_self (meths, vars, cl_num, ty) }
            cl_env.meth_env;
        par_env = Env.add_value id
            { valdesc with val_loc = Location.none } (* copy *)
            cl_env.par_env;
      }) binded cl_env in
  ty, { cl_env with meths; vars }

let type_class_arg_pattern cl_num cl_env lab p =
  let ty, binded, ctx = type_pattern' cl_env.ctx SMap.empty p p.pat_type in
  print_debug
    (Format.asprintf "type_class_arg_pattern \n\
                      typat: %a\n\
                      ty_found: %a"
       Printtyp.raw_type_expr p.pat_type
       Printtyp.raw_type_expr ty);
  let ty = Typecheck_typing.apply_subst ty cl_env.substs in
  if is_optional lab then
    (match Typecheck_typing.instance
            ctx ty (type_option (newvar ())) TyMap.empty with
      Ok _ -> ()
    | Error _ -> failwith "Should be an option");
  let cl_env = SMap.fold (fun n (ty, id, _) ctx ->
      let vd = { val_type = ty;
                 val_kind = Val_ivar (Asttypes.Immutable, cl_num);
                 val_attributes = [];
                 Types.val_loc = p.pat_loc } in
      let cl_env = { cl_env with
                     meth_env = Env.add_value id vd cl_env.meth_env } in
      cl_env) binded cl_env in
  ty, binded, { cl_env with val_env = add_pattern_variables cl_env.val_env binded }


let rec type_expr_aux ctx expr ty_exp =
  let dbmode = debug_mode expr.exp_attributes in
  print_debug (Format.asprintf"type_expr: %a\n\
                                       expected ty: %a"
                         Typecheck_pretty.expression expr
                         Printtyp.type_expr ty_exp);
  (* env' is the result of adding some extras into the environment, which are
     either :
     - an opening
     - a locally abstract type
  *)
  (* exp_type : type infered
     ty : type resulting from type checking of the expression
     env |- expr : ty && unifiable ty exp_ty
     ==> env |- expr : expr_ty
  *)
  let ty, ctx' = type_extra ctx expr.exp_loc expr.exp_extra expr ty_exp in
  (* the resulting type must be refined using the following extras if available:
     - a coercion
     - a constraint
     - a constraint to verify that the method is polymorphic
  *)
  print_debug (Format.asprintf
                         "Expression typed with type: %a. Retained in typedtree: %a"
                         Printtyp.raw_type_expr ty Printtyp.raw_type_expr expr.exp_type);
  (* A property of the typedtree is the following:
     If the node describe a value that has type "'a -> 'a", and used in the
     context where it is instantiated with the type "int -> int", then the type
     retained by the node is the instantiated one. As a result, the type of the
     expression and the englobing node might not be the same.
  *)
  print_debug "WELLFORMED: tychecked";
  begin
    match wellformed_type ctx ty with
      Ok () -> ()
    | Error r ->
      raise_error ~reason:(Some r) expr.exp_loc @@ Illformed_type (ty, Checked)
  end;
  print_debug "WELLFORMED: infered type";
  begin
    match wellformed_type ctx expr.exp_type with
      Ok () -> ()
    | Error r ->
      raise_error ~reason:(Some r) expr.exp_loc @@ Illformed_type (ty, Infered)
  end;
  print_debug (Format.asprintf "EXPRESSION: type wellformed\n%a"
                       Typecheck_pretty.expression expr);
  check_instance expr.exp_loc ctx expr.exp_type ty;
  print_debug "BOTH TYPES ARE EQUIVALENT";
  (* if not @@ Typecheck_typing.eq env ty expr.exp_type then *)
  (*   if not @@ Typecheck_typing.instance env expr.exp_type ty *)
  (*   then raise (Expr_error (Incompatible_types (expr.exp_type, ty))); *)
  print_debug (Format.asprintf "end of:\n  type_expr: %a"
                         Typecheck_pretty.expression expr);
  dbmode ();
  ty_exp, ctx

and type_extra (ctx : context) loc extras expr tyexp =
  match extras with
  | [] -> type_expr_desc ctx loc expr.exp_desc tyexp
  | (Texp_open (fl, path, lid, e), _, _) :: l ->
    let ctx = !type_open fl ctx path in
    type_extra ctx loc l expr tyexp
  | (Texp_newtype name, _, _) :: l ->
    let id =
      (fst @@ Env.lookup_type (Longident.Lident name) expr.exp_env)
      |> Path.head in
    let _, new_env, finalize =
      Typecheck_typexpr.generate_abstract_type ctx.env name id in
    let tyexpr, _ = type_extra {ctx with env = new_env} loc l expr tyexp in
    print_debug (
      Format.asprintf "Type of the expression newtyped: %a\nregistered: %a"
        Printtyp.raw_type_expr tyexpr
        Printtyp.raw_type_expr tyexp);
    let tyexpr_final = finalize ctx.env tyexpr in
    tyexpr_final, ctx

  | (Texp_constraint cty, _, _) :: l ->
    print_debug
      (Format.asprintf "Constraint: %a" Printtyp.type_expr cty.ctyp_type);
    begin_def ();
    let vars, gen = !(Variables.curr_vars) in
    let ty_cstr, _ =
      Typecheck_typexpr.transl_ctype_aux
        ctx vars Typecheck_typexpr.Extensible gen cty in
    end_def ();
    (* For Polytype: generate an abstract type for each Univar *)
    (* let ty_exp, expr, env, finalizers = match (repr ty_cstr).desc with *)
    (*     Tpoly (ty, vars) -> *)
    (*     let vars' = List.fold_left (fun (vars', env, finalizers) -> *)
    (*       ) ([], env, []) vars in *)

    (* in *)
    let ty_expect =
      try
        less_gen loc ctx.env ty_cstr tyexp
      with _ -> raise_error loc @@
        Constraint_not_applicable (ty_cstr, tyexp) in
    print_debug "Determining the expected type";
    let ty_expr, _ = type_extra ctx loc l expr ty_expect in
    ty_expr, ctx
  | (Texp_coerce (ct1_opt, ct2), _, _) :: l ->
    (* let *)
    assert false
  | (Texp_poly cty, _, _) :: l ->
    print_debug
      (Format.asprintf "Texp_poly");
    begin_def ();
    let ty =
      match cty with
        None -> tyexp
      | Some cty -> Typecheck_typexpr.transl_ctype ctx cty
    in
    print_debug
      (Format.asprintf "poly_type: %a" Printtyp.raw_type_expr ty);
    end_def ();
    generalize_structure ty;
    let ctx =
      if cty <> None then
        match Typecheck_typing.eq ctx ty tyexp with
          Ok ctx -> ctx
        | Error r ->
          raise_error ~reason:(Some r) loc @@ Incompatible_types (ty, tyexp)
      else ctx
    in
    print_debug "Texp_poly: after eq";
    let exp =
      match (expand_head ctx.env ty).desc with
        Tpoly (ty', _) ->
        print_debug "First case";
        let ty', ctx  = type_extra ctx loc l expr ty' in
        ty, ctx
      (* | Tpoly (ty', tl) -> *)
      (*   (\* begin_def (); *\) *)
      (*   (\* let vars, ty'' = instance_poly true tl ty' in *\) *)
      (*   (\* end_def (); *\) *)
      (*   (\* generalize_structure ty''; *\) *)
      (*   let ty_expr, ctx = type_extra ctx loc l expr ty'' in *)
      (*   (\* end_def (); *\) *)
      (*   (\* check_univars ctx.env false "method" expr tyexp vars; *\) *)
      (*   ty_expr, ctx *)
      | _ -> assert false in
    exp

and type_expr_desc ctx loc desc tyexp =
  print_debug "type_expr_desc";
  match desc with
    Texp_ident (path, _, valdesc) ->
    (* path in env && ty := env(path) == valdesc.val_type
       ==> path : ty *)
    let v = try find_value path ctx.env
      with Not_found -> raise_error loc @@ Unbound_variable path in
    print_debug
      (Format.asprintf "texp_ident: (%a) value: %a"
         Typecheck_pretty.path path
         (Printtyp.value_description (Ident.create "#none")) v);
    print_debug
      (Format.asprintf "required_globals: %a"
         (fun fmt ids -> List.iter
             (Format.fprintf fmt "%a, " Typecheck_pretty.ident) ids)
         (Env.get_required_globals ()));

    (* let ty1 = v.val_type in *)
    let ty2 = valdesc.val_type in
    print_debug "First unify ?";
    (* check loc ctx ty1 ty2; *)

    (* If the value is polymorphic, the type retained by the node in the
       typedtree has already been instantiated: the instantiation is implicit.
       As a result, we cannot verify the retained type is equal to the the value
       description type *)
    (* print_debug @@ Format.asprintf "Second check ? typexp: %a" *)
    (*   Printtyp.type_expr tyexp; *)
    (* check env (instance env tyexp) ty1; *)
    begin
      match Typecheck_typing.instance ctx tyexp ty2 TyMap.empty with
        Ok _ -> ()
      | Error r ->
        raise_error ~reason:(Some r) loc @@
        Incompatible_types (tyexp, ty2)
    end;
    print_debug (Format.asprintf "return tyexp:%a\n of ident:%a"
      Printtyp.raw_type_expr tyexp Typecheck_pretty.path path);
    tyexp, ctx
  | Texp_constant c ->
    print_debug "constant";
    (* c in builtins
       ==> c : type(c) *)
    let ty = Typecheck_typecore2.type_constant c in
    print_debug (
      Format.asprintf "check constnt type, %a vs %a"
        Printtyp.raw_type_expr ty Printtyp.raw_type_expr tyexp);
    check loc ctx ty tyexp;
    ty, ctx
  | Texp_let (recfl, values, expr) ->
    (* non_rec : \/x in values -> env |- xi : ti
       rec : \/x in values -> env, x0 : t0 .., xn : tn |- xi : ti
       && env, x0 : t0 .. xn : tn |- expr : ty
       ==> Texpr_let _ : ty *)
    let _, ctx' = type_let ctx values recfl in
    let ty, _ = type_expr_aux ctx' expr tyexp in
    ty, ctx
  | Texp_function (label, cases, partial_flag) ->
    (* without labels
       \/c in cases -> env |- ci : ti
       && \/ti, unifiable t(i-1) ti     (using type equations for non trivial
                                         unification, GADTs for example)
       ==> function _ : t0 *)
    type_function ctx loc label cases tyexp, ctx
  | Texp_apply (eapp, eargs) ->
    (* env |- eapp : t0 -> .. -> tn -> ty
       && \/e in eargs, env |- ei : ti'
       && \/ti,ti', unifiable ti ti
       -> instantiation of type variables in t(i+1) -> .. -> ty
       ==> apply : ty instantiated
    *)
    print_debug "Before tyfun";
    let ty_fun, _ = type_expr_aux ctx eapp eapp.exp_type in
    print_debug "Before tyapp";
    let tyapp = type_application ctx loc ty_fun eargs in
    print_debug "After tyapp";
    tyapp
  | Texp_match (expr, cases, exn_cases, partial_flag) ->
    (* env |- expr : ty1
       \/c in cs1, env |- ci : tyi1 -> tyi2
       \/ex in cs2, env |- ex : exn - tyi2'
       && \/tyi1, tyi2, tyi',
         unifiable tyi1 ty1 && unifiable ty(i-1)2 tyi2 && unifiable tyi2'
       ==> match _ : ty2 *)
    let tysc, _ = type_expr_aux ctx expr expr.exp_type in
    let ty_cases = type_cases ctx tysc tyexp cases in
    let ty_exn_cases = type_cases ctx Predef.type_exn tyexp exn_cases in
    check loc ctx ty_cases ty_exn_cases; (* Technically, already done by type_cases *)
    ty_cases, ctx
  | Texp_try (expr, cases) ->
    (* env |- expr : ty
       \/c in cases, env |- ci : exn -> tyi
       && \/tyi unifiable tyi ty
       ==> try-with _ : ty *)
    let ty_expr, _ = type_expr_aux ctx expr tyexp in
    let type_with = type_cases ctx Predef.type_exn ty_expr cases in
    type_with, ctx
  | Texp_tuple (exprs) ->
    (* \/e in exprs, env |- ei : tyi
       tuple : ty0 * .. * tyn *)
    let tys_exp =
      match Extract.extract_tuple_info ctx tyexp with
        Ok tys -> tys
      | Error e -> raise Typecheck_typing.(Typing_error (Types_error e, loc))
    in
    let tys = List.fold_left2 (fun tys e tyexp ->
        let ty, _ = type_expr_aux ctx e tyexp in
        ty :: tys) [] exprs tys_exp |> List.rev in
    check loc ctx tyexp @@ newty (Ttuple tys);
    tyexp, ctx
  | Texp_construct (lid, desc, args) -> (* Already disambiguated! *)
    (* lid in env => lid : env(lid) : t0 * .. * tn -> ty ('a0, .., 'am)
       \/e in args, env |- ei : ti' && check ti ti'
           if exists set('a) in tis => \/'b in set('a), ty' = ty ['bi\ti]
       constr : ty' (after unification and type instantiations) *)
    print_debug "Texp_construct";
    let ty_args, ty_res = instance_constructor desc in
    check_instance loc ctx tyexp ty_res;
    begin
      try
        let constrs = extract_constructors ctx.env desc in
        let constr = Longident.last lid.Asttypes.txt in
        ignore @@ List.find (fun cd -> Ident.name cd.cd_id = constr) constrs
      with Typecheck_utils.Cannot_extract_exttype_constructor -> ()
    end;
    (* TODO: verify that desc corresponds to cd, ie 3rd line of rule *)
    let ty = new_funtype ty_args ty_res in
    List.iteri (fun i ty -> print_debug (Format.asprintf "arg%d: %a"
                   i Printtyp.raw_type_expr ty)) ty_args;
    print_debug (Format.asprintf "generated_funtype: %a"
      Printtyp.raw_type_expr ty);
    let ty_res, ctx = type_application ctx loc ty
        (List.map (fun arg -> "", Some arg, Required) args) in
    print_debug (Format.asprintf "resulting construct type:\n%a"
      Printtyp.type_expr ty_res);
    (* List.iter2 (type_argument env) ty_args args; *)
    tyexp, ctx
  | Texp_variant (label, eopt) ->
    let tyexp_opt =
      match Extract.extract_variant_info ctx tyexp with
        Ok ({ row_fields; _ }) ->
        let f = List.find (fun (l, r) -> l = label) row_fields in
        begin match f with
            _, Rpresent tyopt -> tyopt
          | _ -> raise_error loc @@
            Tag_absent_in_variant (label, tyexp)
        end
      | Error e ->
        raise Typecheck_typing.(Typing_error(Types_error e, loc))in
    let _tyopt = match eopt, tyexp_opt with
        None, None -> None
      | Some e, Some ty -> Some (fst @@ type_expr_aux ctx e ty)
      | _ -> raise_error loc @@
        Variant_inconsistency tyexp in
    tyexp, ctx
  | Texp_record (fields, eopt) ->
    (* env |- eopt : ty if Some _ else 'a
       \/l in fields,
         env' |- (li: ei) : ti && l(i-1).ty_res = li.ty_res &&
         li in field (ty_res) && li.ty_args = ty_res.li.ld_type
       unifiable l0.ty_res ty
       ==> record : ty *)
    let ty_record = match eopt with
        None -> tyexp
      | Some e -> fst @@ type_expr_aux ctx e tyexp in
    let ty_record = List.fold_left (fun ty_record' (lid, ldesc, expr) ->
        let tyexpr, _ = type_expr_aux ctx expr expr.exp_type in
        check_instance loc ctx tyexpr ldesc.lbl_arg;
        check_instance loc ctx ty_record' ldesc.lbl_res;
        (* Next assert: Out_of_memory, too much to check *)
        (* assert (ldesc.lbl_all.(ldesc.lbl_pos) = ldesc); *)
        if not (ldesc.lbl_all.(ldesc.lbl_pos).lbl_name = ldesc.lbl_name) then
          raise_error loc @@ Typecheck_inconsistency
            "Label name is different in labels retained for disambiguation.";
        if not (ldesc.lbl_name = Longident.last lid.Asttypes.txt) then
          raise_error loc @@ Typecheck_inconsistency
            "Label in descriptor different from given label.";
        ty_record') ty_record fields in
    ty_record, ctx
  | Texp_field (expr, lid, ldesc) ->
    (* env |- expr : { ... } as tyrec
       lid in fields(tyrec)
       ldesc.ty_res = tyrec
       ==> field_expr : ldesc.ty_args
    *)
    let tyexpr, _ = type_expr_aux ctx expr expr.exp_type  in
    check_instance expr.exp_loc ctx tyexpr ldesc.lbl_res;
    if not (ldesc.lbl_all.(ldesc.lbl_pos).lbl_name = ldesc.lbl_name) then
      raise_error loc @@ Typecheck_inconsistency
        "Label name is different in labels retained for disambiguation.";
    if not (ldesc.lbl_name = Longident.last lid.Asttypes.txt) then
      raise_error loc @@ Typecheck_inconsistency
        "Label in descriptor different from given label.";
    ldesc.lbl_arg, ctx
  | Texp_setfield (expr, lid, ldesc, expr2) ->
    (* Same as previous + (-> ty_field)
       l_desc.lbl_mutable = true
       env |- expr2 : ty && unifiable ty ty_field
       ==> setfield : unit *)
    let _ = type_expr_aux ctx expr ldesc.lbl_res in
    if not (ldesc.lbl_all.(ldesc.lbl_pos).lbl_name = ldesc.lbl_name) then
      raise_error loc @@ Typecheck_inconsistency
        "Label name is different in labels retained for disambiguation.";
    if not (ldesc.lbl_name = Longident.last lid.Asttypes.txt) then
      raise_error loc @@ Typecheck_inconsistency
        "Label in descriptor different from given label.";
    if not (ldesc.lbl_mut = Asttypes.Mutable) then
      raise_error loc @@ Record_field_immutable;
    let tyarg, _ = type_expr_aux ctx expr2 expr2.exp_type in
    check expr2.exp_loc ctx tyarg ldesc.lbl_arg;
    Predef.type_unit, ctx
  | Texp_array exprs ->
    (* \/e in exprs, env |- ei : ti && unifiable t(i-1) ti
       ==> array : array t0
    *)
    let tyexp = List.hd @@ extract_constructor_types tyexp in
    let ty = List.fold_left (fun ty_res e ->
        fst @@ type_expr_aux ctx e ty_res) tyexp exprs in
    Predef.type_array ty, ctx
  | Texp_ifthenelse (cond, e1, e2opt) ->
    (* env |- cond : bool
       env |- e1 : t1
       env |- case :
                Some e -> env |- e : t2
                None -> (t2 = unit)
       unifiable t1 t2
       ==> if : t1
    *)
    let _ = type_expr_aux ctx cond Predef.type_bool in
    let tyif, _ = type_expr_aux ctx e1 tyexp in
    let tyelse, _ = match e2opt with
        None -> Predef.type_unit, ctx
      | Some e -> type_expr_aux ctx e tyexp in
    check loc ctx tyif tyelse;
    tyif, ctx
  | Texp_sequence (e1, e2) ->
    (* env |- e1 : unit
       env |- e2 : t
       ==> env |- e1; e2 : t *)
    let ty1, _ = type_expr_aux ctx e1 Predef.type_unit in
    let ty2, _ = type_expr_aux ctx e2 tyexp in
    (try check e1.exp_loc ctx ty1 (Predef.type_unit)
     with Expr_error (Incompatible_types (_, _), _, _) ->
       () (* Should issue a warning *));
    ty2, ctx
  | Texp_while (cond, e2) ->
    (* ctx |- cond : bool
       env |- e2 : unit
       == env |- while ... : unit *)
    let tycond, _ = type_expr_aux ctx cond cond.exp_type in
    check cond.exp_loc ctx tycond Predef.type_bool;
    let ty2, _ = type_expr_aux ctx e2 Predef.type_unit in
    (try check e2.exp_loc ctx ty2 (Predef.type_unit)
     with Expr_error (Incompatible_types (_, _), _, _) ->
       () (* Should issue a warning *));
    Predef.type_unit, ctx
  | Texp_for (id, pat, init, cond, dir, expr) ->
    (* env |- init : int
       env |- cond : int
       env, id : int |- expr : unit
       ==> for ... : unit
    *)
    let tyinit, _ = type_expr_aux ctx init Predef.type_int in
    let _ = type_expr_aux ctx cond Predef.type_int in
    let ctx' =
      { ctx with env =
                   Env.add_value id (create_value_desc tyinit []) ctx.env } in
    let tyexpr, _ = type_expr_aux ctx' expr Predef.type_unit in
    (try check expr.exp_loc ctx tyexpr (Predef.type_unit)
     with Expr_error (Incompatible_types (_, _), _, _) ->
       () (* Should issue a warning *));
    Predef.type_unit, ctx
  | Texp_assert { exp_desc = Texp_construct(_, {cstr_name="false"}, _) } ->
    (* ==> assert false : 'a *)
    tyexp, ctx
  | Texp_assert e ->
    (* env |- e : bool
       ==> assert e : unit *)
    let _ = type_expr_aux ctx e Predef.type_bool in
    Predef.type_unit, ctx
  | Texp_lazy e ->
    (* env |- e : t
       ==> env |- lazy e : t lazy *)
    let tyexp = List.hd @@ extract_constructor_types tyexp in
    let ty, _ = type_expr_aux ctx e tyexp in
    Predef.type_lazy_t ty, ctx
  | Texp_letmodule (id, _, md, e) ->
    (* We don't need to verify scoping: indeed, in an explicitly typed language,
       it is impossible to refer to types that are declared *inside* of the
       module but outside of it, before the "let module" binding. For example:
       "let f : unit -> M.t = fun () ->
          let module M : sig type t val x : t end=
            struct type t = int let x : t = 42 end in
          M.x"
       This kind of declaration is invalid, since M does not exists when
       checking the annotation. We can refer to it after the "in", but not
       before. It cannot escape outside the "let module ... in"
       As a result, the correct rule is:
       env |- modexpr : S
       env, M : S |- e : t
       ==> env |- let module M : S = modexpr in e : t
    *)
    let mty, ctx = type_module ctx md in
    print_debug (Format.asprintf
      "Module type infered: %a\n\
       module type generated: %a"
      Printtyp.modtype md.mod_type
      Printtyp.modtype mty);
    let ctx = { ctx with env = Env.add_module id mty ctx.env } in
    type_expr_aux ctx e tyexp
  | Texp_pack me ->
    let (p, lids, tys) =
      match Extract.extract_package_info ctx tyexp with
        Ok (p, lids, tys) -> (p, lids, tys)
      | Error e -> raise Typecheck_typing.(Typing_error (Types_error e, loc))
    in
    print_debug "Generating mty from package";
    let pack_mty =
      Typecheck_types.create_package_mty ctx.env (Mty_ident p) lids tys in
    print_debug
    (Format.asprintf "pack_type generated: %a; expected: %a"
      Printtyp.modtype pack_mty Printtyp.type_expr tyexp);
    let sg, ctx' = type_module ctx me in
    begin
      match Typecheck_typing.coercible_mty
              ctx
              sg pack_mty
              Typecheck_types.TyMap.empty with
        Ok _ -> tyexp, ctx
      | Error r -> raise_error ~reason:(Some r) loc @@
        Module_not_packable (sg, tyexp)
    end
  | Texp_send (obj, meth, None) ->
    (* value: Related to inheritance, is Some exp if obj is a superclass *)
    let ty_obj, ctx = type_expr_aux ctx obj obj.exp_type in
    let meth = match meth with
        Tmeth_val id -> Ident.name id
      | Tmeth_name s -> s in
    let ty_obj = match obj.exp_desc with
        Texp_ident (p, _, { val_kind = Val_self (meths, _, _, privty) }) ->
        privty
      | Texp_ident (_, _, { val_kind = Val_anc (_, _)}) ->
        assert false
      | _ -> ty_obj in
    let meth_ty =
      Extract.find_meth ctx obj.exp_loc meth Asttypes.Public ty_obj in
    let ty = match repr meth_ty with
      | { desc = Tpoly (ty, [])} -> Ctype.instance ctx.env ty
      | { desc = Tpoly (ty, tl)} ->
        instance_poly false tl ty |> snd
      | _ -> assert false (* Every methods are already resolved and available in
                             the object type. Otherwise, the inference should be
                             incorrect *)
    in
    ty, ctx
  | Texp_send (_, _, Some _) ->
    raise (Expr_error (Error_msg "Super case not managed.", None, loc))
  | Texp_new (p, lid, cd) ->
    let cl_decl = Env.find_class p ctx.env in
    begin
      match Typecheck_typing.instance_class_decl ctx cd cl_decl TyMap.empty with
      Error e -> raise (Typing_error (e, loc))
    | Ok ctx -> match cd.cty_new with
        None -> assert false
      | Some ty -> ty, ctx
    end
  | Texp_instvar (self, var, _) ->
    let desc = Env.find_value var ctx.env in
    begin
      match desc.val_kind with
        Val_ivar (_, cl_num) ->
        desc.val_type, ctx
      | _ -> raise_error loc @@ Unbound_instance_variable var
    end
  | Texp_setinstvar (self, var, _, expr) ->
    let desc = Env.find_value var ctx.env in
    begin
      match desc.val_kind with
        Val_ivar (Asttypes.Mutable, cl_num) ->
        let tye, ctx = type_expr_aux ctx expr expr.exp_type in
        check loc ctx tye desc.val_type;
        Predef.type_unit, ctx
      | Val_ivar (Asttypes.Immutable, _) ->
        raise_error loc @@ Immutable_instance_variable var
      | _ -> raise_error loc @@ Unbound_instance_variable var
    end
  | Texp_override (self, meths) ->
    assert false
  | Texp_object (desc, meths) ->
    let csig = !type_object ctx loc desc in
    csig.csig_self, ctx

and type_let ctx vbs recflag =
  print_debug "type_let";
  (*
     Adapted from Typecore.type_let's algorithm.
     We don't need inference, then it might reduce the burden of a first typing
     approximation in case of of recursive bindings. Moreover, there is no level
     to take care of.

     vbs is a list of pattern * expr, where the pattern declares the variables
     binded.
     Each pattern is already annotated, then we need to type-check the pattern
     with its annotation. In case of recursive bindings, every variable+type is
     added to the environment. Otherwise, they are added right after the
     typing of the expression.
     Then type_expr, then try to check the type of the pattern with the type of
     the expression.

     More or less:
     * if not rec
     \/p, e in vbs
    match Typemod.type_structure
       let currenv = env, p0 : t0, .., p(i-1) : t(i-1) in
       currenv |- pi : ti && currenv |- ei : ti' && check ti ti'
       ==> env |- p0 = e0 : t0 .. pn = en : tn

     * else
       let currenv = env, p0 : annot_t0 .. pn : annot_tn in
       currenv |- pi : ti && currenv |- ei : ti' && check ti ti'
       ==> env |- p0 = e0 : t0 .. pn = en : tn

     where annot_ti is the annotated type for the pattern, and ti the type
     "infered", i.e. resulting of the type checking of the expected type against
     the annotated type.
  *)

  (* ======= IMPLEMENTATION ===== *)


  (* We split patterns and expressions into two separate lists *)
  let pats, exprs, attrs, locs =
    List.map
      (fun {vb_pat = p; vb_expr = e; vb_attributes = a; vb_loc = l } ->
         p, e, a, l) vbs
    |> split4 in

  (* Patterns are typed, and the binded variables recovered *)
  let ty_pats, binded =
    List.fold_left2 (fun (tys, binded) p a ->
        let dbmode = debug_mode a in
        let ty, b, ctx =
          type_pattern' ctx binded p (p.pat_type) in
        dbmode();
        ty :: tys, b) ([], SMap.empty) pats attrs in
  let ty_pats = List.rev ty_pats in

  (* Every binded variable is added into the environment in case of recursive
     bindings *)
  let old_ctx = ctx in
  let new_ctx = { ctx with env = pattern_bindings true ctx.env binded } in
  let ctx = if recflag = Asttypes.Recursive then new_ctx else ctx in

  (* Type each expression and checks it against the pattern type *)

  let tys = fold_left3 (fun typed expr pat att ->
      let dbmode = debug_mode att in
      let ty_expr = fst @@ type_expr_aux ctx expr pat in
        (* match (repr pat).desc with *)
        (* (\* if the pattern is polymorphic *\) *)
        (* | Tpoly (ty, tl) -> *)
        (*   print_debug "!!! is Tpoly !!!"; *)

        (*   let vars, _ = instance_poly ~keep_names:true true tl ty in *)
        (*   let ty_expr, _ = type_expr_aux ctx expr pat in *)
        (*   print_debug "Correctly typed with polymorphic ty"; *)
        (*   (\* check expr.exp_loc ctx ty_expr ty'; *\) *)

        (*   pat *)
        (* | _-> print_debug "!!! not Poly !!!"; *)
        (*   fst @@ type_expr_aux ctx expr pat in *)
      dbmode ();
      (pat, ty_expr) :: typed
    ) [] exprs ty_pats attrs in
  let tys = List.rev tys in

  iter3 (fun (pat, tyexpr) expr loc ->
      print_debug
        (Format.asprintf "Resulting type:\n%a \n=\n%a"
           Printtyp.raw_type_expr pat Printtyp.raw_type_expr tyexpr);
      check_instance loc ctx tyexpr pat;
      if Typecore.is_nonexpansive expr then
        begin
          print_debug (
            Format.asprintf "is non_expeansive: \n%a\n%!"
              Typecheck_pretty.expression expr);
          Typecheck_typing.check_gen ctx loc true pat
        end
      else
        (
          print_debug (
            Format.asprintf "is expansive\n%a\n%!"
              Typecheck_pretty.expression expr);
          Typecheck_typing.check_gen ctx loc false pat)
    ) tys exprs locs;


  let final_env =
    SMap.fold (fun k (ty, id, _) env ->
        let ty = match ty.desc with
            Tpoly (ty, tl) ->
            (* Avoids values with the type ['a0 'an. t] *)
            begin_def ();
            let _, ty =
              Typecheck_ctype.instance_poly ~keep_names:true true tl ty in
            end_def ();
            generalize ty;
            ty
          | _ -> ty in
        Env.add_value id (create_value_desc ty []) env) binded old_ctx.env in

  SMap.fold (fun k (ty, id, order) typed ->
      (* generalize ty; *)
      let vd = Env.find_value (Path.Pident id) final_env in
      print_debug (Format.asprintf "value_desc: %a"
                             (Printtyp.value_description id) vd);
      (id, vd, order) :: typed)
    binded [] |>
  List.sort (fun (_, _, order) (_, _, order') ->
      compare order order'), { ctx with env = final_env }



and type_bindings ctx vbs flag =
  (* should type each binding, and return its value description + id + order of
     binding (not really relevant since idents can be sorted by their binding
     time, only for debug) *)
  Typetexp.reset_type_variables();
  type_let ctx vbs flag

and type_cases ctx ty_arg ty_res cases =
  print_debug "in type cases";
  let tyres = List.fold_left (fun ty case ->
      let typat, binded, ctx =
        type_pattern' ctx SMap.empty case.c_lhs ty_arg in
      (* check env ty_arg typat; *)
      let vars = SMap.fold (fun _ (ty, _, _) vars ->
          let tys = Typecheck_types.extract_vars_list [] ty in
          List.fold_left (fun vars ty -> TySet.add ty vars) vars tys)
          binded ctx.generalized_vars in
      let ctx' =
        { ctx with env = pattern_bindings true ctx.env binded;
                   generalized_vars = vars
        } in
      begin
        match case.c_guard with
          None -> ()
        | Some e ->
          ignore @@ type_expr_aux ctx' e Predef.type_bool
      end;
      (* print_debug "search_a"; *)
      (* search_a ctx'.env; *)
      print_debug
        (Format.asprintf "Ambivalents: %a"
           (fun fmt ->
              TyMap.iter (fun k v -> Format.fprintf fmt "[%a: %d]; "
                             Printtyp.type_expr k v.uniq)) ctx'.ambivalents);
      print_debug
        (Format.asprintf "Pattern typed with type: %a. in gadt: %b"
           Printtyp.type_expr typat ctx'.gadt);
      let tyexpr, ctx = type_expr_aux ctx' case.c_rhs ty in
      print_debug (Format.asprintf "ty_pat = %a, ty_res = %a, ty_expr = %a"
                             Printtyp.type_expr typat
                             Printtyp.type_expr tyexpr
                          Printtyp.type_expr case.c_rhs.exp_type);
      print_debug
        (Format.asprintf "Ambivalents after: %a"
           (fun fmt ->
              TyMap.iter (fun k v -> Format.fprintf fmt "[%a]; "
                             Printtyp.type_expr k)) ctx'.ambivalents);
      tyexpr)
      ty_res cases in
  print_debug (Format.asprintf "type_cases:\n\
                                        tyres= %a"
                         Printtyp.raw_type_expr tyres);
  tyres

and type_function ctx loc label cases tyexp =
  print_debug "type_function-begin:";
  print_debug
    (Format.asprintf "tyexp: %a" Printtyp.raw_type_expr tyexp);

  let ty_arg, ty_res_exp =
    let t = match repr tyexp with
        { desc = Tpoly (t, v); _ } -> t | t -> t in
    match Extract.extract_arrow_info ctx t with
      Ok (l, ty, ty') when l = label -> ty, ty'
    | Ok _ -> failwith "label mismatch"
    | Error e ->
      raise Typecheck_typing.(Typing_error (Types_error e, loc))
  in
  print_debug "functional type";
  if is_optional label then
    begin
      let tv = newvar() in
      match Typecheck_typing.instance
              ctx ty_arg (Predef.type_option tv) TyMap.empty with
        Ok _ -> ()
      | Error _ -> assert false
    end;
  let _ty_res = type_cases ctx ty_arg ty_res_exp cases in
  print_debug "type_function-end:";
  tyexp

(* for now, we suppose no labels (and obviously no optional argument) *)
and type_application ctx loc ty_fun args =
  let open Typecheck_types in
  let (ty_res, subst, ctx, _) = List.fold_left
      (fun (ty_res, subst, ctx, loc) (l, eopt, opt) ->
         let arg = match eopt with
             Some e -> e
           | None -> assert false in
         let ty_arg, ty_res =
           match Extract.extract_arrow_info ctx ty_res with
             Ok (lab, ty, ty') when lab = l -> ty, ty'
           | Ok _ -> failwith "Label mismatch"
           | Error r ->
             raise_error ~reason:(Some (Typecheck_typing.Types_error r)) loc @@
             Not_a_function ty_res in
         let ty_arg', subst = type_argument ctx ty_arg arg subst in
         match subst with
           Error r -> raise_error ~reason:(Some r) loc @@
           Incompatible_types (ty_arg', ty_arg)
         | Ok (subst, ctx) -> ty_res, subst, ctx,
      Location.({ loc with loc_end = arg.exp_loc.loc_end }))
      (ty_fun, Typecheck_types.TyMap.empty, ctx, loc)
      args in
  Typecheck_typing.apply_subst ty_res subst, ctx

and type_argument (ctx : Typecheck_types.context) ty_exp arg subst =
  let open Typecheck_types in
  print_debug
    (Format.asprintf "type_argument: arg:%a, ty_exp: %a"
       Typecheck_pretty.expression arg
       Printtyp.raw_type_expr ty_exp);
  let ty_arg, _ = type_expr_aux ctx arg arg.exp_type in
  ty_arg, Typecheck_typing.instance ctx ty_arg ty_exp subst


and type_top_expr ctx e =
  Typetexp.reset_type_variables();
  begin_def();
  let ty, _ = type_expr_aux ctx e e.exp_type in
  end_def();
  if Typecore.is_nonexpansive e then generalize ty
  else generalize_expansive ctx.env ty;
  ty

let print_error fmt = function
    Incompatible_types (ty1, ty2) ->
    Format.fprintf fmt "Incompatible types:\n%a\n&&\n%a\n%!"
      Printtyp.type_expr ty1 Printtyp.type_expr ty2
  | Illformed_type (ty, pass) ->
    let pass = match pass with Infered -> "infered"  | Checked -> "checked" in
    Format.fprintf fmt "The type %s of this expression is illformed:\n%a."
      pass Printtyp.type_expr ty
  | Pattern_package_expected ty ->
    Format.fprintf fmt
      "This patterns describes a package, but is expected to have pattern:\n%a"
      Printtyp.type_expr ty
  | Pattern_already_bound_var _ ->
    Format.fprintf fmt "This variable is already binded in the current pattern."
  | Pattern_type_clash (exp, ty) ->
    Format.fprintf fmt
      "This pattern describes a %s type, but is expected to have type:\n%a."
      exp Printtyp.type_expr ty
  | Pattern_unexpected_variant (lab, ty) ->
    Format.fprintf fmt
      "This variant tag `%s is expected to be absent in type:\n%a."
      lab Printtyp.type_expr ty(* declared absent in type *)
  | Pattern_unexpected_variant_type (lab, ty) ->
    Format.fprintf fmt
      "The variant tag `%s has a different type in the expected type:\n%a."
      lab Printtyp.type_expr ty
  | Pattern_or_unbound_variable s ->
    Format.fprintf fmt
      "Variable %s is not bound in eahc branch of this or-pattern." s
  | Pattern_or_variable_clash (s, tyexp, ty) ->
    Format.fprintf fmt
      "Variable %s has type %a in other branches of this or-pattern, \
       while it has type %a in currently typed."
      s Printtyp.type_expr tyexp Printtyp.type_expr ty
  | Pattern_or_ident_clash (id1, id2) ->
    Format.fprintf fmt
      "Idents for the same variable are different in this or-pattern."
  | Unbound_variable v ->
    Format.fprintf fmt
      "Unbound variable %a." Printtyp.path v
  | Type_unexpected (exp, ty) ->
    Format.fprintf fmt
      "This expression has the form of a %s type,\n\
       but is expected have type:\n%a."
      exp Printtyp.type_expr ty
  | Tag_absent_in_variant (lab, ty) ->
    Format.fprintf fmt
      "The label `%s is declared absent in the expected type %a."
      lab Printtyp.type_expr ty
  | Variant_inconsistency ty ->
    Format.fprintf fmt
      "This variant is inconsistent, it does not have the same type in the\
       variant type:\n%a"
      Printtyp.type_expr ty
  | Record_field_immutable ->
    Format.fprintf fmt "This record field is immutable."
  | Typecheck_inconsistency msg ->
    Format.fprintf fmt "%s" msg
  | Module_not_packable (mty, ty) ->
    Format.fprintf fmt "This module has type\n%a\n\
                        It cannot be packed by the expected type\n%a."
      Printtyp.modtype mty Printtyp.type_expr ty
  | Not_a_function ty ->
    Format.fprintf fmt
      "This expression cannot be applied, it is not a function. \
       It has type:\n%a."
      Printtyp.type_expr ty
  | Not_in_a_class ->
      Format.fprintf fmt
        "This expression is only valid in the body of a class."
  | Immutable_instance_variable i ->
    Format.fprintf fmt "The instance variable %a is not mutable."
      Printtyp.path i
  | Unbound_instance_variable i ->
    Format.fprintf fmt "The instance variable %a is unbound." Printtyp.path i
  | Constraint_not_applicable (ty, ty') ->
    Format.fprintf fmt "The type\n%a\ndoes not match the constraint\n%a."
      Printtyp.type_expr ty' Printtyp.type_expr ty
  | Error_msg msg ->
    Format.fprintf fmt "%s" msg

let print_error fmt (e, r, loc) =
  let print_reason fmt = function
      Some e -> Format.fprintf fmt "%a\n" Typecheck_typing.print_error_desc e
    | None -> () in
  Format.fprintf fmt "%a\n%a\n%a"
    Location.print_loc loc
    print_error e
    print_reason r
