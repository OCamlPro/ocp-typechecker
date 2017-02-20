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
open Typedtree
open Types
open Printtyp
open Format

let full = ref false

let wrap_full f fmt v =
  if !full then f fmt v
  else ()

let type_scheme = raw_type_expr
let type_expr = raw_type_expr
let constant = Pprintast.default#constant
let rec_flag = Pprintast.default#rec_flag
let longident = Pprintast.default#longident
let ident fmt i = fprintf fmt "%s(*/%d*)" i.Ident.name i.Ident.stamp
let rec path fmt =
  let open Path in
  function
    Pident i -> ident fmt i
  | Pdot (t, s, _) -> fprintf fmt "%a.%s" path t s
  | Papply (p1, p2) -> fprintf fmt "%a %a" path p1 path p2

let optional fmt = function
    Required -> ()
  | Optional -> Format.fprintf fmt "(* optional *)"

let partial fmt = function
    Partial -> Format.fprintf fmt "(* partial app *)"
  | Total ->  ()

let override fmt = function
    Override -> Format.fprintf fmt "overrides"
  | Fresh ->  fprintf fmt "no overriding"

let closed_flag fmt = function
    Closed -> ()
  | Open -> fprintf fmt ".."

let mutable_flag fmt = function
    Mutable -> fprintf fmt "mutable "
  | Immutable -> ()

let private_flag fmt = function
    Public -> ()
  | Private -> fprintf fmt " private "

let variance fmt = function
    Covariant -> fprintf fmt "+"
  | Contravariant -> fprintf fmt "-"
  | Invariant -> ()

let rec pattern fmt p =
  fprintf fmt "@[<hv 2>(%a (*:@, %a*))%a@]"
    pattern_desc p.pat_desc
    (wrap_full type_expr) p.pat_type
    (wrap_full attributes) p.pat_attributes

and pattern_desc fmt = function
    Tpat_any -> Format.fprintf fmt "_"
  | Tpat_var (id, str) ->
    fprintf fmt "%a" ident id
  | Tpat_alias (pat, id, str) ->
    fprintf fmt "(%a as %a)"
      pattern pat
      ident id
  | Tpat_constant c ->
    fprintf fmt "%a" constant c
  | Tpat_tuple pats ->
    fprintf fmt "(%a)" (pattern_list ", ") pats
  | Tpat_construct (lid, cons_desc, pats) ->
    fprintf fmt "%a %a"
      longident lid.txt
      (pattern_list' ", ") pats
  | Tpat_variant (l, p_opt, r_desc_ref) ->
    fprintf fmt "`%s %a"
      l
      pattern_opt p_opt
  | Tpat_record (labels, flag) ->
      fprintf fmt "{ %a }"
      label_patterns labels
  | Tpat_array pats ->
    fprintf fmt "[| %a|]" (pattern_list "; ") pats
  | Tpat_or (p1, p2, row_desc_opt) ->
    fprintf fmt "%a @,| %a" pattern p1 pattern p2
  | Tpat_lazy p ->
    fprintf fmt "lazy %a" pattern p

and pattern_opt fmt = function
    None -> ()
  | Some p -> pattern fmt p

and pattern_list sep fmt pats =
  if List.length pats <> 0 then
    (pattern fmt (List.hd pats);
     List.iter (fun p ->
         Format.fprintf fmt "%s%a" sep pattern p) @@ List.tl pats)

and pattern_list' sep fmt pats =
  if List.length pats <> 0 then
    fprintf fmt "(%a)" (pattern_list sep) pats

and label_patterns fmt labels =
  List.iter (fun (lid, _, p) ->
      fprintf fmt "@[<hv 2>%a =@, %a; @]"
        longident lid.txt
        pattern p) labels

and expression fmt exp =
  Format.fprintf fmt "@[<hv 2>(%a : @,%a)@,%a\n@,(expr_%a)@]"
    expression_desc exp.exp_desc
    (wrap_full type_scheme) exp.exp_type
    (wrap_full extras) exp.exp_extra
    (wrap_full attributes) exp.exp_attributes

and expression_desc fmt = function
    Texp_ident (p, l, v_desc) ->
    Format.fprintf fmt "%a (* %a *)"
      path p
      (wrap_full (Printtyp.value_description (Path.head p))) v_desc
  | Texp_constant c ->
    Format.fprintf fmt "%a"
      constant c

  (* let rec? x1 = e1 ... and xn = en in expr, where
     vals = [(x1, e1); ..; (xn, en)]  *)
  | Texp_let (flag, vals, expr) ->
    Format.fprintf fmt "let %a %a in@, %a"
      rec_flag flag
      value_bindings vals
      expression expr

  (* Function declaration and application Note: "fun x ->" and "function x ->"
     are the same, "fun" only binds one pattern (including variable binding)
     whereas "function" deals with pattern-matching (that can be variable
     binding) *)
  | Texp_function (l, c, p_flag) ->
    fprintf fmt "function %a%a%a"
      label l cases c (wrap_full partial) p_flag
  (* expr [e1 .. en]: arguments aren't applied one by one as in naive
     implementations (i.e. ((expr e1) ...) en) *)
  | Texp_apply (eapp, eargs) ->
    fprintf fmt "%a %a"
      expression eapp
      apply_args eargs

  (* Pattern matching, constructors *)
  | Texp_match (expr, cs1, cs2, p_flag) ->
    fprintf fmt "match %a with %a\n@[<hv 2>%a@]\n(* %a *)\n"
      expression expr (wrap_full partial) p_flag
      cases cs1 cases cs2
  | Texp_try (expr, cs) ->
    fprintf fmt "try\n %a\n with\ %a"
      expression expr
      cases cs
  | Texp_tuple exprs ->
    fprintf fmt "(%a)"
      (expressions ", ") exprs
  | Texp_construct (lid, _, exprs) ->
    fprintf fmt "%a (%a)"
      longident lid.txt
      (expressions_par ", ") exprs

  (* Polymorphic variants only accepts one argument, i.e `Foo (1,2) -> (1,2) is
     a tuple, while Foo (1,2) -> Foo can be a constructor that takes 2
     arguments. Allows efficient compilation of variants (allocates only 1
     pointer). *)
  | Texp_variant (label, eopt) ->
    fprintf fmt "`%s %a"
      label (expression_opt ()) eopt

  (* Records *)
  | Texp_record (field, ext) ->
    record_args fmt field ext
  | Texp_field (expr, lid, l_desc) ->
    fprintf fmt "%a.%a"
      expression expr longident lid.txt
  | Texp_setfield (e1, lid, l_desc, e2) ->
    fprintf fmt "%a.%a <- %a"
      expression e1 longident lid.txt expression e2

  (* Arrays
     Note: <ar>.(<cst>) <- <expr> is a syntactic sugar for
           Array!.set <id> <cst> <expr> *)
  | Texp_array exprs ->
    fprintf fmt "[| %a |]"
      (expressions "; ") exprs

  | Texp_ifthenelse (cond, e1, e2opt) ->
    fprintf fmt "if %a then %a%a"
      expression cond expression e1
      (expression_opt ~prefix:" else " ()) e2opt

  (* Imperative features *)
  | Texp_sequence (e1, e2) ->
    fprintf fmt "%a;\n%a"
      expression e1 expression e2
  | Texp_while (e1, e2) ->
    fprintf fmt "while %a do\n%a\ndone"
      expression e1 expression e2
  | Texp_for (id, pat, init, cond, dir, expr) ->
    fprintf fmt "for %a = %a to %a do (* %a *) \n %a \n done"
      ident id
      expression init
      expression cond
      (wrap_full Pprintast.pattern) pat
      expression expr

  (* Objects *)
  | Texp_object (cl_str, sl) -> (* Direct object *)
    fprintf fmt "object\n%a\nend"
      class_structure cl_str
  | Texp_send (obj, m, expr) ->
    fprintf fmt "%a#%a%a"
      expression obj
      meth m
      (expression_opt ()) expr
  | Texp_new (p, lid, cl_decl) ->
    fprintf fmt "new %a (* %a, \"cl_decl\" *)"
      path p (wrap_full longident) lid.txt
  | Texp_instvar (self_path, p, s) ->
    (* Instance variable for objects. Generated from a Pexp_ident whose
       value_kind is Val_ivar. Only happens in the scope of the object, it is
       morally equivalent to "self#s"
    *)
    fprintf fmt "{typedtree {Texp_instvar (%a, %a, %s)}}"
      path self_path path p s.txt
  | Texp_setinstvar (self_path, p, s, expr) ->
    fprintf fmt "%s <- %a (* self: %a, p: %a *)"
      s.txt expression expr path self_path path p
  | Texp_override (self_path, l) -> (* Functional object: copy *)
    fprintf fmt "{< %a >} (* self_path: %a *)"
      (fun fmt -> List.iter (fun (p, s, expr) ->
           fprintf fmt "%s = %a; (* path: %a *)\n"
             s.txt expression expr path p)) l path self_path

  | Texp_letmodule (id, s, mod_expr, expr) ->
    fprintf fmt "let module %a = %a in\n%a"
      ident id
      module_expression mod_expr
      expression expr
  | Texp_pack mod_expr ->
    fprintf fmt "(module %a)"
      module_expression mod_expr


  | Texp_assert e ->
    fprintf fmt "assert %a" expression e
  | Texp_lazy e ->
    fprintf fmt "lazy %a" expression e

and expression_opt ?(prefix="") ?(suffix="") () fmt = function
    None -> ()
  | Some e -> fprintf fmt "%s%a%s"
                prefix expression e suffix

and expressions sep fmt exprs =
  if List.length exprs <> 0 then
    (expression fmt @@ List.hd exprs;
     List.iter (fun e ->
         fprintf fmt "%s%a" sep expression e)
       (List.tl exprs))

and expressions_par sep fmt exprs =
  if List.length exprs <> 0 then
    Format.fprintf fmt "(%a)" (expressions sep) exprs

and value_binding fmt v =
  Format.fprintf fmt "@[<2>%a = @, %a@] (vb_%a)"
    pattern v.vb_pat
    expression v.vb_expr
    (wrap_full attributes) v.vb_attributes

and value_bindings fmt vbs =
  value_binding fmt @@ List.hd vbs;
  List.iter (fun vb ->
      Format.fprintf fmt "@.and %a" value_binding vb)
    (List.tl vbs)

and label fmt = function
    "" -> ()
  | s when s.[0] = '?' -> fprintf fmt "%s:" s
  | s -> fprintf fmt "~%s:" s

and cases fmt c =
  if List.length c <> 0 then
    (case fmt @@ List.hd c;
     List.iter (fun c ->
         Format.fprintf fmt "@[<hv 2> | %a\n%!@]" case c) (List.tl c))

and case fmt c =
  fprintf fmt "%a%a -> @,%a"
    pattern c.c_lhs
    guard c.c_guard
    expression c.c_rhs

and guard fmt = function
    None -> ()
  | Some e -> fprintf fmt " when %a" expression e

and apply_args fmt args =
  List.iter (fun (l, eopt, opt) ->
      match l, eopt with
        "", Some e -> Format.fprintf fmt "%a %a"
                        expression e
                        optional opt
      | lab, None -> fprintf fmt "~%s %a" lab optional opt
      | lab, Some e -> fprintf fmt "~(%s=%a) %a"
                         lab expression e optional opt) args

and record_args fmt f = function
    None -> fprintf fmt "{ %a }" fields_decl f
  | Some e -> fprintf fmt "{ %a with\n %a }"
                expression e fields_decl f

and fields_decl fmt fs =
  List.iter (field_decl fmt) fs

and field_decl fmt (l, l_desc, expr) =
  fprintf fmt "%a = @,%a;"
    longident l.txt expression expr

and meth fmt = function
    Tmeth_name m -> fprintf fmt "%s" m
  | Tmeth_val i -> fprintf fmt "%a" ident i

and extras fmt exts =
  if List.length exts <> 0 then
    fprintf fmt "\n(* extras:\n %a *)" extras' exts

and extras' fmt exts =
  List.iter (fprintf fmt "%a\n" extra) exts

and extra fmt (ext, loc, attr) =
  fprintf fmt "@[%a, @extra_%a@]"
    extra_expr ext
    attributes attr

and extra_expr fmt = function
  (* Typing constraint added by the user:
     exp : ty
  *)
  | Texp_constraint ty ->
    fprintf fmt "constraint %a" core_type ty
  (* Coercion constraint:
     exp : tyopt :> ty
     exp :> ty
  *)
  | Texp_coerce  (tyopt, ty) ->
    fprintf fmt "coerce (%a, %a)"
      core_type_opt tyopt
      core_type ty
  (* let open P in *)
  | Texp_open (flag, p, lid, env) ->
    fprintf fmt "open (%a, %a, %a)"
      override flag
      path p
      longident lid.txt
  (* Constraint to verify that methods are polymorphic *)
  | Texp_poly tyopt ->
    fprintf fmt "poly %a" core_type_opt tyopt
  (* Adds a locally abstract type
     fun (type ty) -> *)
  | Texp_newtype ty ->
    fprintf fmt "newtype %s" ty


and value_description fmt vd =
  fprintf fmt "val %a (valdesc_%a) : @,%a (* prims: [%a]; ty: %a *)"
    ident vd.val_id
    (wrap_full attributes) vd.val_attributes
    core_type vd.val_desc
    (wrap_full (fun fmt -> List.iter (fprintf fmt "%s "))) vd.val_prim
    (* Pstr_primitive can take multiple arguments *)
    (wrap_full (Printtyp.value_description vd.val_id)) vd.val_val

and type_declaration_list fmt l =
  (* invariant: length l >= 1 *)
  fprintf fmt "%a" type_declaration @@ List.hd l;
  List.iter (fprintf fmt "\nand %a" type_declaration) @@ List.tl l

and type_declaration fmt td =
  fprintf fmt "%a%a(tydecl_%a) = @,%a%a%a\n%a"
    (* args, id, attributes, ?manifest, private, type_kind, constraints *)
    type_decl_params td.typ_params
    ident td.typ_id
    (wrap_full attributes) td.typ_attributes
    (fun fmt -> function
         None -> ()
       | Some ct -> fprintf fmt "%a = " core_type ct) td.typ_manifest
    private_flag td.typ_private
    type_kind td.typ_kind
    constraints td.typ_cstrs

and type_substitution fmt td =
  fprintf fmt "%a%a%a := @,%a%a%a\n%a"
    (* args, id, attributes, ?manifest, private, type_kind, constraints *)
    type_decl_params td.typ_params
    ident td.typ_id
    (wrap_full attributes) td.typ_attributes
    (fun fmt -> function
         None -> ()
       | Some ct -> fprintf fmt "%a = " core_type ct) td.typ_manifest
    private_flag td.typ_private
    type_kind td.typ_kind
    constraints td.typ_cstrs

and type_decl_params fmt = function
  | [] -> ()
  | (ty, v) :: rem ->
    fprintf fmt "(%a%a"
      variance v
      core_type ty;
    List.iter (fun (ty, v) ->
        fprintf fmt ", %a%a"
          variance v
          core_type ty) rem;
    fprintf fmt ")"

and type_kind fmt = function
    Ttype_abstract -> fprintf fmt "(* Abstract *)"
  | Ttype_variant constrs ->
    constructor_declaration_list fmt constrs
  | Ttype_record labels ->
    label_declaration_list fmt labels
  | Ttype_open -> fprintf fmt ".."

and label_declaration_list fmt l =
  List.iter (fprintf fmt "%a; @," label_declaration) l

and label_declaration fmt lab =
  fprintf fmt "(* id:%a *) %a%s : %a%a"
    (wrap_full ident) lab.ld_id
    mutable_flag lab.ld_mutable
    lab.ld_name.txt
    core_type lab.ld_type
    (wrap_full attributes) lab.ld_attributes

and constructor_declaration_list fmt cstrs =
  List.iter (fprintf fmt "| %a \n" constructor_declaration) cstrs


(* 4.03: add support for inlined record *)
and constructor_declaration fmt c =
  fprintf fmt "(* id: %a *) %s%a%a"
    (wrap_full ident) c.cd_id
    c.cd_name.txt
    (wrap_full attributes) c.cd_attributes
    constructor_args (c.cd_args, c.cd_res)

and constructor_args fmt = function
    [], None -> ()
  | h :: t, None ->
    fprintf fmt " of %a%a"
      core_type h
      (fun fmt -> List.iter (fprintf fmt "* %a" core_type)) t
  | [], Some ty -> fprintf fmt " : %a" core_type ty
  | h :: t, Some ty ->
    fprintf fmt " : %a%a -> %a"
      core_type h
      (fun fmt -> List.iter (fprintf fmt "* %a" core_type)) t
      core_type ty

and constraints fmt l =
  List.iter (fun (ct1, ct2, _) ->
      fprintf fmt "constraint %a = %a \n"
        core_type ct1
        core_type ct2) l

and type_extension fmt te =
  fprintf fmt "%a%a%a += %a%a"
    type_decl_params te.tyext_params
    path te.tyext_path
    attributes te.tyext_attributes
    private_flag te.tyext_private
    extension_constructor_list te.tyext_constructors

and extension_constructor_list fmt l =
  List.iter (extension_constructor fmt) l

and extension_constructor fmt ec =
  fprintf fmt "| %s%a%a (* type: %a *)\n"
    ec.ext_name.txt
    attributes ec.ext_attributes
    ext_constructor_kind ec.ext_kind
    (Printtyp.extension_constructor ec.ext_id) ec.ext_type

and ext_constructor_kind fmt = function
    Text_rebind (p, lid) ->
    fprintf fmt " = %a" path p
  | Text_decl (args, res) ->
    constructor_args fmt (args, res)

and core_type_opt fmt = function
    None -> fprintf fmt "None"
  | Some ty -> core_type fmt ty

and core_type fmt ct =
  fprintf fmt "@[(%a : @,%a)@]@."
    core_type_desc ct.ctyp_desc
    type_expr ct.ctyp_type

and core_type_desc fmt = function
    Ttyp_any -> fprintf fmt "_"
  | Ttyp_var v -> fprintf fmt "'%s" v (* type variable *)
  | Ttyp_arrow (lab, ct1, ct2) ->
    let l = if lab <> "" then lab ^ ":" else lab in
    fprintf fmt "%s%a -> %a" l core_type ct1 core_type ct2
  | Ttyp_tuple ctl ->
    core_type_list ~prefix:"(" ~suffix:")" "*" fmt ctl
  | Ttyp_constr (p, lid, ctl) ->
    fprintf fmt "%a %a"
      (core_type_list_empty ~prefix:"(" ~suffix:")" ",") ctl
      path p
  | Ttyp_object (comps, closed) ->
    fprintf fmt "< %a; %a >"
      class_components comps closed_flag closed
  | Ttyp_class (p, lid, ctl) ->
    fprintf fmt "%a #%a"
      (core_type_list_empty ~prefix:"(" ~suffix:")" ",") ctl
      path p
  | Ttyp_alias (ct, al) ->
    fprintf fmt "%a as %s" core_type ct al
  | Ttyp_variant (rfs, closed, labels_opt) ->
    print_variant_type fmt rfs closed labels_opt
  | Ttyp_poly (vars, ty) ->
    if vars = [] then core_type fmt ty
    else fprintf fmt "%a. %a"
        (fun fmt -> List.iter (fprintf fmt "'%s")) vars
        core_type ty
  | Ttyp_package packty ->
    fprintf fmt "(module %a)"
      package_type packty

and core_type_list_empty ?(prefix="") ?(suffix="") sep fmt l =
  if List.length l <> 0 then
    core_type_list ~prefix ~suffix sep fmt l

and core_type_list ?(prefix="") ?(suffix="") sep fmt l =
  fprintf fmt "%s" prefix;
  if List.length l <> 0 then
    begin
      core_type fmt @@ List.hd l;
      List.iter (fun ct -> fprintf fmt "* %a"
                    core_type ct) (List.tl l)
    end;
  fprintf fmt "%s" suffix

and print_variant_type fmt rfs closed opt =
  match closed, opt with
    Closed, None -> fprintf fmt "[ %a ]" row_field_list rfs
  | Open, None -> fprintf fmt "[> %a ]" row_field_list rfs
  | Closed, Some [] -> fprintf fmt "[< %a ]" row_field_list rfs
  | Closed, Some l ->
    fprintf fmt "[< %a > %a ]" row_field_list rfs
      (fun fmt l -> List.iter (fprintf fmt "`%s ") l) l
  | _, _ -> assert false

and row_field_list fmt l =
  List.iter (row_field fmt) l

and row_field fmt = function
    Ttag (l, attr, cst, ctys) ->
    if cst then fprintf fmt "`%s%a @,| " l attributes attr;
    List.iter (fun cty ->
        fprintf fmt "`%s%a of %a & "
          l attributes attr core_type cty) ctys
  | Tinherit cty -> core_type fmt cty

and class_components fmt l =
  List.iter (fun (n, attr, ct) ->
      fprintf fmt "%s%a : @,%a"
        n attributes attr core_type ct) l

and attribute: formatter -> Typedtree.attribute -> unit =
  fun fmt (attr, pay) ->
    Format.fprintf fmt "(%s : %a)" attr.txt payload pay

and payload fmt = function
    Parsetree.PStr _ -> Format.fprintf fmt "Pstr"
  | Parsetree.PTyp _ -> Format.fprintf fmt "Ptyp"
  | Parsetree.PPat _ -> Format.fprintf fmt "Ppat"

and attributes fmt (l:Typedtree.attributes) =
  Format.fprintf fmt "attrs: [ %a ]" (fun fmt ->
      List.iter (fprintf fmt "%a " attribute)) l

and package_type fmt p =
  fprintf fmt "%a%a : @,%a"
    path p.pack_path
    field_constraints p.pack_fields
    modtype p.pack_type

and field_constraints fmt l =
  if l <> [] then
    begin
      let (lid, ty), rem = List.hd l, List.tl l in
      fprintf fmt "with type %a = @,%a"
        longident lid.txt
        core_type ty;
      List.iter (fun (lid, ty) ->
          fprintf fmt "and %a = @,%a"
            longident lid.txt
            core_type ty) rem
    end

and module_declaration fmt m =
  fprintf fmt "%a%a : %a"
    ident m.md_id
    attributes m.md_attributes
    module_type m.md_type

and module_type_declaration fmt mty =
  fprintf fmt "%a%a%a"
    ident mty.mtd_id
    attributes mty.mtd_attributes
    (fun fmt -> function
         None -> ()
       | Some mtype -> fprintf fmt " = %a" module_type mtype) mty.mtd_type

and module_type fmt mty =
  fprintf fmt "%a%a (* : %a *)"
    module_type_desc mty.mty_desc
    attributes mty.mty_attributes
    Printtyp.modtype mty.mty_type

and module_type_desc fmt = function
    Tmty_ident (p, lid) ->
    path fmt p
  | Tmty_signature s ->
    signature fmt s
  | Tmty_functor (id_arg, n, mty_opt, mty_res) ->
    fprintf fmt "functor (%a%a) -> \n%a"
      ident id_arg
      module_type_option mty_opt
      module_type mty_res
  | Tmty_with (mty, with_cstr) ->
    fprintf fmt "%a with %a"
      module_type mty
      with_constraints with_cstr
  | Tmty_typeof me ->
    fprintf fmt "module type of %a"
      module_expression me
  | Tmty_alias (p, lid) ->
    fprintf fmt "(module %a)"
      path p

and with_constraints fmt cstrs =
  List.iter (fprintf fmt "%a " with_constraint) cstrs

and with_constraint fmt (p, _, c) =
  match c with
    Twith_type td ->
    type_declaration fmt td
  | Twith_module (p', lid) ->
    fprintf fmt "%a = %a"
      path p
      path p'
  | Twith_typesubst td ->
    type_substitution fmt td
  | Twith_modsubst (p', lid) ->
    fprintf fmt "%a := %a"
      path p
      path p'

and signature fmt s =
  fprintf fmt "sig\n%aend\n(* : %a *)"
    (fun fmt -> List.iter (fun si ->
         fprintf fmt "  %a\n" signature_item_desc si.sig_desc)) s.sig_items
    (wrap_full Printtyp.signature) s.sig_type

and signature_item_desc fmt = function
    Tsig_value v -> value_description fmt v
  | Tsig_type (td :: rem) -> (* invariant: at least one type *)
    fprintf fmt "type %a" type_declaration td;
    List.iter (fprintf fmt "\nand %a" type_declaration) rem
  | Tsig_typext ext ->
    fprintf fmt "type %a"
      type_extension ext
  | Tsig_exception ex ->
    fprintf fmt "exception %a"
      extension_constructor ex
  | Tsig_module md ->
    fprintf fmt "module %a"
      module_declaration md
  | Tsig_recmodule (mb :: rem) -> (* invariant: always 1 module *)
    fprintf fmt "module rec %a\n%a"
      module_declaration mb
      (fun fmt -> List.iter (fprintf fmt "and %a" module_declaration)) rem
  | Tsig_modtype mty_decl ->
    fprintf fmt "module type %a"
      module_type_declaration mty_decl
  | Tsig_open open_desc ->
    fprintf fmt "open %a"
      open_description open_desc
  | Tsig_class _ -> assert false
  | Tsig_class_type _ -> assert false
  | Tsig_include incl_decl ->
    fprintf fmt "include %a"
      include_description incl_decl
  | Tsig_attribute attr ->
    attribute fmt attr
  | _ -> assert false

and module_expression fmt mod_expr =
  fprintf fmt "@[<1>(%a : %a)@]"
    module_expr_desc mod_expr.mod_desc
    modtype mod_expr.mod_type

and module_type_constraint fmt = function
  | Tmodtype_implicit ->
    fprintf fmt "Implicit"
  | Tmodtype_explicit mty ->
    fprintf fmt "Explicit (%a)"
      module_type mty

and module_expr_desc fmt = function
    Tmod_ident (p, lid) ->
    path fmt p
  | Tmod_structure strc ->
    structure fmt strc
  | Tmod_functor (id, str, modtype_opt, modexpr) ->
    fprintf fmt "functor (%a%a) -> \n%a"
      ident id
      module_type_option modtype_opt
      module_expression modexpr
  | Tmod_apply (modfun, modarg, modco) ->
    fprintf fmt "%a(%a) (* :> %a *)"
      module_expression modfun
      module_expression modarg
      module_coercion modco
  | Tmod_constraint (modexpr, mtype, mty_constr, modco) ->
    fprintf fmt "(%a : %a) \n(* mty_constr: %a;\n   :> %a *)"
      module_expression modexpr
      modtype mtype
      module_type_constraint mty_constr
      module_coercion modco
  | Tmod_unpack (expr, mty) -> (* (val expr : modtype) *)
    fprintf fmt "(val %a : %a)"
      expression expr modtype mty

and structure fmt strc =
  fprintf fmt "@[<1>(struct\n%aend : sig\n%a\nend)@]"
    structure_items strc.str_items
    Printtyp.signature strc.str_type

and structure_items fmt items =
  List.iter (fun i ->
      fprintf fmt "%a\n  "
        structure_item_desc i.str_desc) items

and structure_item_desc fmt = function
  | Tstr_eval (expr, attr) ->
    fprintf fmt "let _ = \n%a%a"
      expression expr
      attributes attr
  | Tstr_value (flag, vbs) ->
    fprintf fmt "let %a %a"
      rec_flag flag
      value_bindings vbs
  | Tstr_primitive vd ->
    fprintf fmt "external %a"
      value_description vd
  | Tstr_type tydecls ->
    fprintf fmt "type %a"
      type_declaration_list tydecls
  | Tstr_typext tyext ->
    fprintf fmt "type %a"
      type_extension tyext
  | Tstr_exception ex_cons ->
    fprintf fmt "exception %a"
      extension_constructor ex_cons
  | Tstr_module mb ->
    fprintf fmt "module %a"
      module_binding mb
  | Tstr_recmodule (mb :: rem) -> (* invariant: always 1 module *)
    fprintf fmt "module rec %a\n%a"
      module_binding mb
      (fun fmt -> List.iter (fprintf fmt "and %a" module_binding)) rem
  | Tstr_modtype mty_decl ->
    fprintf fmt "module type %a"
      module_type_declaration mty_decl
  | Tstr_open open_desc ->
    fprintf fmt "open %a"
      open_description open_desc
  | Tstr_class cd ->
    fprintf fmt "class %a"
      class_declarations cd
  | Tstr_class_type _ -> assert false
  | Tstr_include incl_decl ->
    fprintf fmt "include %a"
      include_declaration incl_decl
  | Tstr_attribute attr ->
    attribute fmt attr
  | _ -> assert false

and module_binding fmt mb =
  fprintf fmt "%a%a = %a"
    ident mb.mb_id
    attributes mb.mb_attributes
    module_expression mb.mb_expr

and open_description fmt od =
  fprintf fmt "%a%a (* %a *)"
    path od.open_path
    attributes od.open_attributes
    override od.open_override

and include_infos:
  'a. (formatter -> 'a -> 'unit) -> formatter -> 'a include_infos -> unit =
  fun incl_mod fmt inf ->
  fprintf fmt "%a : %a"
    incl_mod inf.incl_mod
    Printtyp.signature inf.incl_type

and include_description fmt id =
  include_infos module_type fmt id

and include_declaration fmt ic =
  include_infos module_expression fmt ic

and module_type_option fmt = function
    None -> ()
  | Some mt -> fprintf fmt " : %a" module_type mt

and module_coercion fmt = function

  | _ -> ()

and class_declarations fmt cd =
  class_declaration fmt (List.hd cd);
  List.iter (fun (cd : (Typedtree.class_declaration * string list * Asttypes.virtual_flag))-> Format.fprintf fmt "and %a" class_declaration cd)
  @@ List.tl cd

and class_declaration fmt (ci, _, _) =
  class_infos class_expr fmt ci

and class_infos f fmt ci =
  Format.fprintf fmt "[%a] %s =\n%a"
    type_decl_params ci.ci_params
    ci.ci_id_name.Location.txt
    f ci.ci_expr

and class_expr fmt ce =
  Format.fprintf fmt
    "%a(* %a *)"
    class_expr_desc ce.cl_desc
    Printtyp.class_type ce.cl_type

and class_expr_desc fmt = function
    Tcl_ident (p, _, tys) ->
    Format.fprintf fmt "[%a]%a"
      (core_type_list ~prefix:"[" ~suffix:"]" ",") tys Printtyp.path p
  | Tcl_structure cl ->
    class_structure fmt cl
  | Tcl_fun (l, pat, _(* meths *), ce, _) ->
    Format.fprintf fmt "fun %a%a -> %a"
      label l
      pattern pat
      class_expr ce
  | Tcl_apply (ce, args) ->
    Format.fprintf fmt "%a %a"
      class_expr ce
      apply_args args
  | Tcl_let (flag, vbs, _, ce) ->
    Format.fprintf fmt "let %a %a in@, %a"
      rec_flag flag
      value_bindings vbs
      class_expr ce
  | Tcl_constraint (ce, ctopt, _, _, _) -> assert false

and class_structure fmt cs =
  Format.fprintf fmt
    "object (%a)\n\
     %a\n\
     end (* : %a *)"
    pattern cs.cstr_self
    class_fields cs.cstr_fields
    (wrap_full Printtyp.class_type) (Cty_signature cs.cstr_type)

and class_fields fmt cfs =
  List.iter (fun cf ->
      Format.fprintf fmt "%a\n" class_field cf.cf_desc) cfs

and class_field_kind fmt = function
    Tcfk_virtual cty ->
    Format.fprintf fmt ": %a" core_type cty
  | Tcfk_concrete (ov, exp) ->
    Format.fprintf fmt "(* %a *) = %a"
      override ov
      expression exp

and class_field fmt = function
    Tcf_inherit (ov, ce, alias, _, _) ->
    Format.fprintf fmt "inherit (*%a*)%a%a"
      override ov
      class_expr ce
      (fun fmt al ->
         match al with None -> () | Some s -> Format.fprintf fmt "as %s" s)
      alias
    (* Inherited instance variables and concrete methods *)
  | Tcf_val (n, mut, id, fk, _) ->
    Format.fprintf fmt "val %a %s %a"
      mutable_flag mut n.Location.txt
      class_field_kind fk
  | Tcf_method (n, priv, cfk) ->
    Format.fprintf fmt "method %a %s %a"
      private_flag priv n.Location.txt
      class_field_kind cfk
  | Tcf_constraint (cty, cty') ->
    Format.fprintf fmt "constraint %a = %a"
      core_type cty
      core_type cty'
  | Tcf_initializer exp ->
    Format.fprintf fmt "initializer %a"
      expression exp
  | Tcf_attribute attrs -> assert false
    (* attributes fmt attrs *)

module Types = struct
  open Types

  let rec commutable fmt = function
      Cok -> Format.fprintf fmt "Cok"
    | Cunknown -> Format.fprintf fmt "Cunknown"
    | Clink c -> Format.fprintf fmt "Clink %a" commutable !c

  let type_expr_list fmt tys =
    List.iter (fun ty ->
        Format.fprintf fmt "%a, " Printtyp.raw_type_expr ty) tys

  let type_expr_opt fmt = function
      None -> ()
    | Some ty -> Printtyp.raw_type_expr fmt ty

  let constructor_declaration fmt cd =
  Format.fprintf fmt "{\n\
                        cd_id: %a;\n\
                        cd_args: %a;\n\
                        cd_res: %a;\n\
                      }"
    Printtyp.ident cd.cd_id
    type_expr_list cd.cd_args
    type_expr_opt cd.cd_res

  let constructor_declaration_list fmt cds =
    List.iter (fun cd ->
        Format.fprintf fmt "%a;\n" constructor_declaration cd) cds

  let kind fmt = function
    Type_abstract -> Format.fprintf fmt "Abstract"
  | Type_record _ -> Format.fprintf fmt "Record"
  | Type_variant cds -> Format.fprintf fmt "Variant:\n  %a"
                          constructor_declaration_list cds
  | Type_open -> Format.fprintf fmt "Open"

  let variance_list fmt vl = (* Obj does not exists *)
    List.iter (fun vl -> Format.fprintf fmt "%d, " (Obj.magic vl)) vl

  let type_declaration fmt td =
    Format.fprintf fmt
      "{\n\
       type_params: %a;\n\
       type_arity: %d;\n\
       type_kind: %a;\n\
       type_private: %a;\n\
       type_manifest: %a;\n\
       type_variance: %a;\n\
       }"
      type_expr_list td.type_params
      td.type_arity
      kind td.type_kind
      private_flag td.type_private
      type_expr_opt td.type_manifest
      variance_list td.type_variance

  let type_declaration_list fmt tds =
    List.iter (Format.fprintf fmt "%a; \n"@@ type_declaration) tds


  let rec print_type_simple fmt = function
        Tvar _ -> Format.fprintf fmt "Tvar"
      | Tarrow (_, t1, t2, _) ->
        Format.fprintf fmt "Tarrow (%a, %a)"
          print_type_simple t1.desc print_type_simple t2.desc
      | Ttuple _ -> Format.fprintf fmt "Ttuple"
      | Tconstr (p, _, _) ->
        Format.fprintf fmt "Tconstr %a" path p
      | Tobject _ -> Format.fprintf fmt "Tobject"
      | Tfield _ -> Format.fprintf fmt "Tfield"
      | Tnil -> Format.fprintf fmt "Tnil"
      | Tlink _ -> Format.fprintf fmt "Tlink"
      | Tsubst _ -> Format.fprintf fmt "Tsubst"         (* for copying *)
      | Tvariant _ -> Format.fprintf fmt "Tvariant"
      | Tunivar _ -> Format.fprintf fmt "Tunivar"
      | Tpoly _ -> Format.fprintf fmt "Tpoly"
      | Tpackage _ -> Format.fprintf fmt "Tpackage"

  let print_opt_string fmt = function
      None -> Format.fprintf fmt "None"
    | Some v -> Format.fprintf fmt "(Some %s)" v

  let rec type_expr fmt ty =
    match ty.desc with
      Tvar v-> Format.fprintf fmt "Tvar %a" print_opt_string v
    | Tarrow (l, t1, t2, com) ->
      Format.fprintf fmt "Tarrow (%s, %a, %a, %a)"
        l type_expr t1 type_expr t2
        commutable com
    | Ttuple tys -> Format.fprintf fmt "Ttuple (%a)" type_exprs tys
    | Tconstr (p, tys, mem) ->
      Format.fprintf fmt "Tconstr (%a, [%a], %a)"
        path p
        type_exprs tys
        abbrev_memo !mem
    | Tobject (ty, rem) ->
      Format.fprintf fmt "Tobject (%a, %a)"
        type_expr ty
        object_rem rem
    | Tfield (n, fk, ty, rem) ->
      Format.fprintf fmt "Tfield (%s, %a, %a, %a)"
        n field_kind fk type_expr ty type_expr rem
    | Tnil -> Format.fprintf fmt "Tnil"
    | Tlink te -> Format.fprintf fmt "Tlink (%a)" type_expr te
    | Tsubst _ -> Format.fprintf fmt "Tsubst"         (* for copying *)
    | Tvariant _ -> Format.fprintf fmt "Tvariant"
    | Tunivar _ -> Format.fprintf fmt "Tunivar"
    | Tpoly _ -> Format.fprintf fmt "Tpoly"
    | Tpackage _ -> Format.fprintf fmt "Tpackage"

  and type_exprs fmt tys =
    if List.length tys > 0 then begin
      type_expr fmt @@ List.hd tys;
      List.iter (fun ty -> Format.fprintf fmt ", %a" type_expr ty) (List.tl tys)
    end

  and abbrev_memo fmt = function
      Mnil -> Format.fprintf fmt "Mnil"
    | Mlink mem -> Format.fprintf fmt "Mlink %a" abbrev_memo !mem
    | Mcons (fl, p, t1, t2, mem) ->
      Format.fprintf fmt "Mcons (%a, %a, %a, %a, %a)"
        private_flag fl
        path p
        type_expr t1
        type_expr t2
        abbrev_memo mem

  and row_desc fmt r =
    Format.fprintf fmt "{\nrow_fields =";
    List.iter (fun (l, r) -> Format.fprintf fmt "(`%s,%a)" l row_field r)
      r.row_fields;
    Format.fprintf fmt ";\nrow_more=%a;\nrow_closed=%b;\nrow_fixed=%b;\n}"
      type_expr r.row_more r.row_closed r.row_fixed

  and row_field fmt = function
      Rpresent s -> Format.fprintf fmt "Rpresent %a" type_expr_opt s
    | Reither (cst, tys, p, _) ->
      Format.fprintf fmt "Reither (%b, [%a], %b, _)" cst type_exprs tys p
    | Rabsent -> Format.fprintf fmt "Rabsent"

  and object_rem fmt r =
    match !r with
      None -> Format.fprintf fmt "None"
    | Some (p, tys) ->
      Format.fprintf fmt "Some (%a, [%a])"
        path p
        type_exprs tys

  and field_kind_option fmt = function
      { contents = None } -> Format.fprintf fmt "None"
    | { contents = Some _ } -> Format.fprintf fmt "Some _"

  and field_kind fmt = function
      Fvar f -> Format.fprintf fmt "Fvar (%a)" field_kind_option f
    | Fpresent -> Format.fprintf fmt "Fpresent"
    | Fabsent -> Format.fprintf fmt "Fabsent"

  and value_kind fmt = function
      Val_anc (meths, id) -> Format.fprintf fmt "Val_anc %s" id
    | Val_reg -> Format.fprintf fmt "Val_reg"
    | Val_self (_, _, _, _)-> Format.fprintf fmt "Val_self"
    | Val_ivar (_, id) -> Format.fprintf fmt "Val_ivar %s" id
    | Val_prim _ -> Format.fprintf fmt "Val_prim"
    | Val_unbound -> Format.fprintf fmt "Val_unbound"

  and constructor_description fmt cd =
    Format.fprintf fmt
      "{\n\
       cstr_name: %s;\n\
       cstr_res: %a;\n\
       cstr_existentials: %a;\n\
       cstr_args: %a;\n\
       cstr_arity: %d;\n\
       cstr_generalized: %b;\n\
       }"
      cd.cstr_name
      type_expr cd.cstr_res
      type_expr_list cd.cstr_existentials
      type_expr_list cd.cstr_args
      cd.cstr_arity
      cd.cstr_generalized
end
