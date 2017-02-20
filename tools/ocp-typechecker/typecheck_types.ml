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

open OCaml.Types
open Typecheck_flags
open OCaml.Path
open OCaml.Longident
open Typecheck_result

type error = ..

let path_compare p1 p2 =
  let rec compare p1 p2 = match p1, p2 with
      Pident id1, Pident id2 ->
      if id1 == id2 then 0 else Pervasives.compare id1 id2
    | Pdot(p1, p2, _), Pdot (p1', p2', _) ->
      let c = Pervasives.compare p2 p2' in
      if c = 0 then compare p1 p1' else c
    | Papply(p1, p2), Papply (p1', p2') ->
      let c = compare p1 p1' in
      if c = 0 then compare p2 p2' else c
    | _, _ -> Pervasives.compare p1 p2
  in
  compare p1 p2


module TyMap' = Map.Make(TypeOps)
module PathEq = struct
  open Path
  module H = Map.Make(struct
      type t = Path.t
      let rec compare = path_compare
    end)

  let i = ref 0
  type t = { i : int;
             index : int H.t;
             repr : Typecheck_uf.t }
  let create i = { i = 0; repr = Typecheck_uf.create i; index = H.empty }
  let find h p =
    print_debug
      (Format.asprintf "PathEq.find %a" Typecheck_pretty.path p);
    try
      print_debug "Here?";
      let index = H.find p h.index in
      print_debug "Not here.";
      Typecheck_uf.find h.repr index, h
    with Not_found ->
      print_debug "Not_found";
      h.i, { h with index = H.add p h.i h.index; i = h.i + 1 }

  let union h p1 p2 =
    print_debug (Format.asprintf "Union of %a /\\ %a"
      Typecheck_pretty.path p1 Typecheck_pretty.path p2);
    let i1, h = find h p1 in
    let i2, h = find h p2 in
    { h with repr = Typecheck_uf.union h.repr i1 i2 }

  let rec eq h p1 p2 =
    let i1, h = find h p1 in
    let i2, h = find h p2 in
    print_debug (Format.asprintf "%a: %d, %a: %d"
      Typecheck_pretty.path p1 i1 Typecheck_pretty.path p2 i2);
    if i1 <> i2 then
      if Path.same p1 p2 then
        union h p1 p2, true
      else
        match p1, p2 with
          Pdot (p1', p2', _), Pdot (p1'', p2'', _) ->
          let h, res = eq h p1' p1'' in
          if p2' = p2'' && res then
            union h p1 p2, true
          else h, false
        | Papply (p1', p2'), Papply (p1'', p2'') ->
          let h, res2 = eq h p2' p2'' in
          let h, res1 = eq h p1' p1'' in
          if res1 && res2 then
            union h p1 p2, true
          else h, false
        | _ -> h, false
    else h, true
end

module TyMap = struct
  include TyMap'

  exception Found
  let exists f h =
    try iter (fun k v -> if f k v then raise Found) h; false
    with Found -> true

end

(* Contains generated abstract local types *)
module NewtyTbl = struct
  open Ident
  type t = Types.type_declaration tbl ref

  let create () : t = ref empty

  let add tbl id td =
    tbl := add id td !tbl

  let add_path tbl p td =
    let id = Path.head p in
    add tbl id td

  let find tbl id =
    find_same id !tbl

  let find_path tbl = function
      Pident id -> find tbl id
    | _ -> raise Not_found (* A newtype can only be a direct identificator,
                              otherwise it obviously is not a newtype, or an
                              abbreviated newtype wich will be later expanded *)
end

module UniTbl = Map.Make(String)

type kind =
    Tyvar of string
  | Newtype of Path.t

let print_kind fmt = function
    Tyvar v -> Format.fprintf fmt "(Tyvar %s)" v
  | Newtype p -> Format.fprintf fmt "(Newtype %a)" Typecheck_pretty.path p

module TySet = Set.Make (Types.TypeOps)

type tyset = { mutable value : TySet.t; uniq : int}

type context = {
  names : kind TyMap.t; (* Type to type variable associated *)
  univars : kind TyMap.t;
  named_vars : string list; (* List of named type variables *)
  name_counter : int;
  paths : PathEq.t; (* Set of known paths, with their equalities *)
  ambivalents : tyset TyMap.t;
  env : Env.t;
  gadt : bool; (* Flag: typing a case of a GADT *)
  functor_body : bool; (* Typing a module wihch is the body of a functor *)
  generalized_vars : TySet.t;
}

let create_context env =
  let names : kind TyMap.t = TyMap.empty in
  let univars : kind TyMap.t = TyMap.empty in
  let named_vars = [] in
  let paths = PathEq.create 1987 (* Arbitrary huge number *) in
  { names;
    univars;
    name_counter = 0;
    named_vars;
    paths;
    ambivalents = TyMap.empty;
    env;
    gadt = false;
    functor_body = false;
    generalized_vars = TySet.empty;
  }

let create_tyset =
  let id = ref 0 in
  fun () -> { value = TySet.empty; uniq = (incr id; !id) }

let newtypes = NewtyTbl.create ()

let add_named_var ty ctx =
  match ty.desc with
    Tvar (Some name) | Tunivar (Some name) ->
      if List.mem name ctx.named_vars then ctx else
      { ctx with named_vars = name :: ctx.named_vars }
  | _ -> ctx

let rec new_name ctx =
  let name =
    if ctx.name_counter < 26
    then String.make 1 (Char.chr(97 + ctx.name_counter))
    else String.make 1 (Char.chr(97 + ctx.name_counter mod 26)) ^
           string_of_int(ctx.name_counter / 26) in
  let ctx = { ctx with name_counter = ctx.name_counter + 1 } in
  if List.mem name ctx.named_vars
     || TyMap.exists (fun _ name' -> match name' with
           Tyvar name' -> name = name'
         | Newtype _ -> false) ctx.names
  then new_name ctx
  else Tyvar name, ctx

(** Type equivalence *)

exception No_repr of kind * kind

let find_repr ty ctx =
    try Some (TyMap.find ty ctx.names)
    with Not_found ->
      try match ty.desc with
        | Tunivar _ -> Some (TyMap.find ty ctx.univars)
        | _ -> raise Not_found
      with Not_found -> None

let find_repr' ?(strict=false) ctx ty1 ty2 =
  match find_repr ty1 ctx, find_repr ty2 ctx with
    None, None ->
    let v, ctx = new_name ctx in
    let names = TyMap.add ty1 v ctx.names in
    let names = TyMap.add ty2 v names in
    v, { ctx with names }
  | Some v, None when (not strict || ctx.gadt) ->
    let names = TyMap.add ty2 v ctx.names in
    v, { ctx with names }
  | None, Some v when (not strict || ctx.gadt) ->
    let names = TyMap.add ty1 v ctx.names in
    v, { ctx with names }
  | Some v1, Some v2 -> if v1 = v2 then v1, ctx else raise (No_repr (v1, v2))
  | _, _ -> raise Not_found

let is_univar = function
    { desc = Tunivar _; } -> true
  | _ -> false

let equiv_univars ctx t1 t2 =
  try
    let repr1 = TyMap.find t1 ctx.univars in
    let repr2 = TyMap.find t2 ctx.univars in
    repr1 == repr2
  with Not_found -> raise Not_found

let add_newtype p td =
  NewtyTbl.add_path newtypes p td

let is_newtype p =
  try ignore @@ NewtyTbl.find_path newtypes p; true
  with _ -> false

let rec is_existential p =
  match p with
    Path.Papply (_, _) | Path.Pdot (_, _, _) -> false
  | Path.Pident i ->
    String.contains_from (Ident.name i) 1 '#'

let gadt_mode ctx p =
  (is_newtype p || is_existential p) && ctx.gadt

let find_univar_repr ctx ty1 ty2 =
  match find_repr ty1 ctx, find_repr ty2 ctx with
    None, None ->
    let v, ctx = new_name ctx in
    let univars = TyMap.add ty1 v ctx.univars in
    let univars = TyMap.add ty2 v univars in
    v, { ctx with univars }
  | Some v, None ->
    let univars = TyMap.add ty2 v ctx.univars in
    v, { ctx with univars }
  | None, Some v ->
    let univars = TyMap.add ty1 v ctx.univars in
    v, { ctx with univars }
  | Some v1, Some v2 -> if v1 = v2 then v1, ctx else raise (No_repr (v1, v2))

let allocate_univars ctx v1 v2 =
  List.fold_left2 (fun ctx v1 v2 ->
      let v, ctx = new_name ctx in
      let names = TyMap.add v1 v ctx.names in
      let names = TyMap.add v2 v names in
      match v1.desc, v2.desc with
        Tunivar _, Tunivar _ ->
        (* When univars have already been binded without using a quantifier *)
        let ctx =
          try
            snd @@ find_univar_repr { ctx with names } v1 v2
          with No_repr (_, _) ->
            let univars = TyMap.add v1 v ctx.univars in
            let univars = TyMap.add v2 v univars in
            { ctx with names; univars } in
        ctx
      | _-> assert false) ctx v1 v2

let allocate_vars ctx v1 v2 =
  List.fold_left2 (fun ctx v1 v2 ->
      let v, ctx = new_name ctx in
      let names = TyMap.add v1 v ctx.names in
      let names = TyMap.add v2 v names in
      { ctx with names }) ctx v1 v2

(* Signature matching utilitaries *)

type _ sig_kind =
    Val : value_description sig_kind
  | Type : (Ident.t * type_declaration) sig_kind
  | Ext : (Ident.t * extension_constructor) sig_kind
  | Mod : (Ident.t * module_declaration) sig_kind
  | Modtype : (Ident.t * modtype_declaration) sig_kind
  | Class : (Ident.t * class_declaration) sig_kind
  | Classtype : (Ident.t * class_type_declaration) sig_kind

(* let kindof : type a. signature_item -> a kind = function *)
(*     Sig_value (_, _) -> Val *)
(*   | Sig_type (_, _, _) -> Type *)
(*   | Sig_typext (_, _, _) -> Ext *)
(*   | Sig_module (_, _, _) -> Mod *)
(*   | Sig_modtype (_, _) -> Modtype *)
(*   | Sig_class (_, _, _) -> Class *)
(*   | Sig_class_type (_, _, _) -> Classtype *)

let extract_value : type a. a sig_kind -> signature_item -> a =
  fun kind v ->
    match v, kind with
      Sig_value (_, vd), Val -> vd
    | Sig_type (id, td, _), Type -> id, td
    | Sig_typext (id, ec, _), Ext -> id, ec
    | Sig_module (id, md, _), Mod -> id, md
    | Sig_modtype (id, mtd), Modtype -> id, mtd
    | Sig_class (id, cd, _), Class -> id, cd
    | Sig_class_type (id, ctd, _), Classtype -> id, ctd
    | _, _ -> assert false

let rec similar_paths p p' =
  let res = match p, p' with
      Pident id, Pident id' ->
      print_debug
        (Format.asprintf "id: %s; id2: %s"
           (Ident.name id) (Ident.name id'));
      Ident.name id = Ident.name id'
  | Pdot (p, s, _), Pdot (p', s', _) -> s = s' && similar_paths p p'
  | Papply (p1, p2), Papply (p1', p2') ->
    similar_paths p1 p1' && similar_paths p2 p2'
  | _, _ -> false in
  print_debug (Format.asprintf "%a ?? %a: %b"
                         Printtyp.path p Printtyp.path p' res);
  res

let is_sig_value id = function
    Sig_value (id', _) -> Ident.name id = Ident.name id'
  | _ -> false

let is_sig_type id = function
    Sig_type (id', _, _) -> Ident.name id = Ident.name id'
  | _ -> false

let is_sig_typext (* ( *)id(* , typath) *) = function
    Sig_typext (id', ec, _) ->
    let res = Ident.name id = Ident.name id'(*  && *)
              (* similar_paths ec.ext_type_path typath *) in
    (* print_debug *)
    (*   (Format.asprintf "%a similar to (%a, %a)? %b" *)
    (*      (Printtyp.extension_constructor id') ec Printtyp.ident id *)
    (*      Printtyp.path typath res); *)
    res
  | _ -> false

let is_sig_module id = function
    Sig_module (id', _, _) -> Ident.name id = Ident.name id'
  | _ -> false

let is_sig_modtype id = function
    Sig_modtype (id', _) -> Ident.name id = Ident.name id'
  | _ -> false

let is_sig_class id = function
    Sig_class (id', _, _) -> Ident.name id = Ident.name id'
  | _ -> false

let is_sig_class_type id = function
    Sig_class_type (id', _, _) -> Ident.name id = Ident.name id'
  | _ -> false

type values = signature_item list
type substs = type_expr TyMap.t

let add_env : type a. context -> a sig_kind -> a -> context =
  fun ctx kind args ->
    let env =
      match kind, args with
        Val, vd -> ctx.env
      | Type, (id, td) -> Env.add_type ~check:false id td ctx.env
      | Ext, (id, ec) -> Env.add_extension ~check:false id ec ctx.env
      | Mod, (id, md) -> Env.add_module_declaration id md ctx.env
      | Modtype, (id, mty) -> Env.add_modtype id mty ctx.env
      | Class, (id, cl) -> Env.add_class id cl ctx.env
      | Classtype, (id, cty) -> Env.add_cltype id cty ctx.env
    in
    { ctx with env }

(* let partition_one : *)
(*   type a. (signature_item -> bool) -> values -> a sig_kind -> (a * values) option * *)
(*   a sig_kind = *)
(*   fun f l kind -> *)
(*   let p1, p2 = List.partition f l in *)
(*   match p1 with *)
(*     v :: [] -> Some (extract_value kind v, p2), kind *)
(*   | _ -> None, kind *)

let partition_one :
  type a. (signature_item -> bool) -> values -> a sig_kind -> (a * values) option *
  a sig_kind =
  fun f l kind ->
    let rec partition seen f l =
      match l with
        [] -> None, List.rev seen
      | v :: rem ->
        if f v then Some v, List.rev_append seen rem
        else partition (v :: seen) f rem in
    let p1, p2 = partition [] f l in
    match p1 with
      Some v -> Some (extract_value kind v, p2), kind
    | None -> None, kind
let gen_res :
  type a. substs -> values -> a -> a sig_kind -> context ->
  (substs * values * context, 'b) result =
  fun subst values v kind ctx ->
  Ok (subst, values, add_env ctx kind v)

let try_instance inst v1 v2 ctx subst values kind =
  print_debug "try_isntance";
  match inst ctx v1 v2 subst with
    Error e -> Error e
  | Ok (subst', ctx') -> gen_res subst' values v1 kind ctx'

let transl_core_type :
  (context -> Typedtree.core_type -> Types.type_expr) ref =
  ref (fun _ _ -> assert false)

let apply_constraint :
  (context -> Location.t -> Types.signature -> Path.t -> Typedtree.with_constraint ->
   Types.signature) ref =
  ref (fun _ _ _ _ -> assert false)

(* Extract a signature from a module type *)
let extract_sig env loc mty =
  match Env.scrape_alias env mty with
    Mty_signature sg -> sg
  | _ -> raise(Typemod.Error(loc, env, Typemod.Signature_expected))

let extract_sig_open env loc mty =
  match Env.scrape_alias env mty with
    Mty_signature sg -> sg
  | _ -> raise(Typemod.Error(loc, env, Typemod.Structure_expected mty))


(* First class modules utilitaries *)

let find_types_in_sig cstrs sg =
  let tmp_env = Env.add_signature sg Env.empty in
  List.map (fun l -> Env.lookup_type l tmp_env) cstrs

let find_type_in_sig cstr sg =
  let tmp_env = Env.add_signature sg Env.empty in
  Env.lookup_type cstr tmp_env

let find_modtype_mty ctx i mty =
  let sg = extract_sig ctx.env Location.none mty in
  let tmp_env = Env.add_signature sg Env.empty in
  Env.lookup_modtype (Lident i) tmp_env

let find_module_mty ctx i mty =
  print_debug ("looking for " ^ i);
  let sg = extract_sig ctx.env Location.none mty in
  print_debug (Format.asprintf "extracted sig: %a"
                         Printtyp.signature sg);
  let tmp_env = Env.add_signature sg Env.empty in
  let p = Env.lookup_module ~load:false (Lident i) tmp_env in
  print_debug (Format.asprintf "extracted path: %a"
                         Printtyp.path p);
  Env.find_module p tmp_env

(* let find_module_in_modtype n  *)

let exist_typedecl =
  { type_params = []; type_arity = 0; type_kind = Type_abstract;
    type_private = Asttypes.Private; type_manifest = None; type_variance = [];
    type_newtype_level = None; type_loc = Location.none; type_attributes = [] }

let gen_typedecl package env (p, decl) ty : Types.type_declaration =
  let td = { decl with
             type_params = if package then [] else decl.type_params;
              Types.type_manifest = Some ty;
              type_private = Asttypes.Public } in
  td

let rec extract_rem_path : Path.t -> Longident.t = function
    Pident _ | Papply _ -> assert false
  | Pdot (Pident _, n, _) -> Lident n
  | Pdot (p, n, _) -> Ldot (extract_rem_path p, n)

let gen_signature env p decl sg =
  let rec apply p = function
      (Sig_type (id, td, rs) :: rem) when id = Path.head p ->
      Sig_type (id, decl, rs) :: rem
    | (Sig_module (id, md, rs) :: rem) when id = Path.head p ->
      let lid = extract_rem_path p in
      let sg = extract_sig env Location.none md.md_type in
      let p', _ = find_type_in_sig lid sg in
      let sg' = apply p' sg in
      Sig_module (id, { md with md_type = Mty_signature sg'}, rs) :: rem
    | item :: rem ->
      item :: apply p rem
    | [] -> []
  in
  apply p sg

let create_package_mty env mty lids tys =
  print_debug "create_package_mty:";
  let sg = extract_sig env Location.none mty in
  print_debug (Format.asprintf "signature from mty:\n%a"
     Printtyp.signature sg);
  let tds = find_types_in_sig lids sg in
  let tds' = List.map2 (gen_typedecl true env) tds tys in (* Ugly complexity *)
  let ps = List.map fst tds in
  Mty_signature (
    List.fold_left2 (fun sg p td ->
        print_debug (Format.asprintf "replacing %a by %a"
          Typecheck_pretty.path p
          Typecheck_pretty.Types.type_declaration td);
        gen_signature env p td sg)
      sg ps tds')
  |> (fun mty ->
      print_debug (Format.asprintf "Generated mty: %a"
        Printtyp.modtype mty);
      mty)
  |> Mtype.freshen

let has_package_type ty =
  match (Btype.repr ty).desc with
    Tpackage _ -> print_debug "has_package_type"; true
  | _ -> print_debug "hasn't package_type"; false

module Iterate = struct
  (* Folding function over type, in prefix order (according to Type.type_desc
     declaration) *)

  let rec fold_type visited f acc ty =
    if visited ty then acc else
      let acc = f acc ty in 
      match ty.desc with
        Tvar _ | Tnil | Tunivar _ -> acc
      | Tlink ty | Tsubst ty | Tobject (ty, { contents = None }) ->
        fold_type visited f acc ty
      | Tarrow (_, ty1, ty2, _) | Tfield (_, _, ty1, ty2) ->
        fold_type visited f (fold_type visited f acc ty1) ty2
      | Ttuple tys | Tpackage (_, _, tys) | Tconstr (_, tys, _) ->
        List.fold_left (fold_type visited f) acc tys
      | Tobject (ty, { contents = Some (_, tys) }) | Tpoly (ty, tys) ->
        List.fold_left (fold_type visited f) (fold_type visited f acc ty) tys
      | Tvariant rd -> fold_row_desc visited f acc rd

  and fold_row_desc visited f acc rd =
    let may_fold fold acc arg =
      match arg with Some arg -> fold f acc arg | None ->  acc in
    let rec fold_field f acc rf =
      match rf with
        Rpresent tyopt -> may_fold (fold_type visited) acc tyopt
      | Reither (_, tys, _, { contents = tyopt }) ->
        let acc = List.fold_left (fold_type visited f) acc tys in
        may_fold fold_field acc tyopt
      | Rabsent -> acc
    in
    let acc_f =
      List.fold_left (fun acc (_, rf) ->
          fold_field f acc rf) acc rd.row_fields in
    let acc_m = fold_type visited f acc_f rd.row_more in
    may_fold (fun f acc (_, tys) ->
        List.fold_left (fold_type visited f) acc tys) acc_m rd.row_name

  (* Folds on syntactically equivalent types *)
  let rec fold_type2 visited f acc ty1 ty2 =
    if visited ty1 ty2 then acc else
      let acc = f acc ty1 ty2 in
      match (Btype.repr ty1).desc, (Btype.repr ty2).desc with
        Tvar _, Tvar _ | Tnil, Tnil | Tunivar _, Tunivar _ -> acc
      | Tobject (ty1, { contents = None }),
        Tobject (ty2, { contents = None }) ->
        fold_type2 visited f acc ty1 ty2
      | Tarrow (_, ty11, ty12, _), Tarrow (_, ty21, ty22, _)
      | Tfield (_, _, ty11, ty12), Tfield (_, _, ty21, ty22) ->
        fold_type2 visited f
          (fold_type2 visited f acc ty11 ty21)
          ty12 ty22
      | Ttuple tys1, Ttuple tys2 ->
        List.fold_left2 (fold_type2 visited f) acc tys1 tys2
      | Tpackage (p1, _, tys1), Tpackage (p2, _, tys2)
      | Tconstr (p1, tys1, _), Tconstr (p2, tys2, _) ->
        if path_compare p1 p2 = 0 then
          List.fold_left2 (fold_type2 visited f) acc tys1 tys2
        else acc
      | Tobject (ty1, { contents = Some (_, tys1) }),
        Tobject (ty2, { contents = Some (_, tys2) })
      | Tpoly (ty1, tys1), Tpoly (ty2, tys2) ->
        List.fold_left2
          (fold_type2 visited f)
          (fold_type2 visited f acc ty1 ty2)
          tys1 tys2
      | Tvariant rd1, Tvariant rd2 ->
        fold_row_desc2 visited f acc
          (Btype.row_repr rd1) (Btype.row_repr rd2)
      | _, _ -> acc

  and fold_row_desc2 visited f acc rd1 rd2 =
    let may_fold2 fold acc arg1 arg2 =
      match arg1, arg2 with
        Some arg1, Some arg2 -> fold f acc arg1 arg2
      | _, _ ->  acc in
    let rec fold_field2 f acc rf1 rf2 =
      match rf1, rf2 with
        Rpresent tyopt1, Rpresent tyopt2 ->
        may_fold2 (fold_type2 visited) acc tyopt1 tyopt2
      | Reither (_, tys1, _, { contents = tyopt1 }),
        Reither (_, tys2, _, { contents = tyopt2 }) ->
        let acc =
          List.fold_left2 (fold_type2 visited f) acc tys1 tys2 in
        may_fold2 fold_field2 acc tyopt1 tyopt2
      | _, _ -> acc
    in
    let acc_f =
      List.fold_left2 (fun acc (l1, rf1) (l2, rf2) ->
          if l1 = l2 then fold_field2 f acc rf1 rf2 else acc)
        acc rd1.row_fields rd2.row_fields in
    let acc_m = fold_type2 visited f acc_f rd1.row_more rd2.row_more in
    may_fold2 (fun f acc (p1, tys1) (p2, tys2) ->
        if path_compare p1 p2 = 0 then
          List.fold_left2 (fold_type2 visited f) acc tys1 tys2
        else acc)
      acc_m rd1.row_name rd2.row_name

end

module type Container = sig
  type t
  type elt
  val empty : t
  val exists : (elt -> bool) -> t -> bool
  val add : elt -> t -> t
  val remove : elt -> t -> t
end

module TyList = struct
  type t = type_expr list
  type elt = type_expr

  let empty = []
  let exists f l = List.exists f l
  let add t l = t :: l
  let remove t l = List.filter ((!=) t) l
end

let extract_vars :
  type a. (module Container with type t = a and type elt = type_expr) ->
  a -> type_expr -> a
  = fun m acc ty ->
    let module M = (val m) in
    let seen = ref M.empty in
    let visited ty = M.exists ((==) ty) !seen in
    let extract acc ty =
      let ty = Btype.repr ty in
      seen := M.add ty !seen;
      match ty.desc with
        Tvar v -> M.add ty acc
      | _ -> acc
    in
    Iterate.fold_type visited extract acc ty

let extract_vars_set acc ty =
  extract_vars (module TySet) acc ty

let extract_vars_list acc ty =
  extract_vars (module TyList) acc ty |> List.rev

let instance_types_ref :
  (context -> type_expr list -> type_expr list -> substs
  -> (substs * context, exn) result) ref
  = ref (fun _ _ _ _ -> assert false)

let instance_types ctx tys1 tys2 s =
  !instance_types_ref ctx tys1 tys2 s

let apply_subst_ref :
  (type_expr -> substs -> type_expr) ref
  = ref (fun _ _ -> assert false)

let apply_subst s ty = !apply_subst_ref s ty

let apply_args ctx vars args ty p =
  print_debug (Format.asprintf "apply_args: [%a] on %a"
    (fun fmt -> List.iter (fun ty ->
         Format.fprintf fmt "%a; " Printtyp.type_expr ty)) args
    Printtyp.type_expr ty);
  let ty = Btype.repr ty in
  if args = [] then ty else
    let substs = instance_types ctx args vars TyMap.empty in
    let vars = extract_vars_list [] ty in
    print_debug (Format.asprintf "extract_vars: [%a]"
                           (fun fmt -> List.iter (fun ty ->
                                Format.fprintf fmt "%a; " Printtyp.type_expr ty)) vars);
    match substs with
      Ok (substs, _) ->
      print_debug ("apply_args: OK, apply_subst");
      apply_subst ty substs
    | Error _ -> raise Ctype.Cannot_apply
    (* match ty.desc with *)
    (*   | Tconstr (_, vars, _) -> *)
    (*     Ctype.apply env vars ty args *)
    (*   | _ -> *)
    (*     let vars = (Env.find_type p env).type_params in *)
    (*     Ctype.apply env vars ty args *)

let find_equiv_ambi ctx p args =
  let m' = TyMap.filter (fun k _ ->
      match k with
        { desc = Tconstr (p', args', _); _ } ->
        snd @@ PathEq.eq ctx.paths p p' (* && args = args' *)
      | _ -> false) ctx.ambivalents in
  TyMap.choose m'

let find_equiv_ambi ctx ty args =
  print_debug (
    Format.asprintf "Looking for %a equivalent ambivalent."
      Printtyp.type_expr ty);
  let rec equiv ty ty' =
    let ty = Btype.repr ty and ty' = Btype.repr ty' in
    print_debug (
          Format.asprintf "%a and %a??"
            Printtyp.raw_type_expr ty Printtyp.raw_type_expr ty');
    if ty == ty' then true
    else
      match ty.desc, ty'.desc with
      | Tconstr (p, _, _), Tconstr (p', _, _) ->
        print_debug (
          Format.asprintf "%a and %a??"
            Typecheck_pretty.path p Typecheck_pretty.path p');
        Path.same p p'
      | Ttuple tys, Ttuple tys' ->
        List.for_all2 equiv tys tys'
      | Tarrow (l, ty1, ty2, _), Tarrow (l', ty1', ty2', _) ->
        l = l' && equiv ty1 ty1' && equiv ty2 ty2'
      | Tpoly (ty, _), Tpoly (ty', _)
      | Tobject (ty, _), Tobject (ty', _)->
        equiv ty ty'
      | Tfield (s, k, ty, rem), Tfield (s', k', ty', rem') ->
        s = s' && k = k' && equiv ty ty' && equiv rem rem'
      | Tnil, Tnil -> true
      | Tvariant _, Tvariant _ ->
        print_debug "NOT MANAGED";
        false
      | _ -> false
  in
  let m' = TyMap.filter (fun k _ -> equiv k ty) ctx.ambivalents in
  TyMap.choose m'

(* let find_equiv_ambi ctx ty args = *)
(*   (\* let module Exn = struct exception Continue of type_expr end in *\) *)
(*   let f ty res = *)
(*     match res with *)
(*       Some ty -> res *)
(*     | None -> *)
(*       try Some (find_equiv_ambi ctx ty args) *)
(*       with Not_noud -> None *)
    

let expand_abbrev ctx ty =
  match (Btype.repr ty).desc with
    Tconstr (p, args, abbrev) ->
    print_debug (Format.asprintf "Expansion of %a (%a)"
      Typecheck_pretty.path p
      (fun fmt -> List.iter (Printtyp.type_expr fmt)) args);
    (try
       match (Env.find_type p ctx.env).type_manifest with
         Some ty ->
         print_debug (Format.asprintf "Manifest: %a"
           Printtyp.type_expr ty)
       | None -> print_debug "No manifest"
    with Not_found -> print_debug "Not found....");
    let vars, ty, _ =
      try Env.find_type_expansion p ctx.env
      with Not_found -> print_debug "Not extensible"; raise Ctype.Cannot_expand
    in
    print_debug (Format.asprintf "==> %a\n%!"
      Typecheck_pretty.Types.type_expr ty);
    apply_args ctx vars args ty p
  | _ ->
    print_debug (Format.asprintf "Cannot expand: %a"
      Printtyp.type_expr ty);
    raise Ctype.Cannot_expand

let rec expand_abbrev_max ctx ty =
  match expand_abbrev ctx ty with
    ty' -> expand_abbrev_max ctx ty'
  (* | exception Ctype.Cannot_expand -> ty *)

let rec safe_expand_abbrev_max ctx ty =
  match expand_abbrev ctx ty with
    ty' -> safe_expand_abbrev_max ctx ty'
  | exception Ctype.Cannot_expand -> ty


module Extract = struct
(** Extraction functions.

*)

type 'a repr =
    Rtuple : type_expr list repr
  | Rvariant : row_desc repr
  | Rarrow : (string * type_expr * type_expr) repr
  | Rpackage : (Path.t * Longident.t list * type_expr list) repr
  | Rpoly : (type_expr list * type_expr) repr
  | Robject : type_expr repr

type 'a extractor = {
  matches: type_expr * 'a repr -> bool;
  extract: type_expr * 'a repr -> 'a;
}

type error +=
  Expected_type_mismatch : _ repr * type_expr -> error

let print_repr (type a) fmt : a repr -> unit = function
    Rtuple -> Format.fprintf fmt "tuple type"
  | Rvariant -> Format.fprintf fmt "variant type"
  | Rarrow -> Format.fprintf fmt "functional type"
  | Rpackage -> Format.fprintf fmt "package type"
  | Rpoly -> Format.fprintf fmt "polymorphic type"
  | Robject -> Format.fprintf fmt "object type"

let extract_repr_newty :
  type a. context -> TySet.t -> type_expr -> a repr -> (a, error) result =
  fun ctx ambty ty r ->
    let module TyTbl = Hashtbl.Make (TypeOps) in
    let visited = TyTbl.create 17 in
    let res: (type_expr * a repr) option =
      TySet.fold (fun ty acc ->
        let ty = Btype.repr ty in
        if TyTbl.mem visited ty then acc
        else begin
          TyTbl.add visited ty ();
          match ty with
            { desc = Tconstr (p, [], _); _ } when is_newtype p -> acc
          | { desc =
                (
                  Tarrow (_, _, _, _)
                | Tpackage (_, _, _)
                | Ttuple _
                | Tvariant _
                | Tpoly (_, _)
                | Tobject (_ ,_)
                ); _ } ->
            begin
              match acc with
                None -> Some (ty, r)
              | Some (ty', r) -> Some ((* less_gen ctx ty *) ty', r)
            end
          | { desc = Tconstr _; _} ->
            begin match safe_expand_abbrev_max ctx ty, acc with
                { desc = Tconstr _; _ } as ty, None -> Some (ty, r)
              | { desc = Tconstr _; _ } as _ty, Some (ty', r) ->
                Some ((* less_gen ctx ty  *)ty', r)
              | _, _ -> acc
            end
          | _ -> acc
        end)
        ambty None in
    match res, r with
      Some ({ desc = Ttuple tys; _ }, Rtuple), Rtuple -> Ok tys
    | Some ({ desc = Tvariant rd; _ }, Rvariant), Rvariant -> Ok rd
    | Some ({ desc = Tarrow (l, ty, ty', _); _ }, Rarrow), Rarrow ->
      Ok (l, ty, ty')
    | Some ({ desc = Tpoly (ty, params); _ }, Rpoly), Rpoly ->
      Ok (params, ty)
    | Some ({ desc = Tpackage (l, lids, tys); _ }, Rpackage), Rpackage ->
      Ok (l, lids, tys)
    | Some ({ desc = Tobject (f, _); _ }, Robject), Robject -> Ok f
    | _ -> Error (Expected_type_mismatch (r, ty))

(* Si newtype : remove newtype pour éviter le cycle, on continue
   Sinon, si constr : expanse
   Sinon si tuple : retourne le tuple  (choisi le less_gen??)
   Sinon on continue*)

let rec extract_type_info :
  type a. context -> a extractor -> a repr -> type_expr -> (a, error) result =
  fun ctx ({ matches; extract } as ex) r ty ->
    match Btype.repr ty with
      ty when matches (ty, r) -> Ok (extract (ty, r))
    | { desc = Tconstr (p, [], _); } as ty when gadt_mode ctx p ->
      let ty_repr, ambi = find_equiv_ambi ctx ty [] in
      extract_repr_newty ctx ambi.value ty r
    | { desc = Tconstr _; _ } ->
      expand_abbrev ctx ty |> extract_type_info ctx ex r
    | p -> Error (Expected_type_mismatch (r, ty))

let extract_tuple_info ctx ty =
  extract_type_info ctx {
    extract = (function ({desc = Ttuple tys}, Rtuple) -> tys
                      | _, _ -> assert false);
    matches = (function ({desc = Ttuple _}, Rtuple) -> true
                      | _, _ -> false)
  } Rtuple ty

let extract_variant_info ctx ty =
  extract_type_info ctx {
    extract = (function ({desc = Tvariant rd}, Rvariant) -> rd
                      | _, _ -> assert false);
    matches = (function ({desc = Tvariant _}, Rvariant) -> true
                      | _, _ -> false)
  } Rvariant ty

let extract_poly_info ctx ty =
  extract_type_info ctx {
    extract = (function ({desc = Tpoly (ty, params)}, Rpoly) -> params, ty
                      | _, _ -> assert false);
    matches = (function ({desc = Tpoly _}, Rpoly) -> true
                      | _, _ -> false)
  } Rpoly ty

let extract_arrow_info ctx ty =
  extract_type_info ctx {
    extract = (function ({desc = Tarrow (l, ty, ty', _)}, Rarrow) -> l, ty, ty'
                      | _, _ -> assert false);
    matches = (function ({desc = Tarrow (_, _, _, _)}, Rarrow) -> true
                      | _, _ -> false)
  } Rarrow ty

let extract_package_info ctx ty =
  extract_type_info ctx {
    extract = (function
          ({desc = Tpackage (p, lids, tys)}, Rpackage) -> p, lids, tys
        | _, _ -> assert false);
    matches = (function
          ({desc = Tpackage (_, _, _)}, Rpackage) -> true
        | _, _ -> false)
  } Rpackage ty

let extract_object_info ctx ty =
  extract_type_info ctx {
    extract = (function
          ({desc = Tobject (f, _)}, Robject) -> f
        | _, _ -> assert false);
    matches = (function
          ({desc = Tobject (_, _)}, Robject) -> true
        | _, _ -> false)
  } Robject ty



let find_meth ctx loc meth priv ty =
  (* Simple version *)
  print_debug
    (Format.asprintf "find_meth %s in %a"
       meth Printtyp.raw_type_expr ty);
  let f = match extract_object_info ctx ty with
      Ok f -> f
    | Error e -> failwith "Error"
  in
  let rec find f =
    match (Btype.repr f).desc with
      Tfield (s, k, ty, rem) ->
      if meth = s then ty else find rem
    | Tvar _ | Tnil -> assert false (* raise (Class_error (Undeclared_method s, loc)) *)
    | _ -> assert false (* raise (Class_error (Illformed_object_type ty, loc)) *)
  in
  find f
    
end

(** *)

let expand_modtype_path ctx path =
  (* If module is M(A1)(A2)(...)(An), expand the application ->
     generate the signature by substituting each Xi by Ai in M, assuming M has
     type `functor (Xi : Si) ... -> M`.
     The resulting signature can be used to type types and module types
     resulting from functors applications. Motivated by complex examples in
     tests/girard.ml from Leo White.
  *)
  let open Path in
  let rec expand path subst =
    print_debug
      (Format.asprintf "expand_path: %a" Printtyp.path path);
    let md = Env.find_module path ctx.env in
    print_debug
      (Format.asprintf "expand_path: found: %a"
         Printtyp.modtype md.md_type);
    let mty = match path with
    (*   Pident id -> Subst.modtype subst md.md_type *)
    (* | Pdot (p, sub, _) -> *)
    (*   let mty = expand p subst in *)
    (*   print_debug "pdot"; *)
    (*   (\* search sub in module and returns it *\) *)
    (*   let md = find_module_mty ctx sub mty in *)
    (*   md.md_type *)
    | Papply (p1, p2) ->
      begin
        match Env.scrape_alias ctx.env @@expand p1 subst with
        | Mty_functor (id, _, mty) ->
          Subst.modtype (Subst.add_module id p2 subst) mty
        | mty ->
          Format.printf "orig_path:%a; %a\n%!" Printtyp.path path Printtyp.modtype mty;
          assert false
      end
    | _ -> md.md_type
    in
    print_debug
      (Format.asprintf "Result: %a" Printtyp.modtype mty);
    mty
  in
  let expanded =
    match path with
      Pdot(p, sub, _) ->
      print_debug "Pdot -> expand";
      let mty = expand p Subst.identity in
      print_debug (Format.asprintf "expand res: %a" Printtyp.modtype mty);
      (* search modtype `sub` and returns i *)
      let _, mtd = find_modtype_mty ctx sub mty in
      mtd.mtd_type
    | Pident id ->
      print_debug "Pident -> find";
      let mtd = Env.find_modtype path ctx.env in
      mtd.mtd_type
    | Papply (_, _) -> assert false
(* Functor application cannot produce a module type directly *)
  in
  match expanded with
    Some mty -> mty
  | None -> raise Ctype.Cannot_expand

let try_expand_mty_path ctx mty =
  match mty with
    Mty_alias p | Mty_ident p ->
    (try expand_modtype_path ctx p
     with Ctype.Cannot_expand -> mty)
  | _ -> mty

(* Binded variables environment *)

module Variables = struct
  module SMap = Map.Make(String)

  type variables =
    {
      univars : Types.type_expr SMap.t;
      (* pre_univars : Types.type_expr list; *)
      vars : Types.type_expr SMap.t;
    }

  let empty_variables = {
    univars = SMap.empty;
    (* pre_univars = []; *)
    vars = SMap.empty
  }

  (* Hack used when typing classes to allow the correct use of type parameters *)
  let curr_vars = ref (empty_variables, true)
  let set_curr_vars vars gen =
    let prev_vars = !curr_vars in
    curr_vars := vars, gen;
    fun () -> curr_vars := prev_vars

  let print fmt vs =
    Format.fprintf fmt "vars: [%a]\nunivars: [%a]"
      (fun fmt vs -> SMap.iter (fun v ty ->
           Format.fprintf fmt "%s -> %a"
             v Printtyp.raw_type_expr ty) vs)
      vs.vars
      (fun fmt vs -> SMap.iter (fun v ty ->
           Format.fprintf fmt "%s -> %a"
             v Printtyp.raw_type_expr ty) vs)
      vs.univars
end

(** Class related functions *)

let get_row_type ty =
  let rec find ty =
    let ty = Btype.repr ty in
    match ty.desc with
      Tfield (_, _, _, ty) -> find ty
    | _ -> ty
  in
  match (Btype.repr ty).desc with
    Tobject (fi, _) -> find fi
  | _               -> assert false

type class_env =
  { val_env: Env.t;
    meth_env: Env.t;
    par_env: Env.t;
    vars: (Ident.t * Asttypes.mutable_flag *
           Asttypes.virtual_flag * type_expr) Vars.t ref;
    meths: (Ident.t * type_expr) Meths.t ref;
    ctx: context;
    tvars: Variables.variables;
    substs : type_expr TyMap.t;
  }

let new_cl_env ctx tvars =
  { val_env = ctx.env; meth_env = ctx.env; par_env = ctx.env;
    vars = ref Vars.empty; meths = ref Meths.empty;
    ctx; tvars;
    substs = TyMap.empty;
  }

type internal_class_context =
  { concr_meths : Concr.t;
    concr_vals : Concr.t;
    inherited : (Path.t * type_expr list) list;
    local_vals : Concr.t;
    local_meths : Concr.t;
  }

let empty_class_context =
  { concr_meths = Concr.empty;
    concr_vals = Concr.empty;
    inherited = [];
    local_vals = Concr.empty;
    local_meths = Concr.empty;
  }


let print_error fmt = function
  | Extract.Expected_type_mismatch (repr, ty) ->
    Format.fprintf fmt
      "Expected a %a, got %a."
      Extract.print_repr repr Printtyp.type_expr ty
  | _ ->
    Format.fprintf fmt
      "Error: unknown"
