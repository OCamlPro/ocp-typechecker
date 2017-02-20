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

open Typedtree
open Asttypes
open Types
open Typecheck_flags

module SMap = Map.Make(String)
module SSet = Set.Make(String)

let errors : exn list ref = ref []

let create_value_desc ty attr =
  Typecheck_flags.print_debug
    (Format.asprintf "create_value_desc:\n  ty=%a"
       Printtyp.raw_type_expr ty);
  Types.{val_type = ty;
         val_kind = Val_reg;
         val_loc = Location.none;
         val_attributes = attr; }

let create_field label fields closed fixed =
    let row = {
      row_fields = [ label, fields ];
      row_more = Typecheck_ctype.newvar ();
      row_bound = ();
      row_closed = closed;
      row_fixed = fixed;
      row_name = None;
    } in
    Typecheck_ctype.newty (Tvariant row)

let pattern_bindings poly env binded =
  SMap.fold (fun k (ty, id, _) env ->
      let ty = if poly then ty
        else match ty.desc with
            Tpoly (ty, tl) ->
            snd @@ Typecheck_ctype.instance_poly ~keep_names:true true tl ty
          | _ -> ty in
      Env.add_value id (create_value_desc ty []) env) binded env

exception Cannot_extract_exttype_constructor

let extract_constructors env desc =
  print_debug (Format.asprintf "extract_constructor:\n%a"
    Printtyp.raw_type_expr desc.cstr_res);
  match Typecheck_ctype.extract_concrete_typedecl env desc.cstr_res with
  | _, _, { type_kind = Type_variant cstrs; _} -> cstrs
  | _, _, { type_kind = Type_open; _ } -> raise Cannot_extract_exttype_constructor
  | _ -> assert false

let extract_constructor_types ty =
  match Btype.repr ty with
    { desc = Tconstr (_, tys, _); _ } -> tys
  | p -> failwith @@ Format.asprintf"Expected Tconstr, got %a"
      Typecheck_pretty.Types.print_type_simple p.desc

let generate_abstract_decl vars =
  let level = Typecheck_ctype.get_current_level () in
  let decl = {
    type_params = List.map (fun _ -> Typecheck_ctype.newvar ()) vars;
    type_arity = 0;
    type_kind = Type_abstract;
    type_private = Asttypes.Public;
    type_manifest = None;
    type_variance = [];
    type_newtype_level = Some (level, level);
    type_loc = Location.none;
    type_attributes = [];
  } in
  Ident.create "#abstract", decl
(* let begin_def () = *)
(*   Typecheck_flags.print_debug @@ Format.sprintf "begin_def, level: %d" @@ *)
(*   (Ctype.get_current_level () + 1); *)
(*   Ctype.begin_def() *)


(* let end_def () = *)
(*   Typecheck_flags.print_debug @@ Format.sprintf "end_def, level: %d" @@ *)
(*   Ctype.get_current_level (); *)
(*   Ctype.end_def() *)

let new_funtype args res =
  List.fold_left (fun k ty ->
      (fun res -> k @@ Typecheck_ctype.newty (Tarrow ("", ty, res, Cok)))) (fun x -> x) args
  @@ res

let type_option ty =
  Ctype.newty (Tconstr(Predef.path_option,[ty], ref Mnil))

let path_flatten p =
  let rec f acc = function
      Path.Pident id -> Ident.name id :: acc
    | Path.Pdot (p', id, _) -> f (id :: acc) p'
    | Path.Papply (_, _) -> assert false
  in
  f [] p


let may_map f = function
    None -> None
  | Some v -> Some (f v)

let may f = function
    None -> ()
  | Some v -> f v

(* Monadic interface on option type *)
let option_bind v f =
  match v with
    None -> None
  | Some v -> f v

let ( >>? ) = option_bind

let get_opt = function Some s -> s | None -> raise (Invalid_argument "get_opt")

let longident_of_path =
  let open Longident in
  let open Path in
  let rec step = function
      Pident id -> Lident (Ident.name id)
    | Pdot (p, s, _) -> Ldot (step p, s)
    | Papply (p1, p2) -> Lapply (step p1, step p2) in
  step

let rec map3 f m1 m2 m3 =
  match m1, m2, m3 with
    [], [], [] -> []
  | v1 :: t1, v2 :: t2, v3 :: t3 ->
    let v = (f v1 v2 v3) in
    v :: (map3 f t1 t2 t3)
  | _, _, _ -> raise (Invalid_argument "map3")

let rec fold_left3 f acc m1 m2 m3 =
  match m1, m2, m3 with
    [], [], [] -> acc
  | v1 :: t1, v2 :: t2, v3 :: t3 -> (fold_left3 f (f acc v1 v2 v3) t1 t2 t3)
  | _, _, _ -> raise (Invalid_argument "fold_left3")

let rec split3 = function
    [] -> [], [], []
  | (x, y, z) :: rem ->
    let t1, t2, t3 = split3 rem in
    x :: t1, y :: t2, z :: t3

let rec split4 = function
    [] -> [], [], [], []
  | (x, y, z, w) :: rem ->
    let t1, t2, t3, t4 = split4 rem in
    x :: t1, y :: t2, z :: t3, w :: t4

let rec iter3 f m1 m2 m3 =
  match m1, m2, m3 with
    [], [], [] -> ()
  | v1 :: t1, v2 :: t2, v3 :: t3 ->
    f v1 v2 v3;
    iter3 f t1 t2 t3
  | _, _, _ -> raise (Invalid_argument "iter3")

let search_a env =
  if !Typecheck_flags.debug then
    try Env.find_type
          (Path.Pident Ident.({ name = "a"; stamp = 1014; flags = 0 }))
          env |> fun td ->
        Format.printf "manifest: %a\n%!"
          (fun fmt -> function None -> Format.fprintf fmt "None"
                             | Some ty ->
                               Printtyp.type_expr fmt ty)
          td.type_manifest
    with Not_found -> Format.printf "Not_found!\n%!"; ()


let structure_location strc =
  try
    let start_pos = List.hd strc in
    let end_pos = List.fold_left (fun _ x -> x) start_pos strc in
    Location.({
        loc_start = start_pos.str_loc.loc_start;
        loc_end = end_pos.str_loc.loc_end;
        loc_ghost = false;
      })
  with Invalid_argument _ -> Location.none


let signature_location strc =
  try
    let start_pos = List.hd strc in
    let end_pos = List.fold_left (fun _ x -> x) start_pos strc in
    Location.({
        loc_start = start_pos.sig_loc.loc_start;
        loc_end = end_pos.sig_loc.loc_end;
        loc_ghost = false;
      })
  with Invalid_argument _ -> Location.none

exception Found_poly of Typedtree.core_type option

let extract_poly l =
  try List.iter (function
        (Texp_poly cty, _, _) -> raise (Found_poly cty)
      | _ -> ()) l;
    raise Not_found
  with Found_poly cty -> cty
