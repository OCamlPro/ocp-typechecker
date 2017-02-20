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

(* Union-find structure that allows to verify that two paths are equivalent
   when chechking that two type constructors are equivalent *)

(* See github.com/pcouderc/union_find.ml for the original implementation, which
   is highly inspired from:
   - A persistent Union-Find Data Structure S. Conchon
   and J.C. Filliatre *)

(* Resizable arrays *)
module ResArray =
struct
  type 'a t =
    { mutable t : 'a array;
      init : int -> int }

  let init n f = { t = Array.init n f; init = f }

  let rec new_size curr i =
    if i < curr then curr else
      new_size (curr*2) i

  let on_resize init t i =
    let s = Array.length t in
    if i < s then Array.get t i else init i

  let get t i =
    if i >= Array.length t.t then
      begin
        t.t <- Array.init
            (new_size (Array.length t.t) i)
            (on_resize t.init t.t)
      end;
    Array.get t.t i

  let set t i v =
    if i > Array.length t.t then
      t.t <- Array.init
          (new_size (Array.length t.t) i)
          (on_resize t.init t.t);
    Array.set t.t i v
end

module PArray = struct

  module Array = ResArray

  type 'a t = 'a data ref
  and 'a data =
  | Arr of 'a Array.t
  | Diff of int * 'a * 'a t

  let init n f = ref (Arr (Array.init n f))

  let rec reroot t =
    match !t with
    | Arr _ -> ()
    | Diff (i, v, t') ->
      reroot t';
      begin match !t' with
      | Arr a as n ->
        let v' = Array.get a i in
        Array.set a i v;
        t := n;
        t' := Diff (i, v', t)
      | Diff _ -> assert false
      end

  let rec get t i = match !t with
    | Arr a -> Array.get a i
    | Diff (j, v, t') ->
      reroot t';
        begin match !t' with
        | Arr a -> Array.get a i
        | Diff _ -> assert false
        end

  let set t i v =
    reroot t;
    match !t with
    | Arr a as n ->
      let old = Array.get a i in
      Array.set a i v;
      let res = ref n in
      t := Diff (i, old, res);
      res
    | Diff _ -> assert false

end


type t = {
  rank : int PArray.t;
  mutable parent : int PArray.t
}

let init_rank _ = 0
let init_parent i = i

let create n = {
  rank = PArray.init n init_rank;
  parent = PArray.init n init_parent;

}

let rec find_aux parents i =
  let father = PArray.get parents i in
  if i == father then
    parents, i
  else
    let parents, result = find_aux parents father in
    let parents = PArray.set parents i result in
    parents , result


let find h x =
  let parents, cx = find_aux h.parent x in
  h.parent <- parents;
  cx

let union h x y =
  let repr_x = find h x in
  let repr_y = find h y in
  if repr_x != repr_y then begin
    let rank_x = PArray.get h.rank repr_x in
    let rank_y = PArray.get h.rank repr_y in
    if rank_x > rank_y then
      { h with parent = PArray.set h.parent repr_y repr_x }
    else if rank_x < rank_y then
      { h with parent = PArray.set h.parent repr_x repr_y }
    else
      { rank = PArray.set h.rank repr_x (rank_x + 1);
        parent = PArray.set h.parent repr_y repr_x }
  end
  else h
