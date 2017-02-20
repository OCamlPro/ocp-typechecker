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

type ex = Ex : 'b -> ex

let ex_int = Ex 42
let ex_bool = Ex true
let eq = ex_int = ex_bool

let extract = (function
  (Ex i (* [@debug] *)) -> ignore i)

let f x =
  let f' : 'a. 'a -> 'a = fun x -> x in
  f' x

module type P = sig val x : int end

type _ t =
    Int : int -> int t
  | Bool : bool -> bool t
  | Pair : 'a t * 'b t -> ('a * 'b) t
  | Fun : ('a -> 'b) -> ('a -> 'b) t
  | Fun2 : 'a t * 'b t -> ('a -> 'b) t
  | Variant : ([`A of 'a] as 'var) -> 'var t
  | Mod : ((module P) as 'm) -> 'm t
  | Obj : (< m : int -> int > as 'obj) -> 'obj t


(* [@@@debug] *)
let rec return : type a. a t -> a = (function
  | (Pair (x, y))-> (return x, return y)
  | Int i -> i
  | Bool b -> b
  | Fun f -> f
  | Fun2 (arg, res) -> (fun x -> let _ = x = return arg in return res)
  | Variant (`A x) -> `A x
  | Mod p -> let module P = (val p) in (module P)
  | Obj o -> (object method m = o#m end )
  )

let i = return (Int 0)
let f = return (Fun2 (Fun2 (Int 2, Int 2), Int 2))
let f' = return (Fun2 (Int 2, Fun2 (Int 3, Bool true)))

type _ u = Ex : 'c * 'b -> 'b u

let g : type b. b u -> int = function
  (Ex (x, y) (* [@debug] *)) -> 42


type _ v = V : 'a * 'b -> ('a * 'b) v

let h : type a. a v -> int = function
  (V (x, y) (* [@debug] *)) -> 42
