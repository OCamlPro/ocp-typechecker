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

type (_, _) eq = Eq : ('a, 'a) eq

let cast : type a b. (a, b) eq -> a -> b = fun eq v ->
  match eq with Eq -> v

(* [@@@debug] *)
let trans : type a b c. (a, b) eq -> (b, c) eq -> (a, c) eq =
  fun e1 e2 ->
    match e1, e2 with Eq, Eq -> Eq

let sym : type a b. (a, b) eq -> (b, a) eq = function Eq -> Eq

type t = int

let t_int : (t, int) eq = Eq

let x_t = cast (sym t_int) 42
let x_int = cast t_int 42
