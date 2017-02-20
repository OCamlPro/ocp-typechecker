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

type t = A of int * int | B of int * int

let (A (z, y) | B (y, z)) = A (1, 2)

let a as x = 42
let b = 41
let c = "Hello_world"
let d, e = a, b
let id x = x
let g x y =
  x = y
let f x =  match x None with
    Some _ -> 1
  | None -> 0
  | exception Not_found -> -1

let t x =
  try
    42
  with Not_found -> 1

let h = (=) 2

type 'a u = A of 'a * int

let a' = A (1, 2)
