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

let a = `A 42

let b x = `A x

let c v = match v with
    `A _ -> 1
  | `B x -> x

let f = function
    `C -> 0
  | _ -> 1

let g = function
    `A -> a
  | `B x -> b x
  | `C -> `C

let a' = b 2

(* Inheritance *)
type t = [ `C | `D ]

let x : [ | t ] = `C
