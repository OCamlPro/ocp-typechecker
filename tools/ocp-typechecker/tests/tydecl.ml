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

type t0 = int

type t1 = Int | Bool

type 'a t2 = T2 of 'a

type 'a t3 = List of 'a constraint 'a = 'b list

let list l = List l

type _ t4 = T4 : 'a -> 'b t4

type t5 = Val of int | End
and t6 = Left of int | Right of int

type t7 = { v : int }

type t8 = { p : 'a. 'a -> 'a }

let p = { p = fun x -> x }
