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

let g (x : int) = x (* int <: 'a*)

let g' (x : 'a) = x (* 'a <: 'a *)

let g'' (x : 'a) = x + 1

let g''' (x : 'a) = (x : int)

let h (x : int) (y: int) = (x, y)

let f = fun (type a) x -> (x : a)

let f2 (type a) (type b) (f' : a -> b) x = f' x

let g2 : (int as 'a) -> 'a = fun x -> x

let v : [ `A of int ] = `A 2

let i : 'a. 'a -> 'a = fun x -> x

let g3 = i 1, f true

let j : _ -> int = fun x -> 0
