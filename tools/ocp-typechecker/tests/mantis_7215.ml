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

type (_,_) eq = Refl : ('a, 'a) eq
let cast (type a) (type b) (Refl : (a, b) eq) (x : a) = (x : b)

let is_int (type a) =
  let rec (p : (int, a) eq) = match p with Refl -> Refl in
  p

(* let bang = print_string (cast (is_int : (int, string) eq) 42) *)

type (_, _) int' = Int : (int, int) int'

let cast (type a) (type b) (Int : (a, b) int') (x : a) = (x : b)
