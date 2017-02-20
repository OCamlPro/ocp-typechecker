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

open List

module M = struct
  let f = fun x -> x
  let length = List.length
end

open! M

let f' = f

let length = length

module S =
struct
  type t = int
end

module type T =
sig
  open S
  type s = t
end

module P =
struct
  let g x = x + 1
end

let f x =
  let open P in
  g x
