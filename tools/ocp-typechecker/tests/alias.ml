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

module S = String

module StringSet = Set.Make(String)
module SSet = Set.Make(S)

let hello =
  StringSet.add "hello" SSet.empty

let world =
  SSet.add "world" StringSet.empty

let hello_world =
  SSet.union hello world
