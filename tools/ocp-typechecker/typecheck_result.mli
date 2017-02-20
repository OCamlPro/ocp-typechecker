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

type ('a, 'b) result = Ok of 'a | Error of 'b

val return : 'a -> ('a, 'b) result

val bind : ('a, 'b) result -> ('a -> ('c, 'b) result) -> ('c, 'b) result

val (>>=) : ('a, 'b) result -> ('a -> ('c, 'b) result) -> ('c, 'b) result

val get : ?fail:('b -> 'a) -> ('a, 'b) result -> 'a
