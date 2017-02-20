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

open Typecheck_result

type filename = string

val safe_open_in : (in_channel -> 'a) -> filename -> ('a, exn) result

val safe_open_out : (out_channel -> 'a) -> filename -> ('a, exn) result
