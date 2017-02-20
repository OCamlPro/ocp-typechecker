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

let safe_open_in f file =
  try
    let ic = open_in file in
    let r = try Ok (f ic) with e -> Error e in
    close_in ic;
    r
  with e -> Error e

let safe_open_out_gen mode perm f file =
  try
    let oc = open_out_gen mode perm file in
    let r = try Ok (f oc) with e -> Error e in
    close_out oc;
    r
  with e -> Error e

let safe_open_out f file =
  safe_open_out_gen
    [Open_wronly; Open_creat; Open_trunc; Open_text] 0o666 f file
