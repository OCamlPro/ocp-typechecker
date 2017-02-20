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

(** Exported functions from Typecore

    Only short/trivial functions, to avoid as long as possible to directly
    modify the interface of Typecore *)

open Typecheck_ctype
open Asttypes
open Types

(* Typing of constants *)

let type_constant = function
    Const_int _ -> instance_def Predef.type_int
  | Const_char _ -> instance_def Predef.type_char
  | Const_string _ -> instance_def Predef.type_string
  | Const_float _ -> instance_def Predef.type_float
  | Const_int32 _ -> instance_def Predef.type_int32
  | Const_int64 _ -> instance_def Predef.type_int64
  | Const_nativeint _ -> instance_def Predef.type_nativeint
