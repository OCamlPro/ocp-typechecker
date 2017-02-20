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

type t = ..

module type S = sig
  type t += M of int
  val v : t
  type t += N of bool
end

module M1 (* : S *) = struct
  type t += M of int | N of bool
  let v = N true
end

type u = ..

module U = struct
  type t += U
  (* type u += U *) (* Forbidden since 4.03 *)
end

type t += V
(* type u += V *) (* Forbidden since 4.03 *)

module type E = sig
  exception X
  (* type t += X *)
end

let f x = match x with
    U.U -> 0
  | V -> 1
  | _ -> -1
