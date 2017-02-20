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

module T  = struct end

module T2 = struct type t = int end

module T3 = functor (M : sig type t end) ->
struct
  type t = M.t
end

module T3' = T3(T2)

(* eta-expansion + application *)
module T4 = (functor (M : sig type t end) -> T3(M)) (T2)

module T5 = struct module M = struct type t end end

module T6 = T5

(* Modtypes *)
module type S = sig end

module type S2 = sig type s end

module M : S2 = struct type s = int end

module type S2' = sig
  type t
  val x : t
end

module M' : S2' = struct
  type t = int
  let x = 0
end

module type Fun = functor (P : S2) -> sig
  type t = P.s
end

module type T4Sig = module type of T4

(* Abstrast module type *)
module type S3 = sig module type S3' end

module M3 : S3 = struct module type S3' end

(* With constraints *)

module M4 : S2 with type s = int =
  struct type s = int end

module type S5 = sig
  type t
  val make : int -> t
end

module M5 : S5 with type t := int =
struct
  let make i = i
end


(* With module constraints *)
module type S6 = sig
  module M' : sig type t end
  val f : M'.t -> M'.t
end

module M6Subst : S6 with module M' := T2 =
struct
  let f x = x
end

module M6' : S6 with module M' = T2 =
struct
  module M' = struct type t = int end
  let f x = x
end

(* Modules with abbrev *)

module type S7 = sig
  type t = int
end

module M7 : S7 = struct
  type u = int
  type t = u
end

(* module M8 = struct *)
(*   let x = true *)
(*   let x = 2 *)
(* end *)
