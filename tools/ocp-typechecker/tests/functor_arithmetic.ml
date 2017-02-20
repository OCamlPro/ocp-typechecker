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

type 'a nat =
  | Zero : unit nat
  | Succ : 'a nat -> (unit -> 'a) nat

type zero = unit
type 'a succ = unit -> 'a

type ('a, 'b, 'c) add =
  | Add_Z : (zero nat, 'a nat, 'a nat) add
  | Add_S : ('a nat, 'b nat, 'c nat) add ->
    ('a succ nat, 'b nat, 'c succ nat) add

module type Base = sig

  type 'a cons

  module type T = sig
    type t
    type x = t cons
    val v : x
  end

end

module Make(A:Base) = struct

  module type Rec = functor (T:A.T) -> A.T
  module type Nat = functor (M:Rec) -> functor (R:A.T) -> A.T

  module Zero
    (* : functor(M:Rec) -> functor (R:A.T) -> A.T with type t = R.t *)
    = functor(M:Rec) -> functor (R:A.T) -> R

  module Succ
    (* : functor(N:Nat) -> functor(S:Rec) -> functor (R:A.T) -> A.T with type t = S(N(S)(R)).t *)
    = functor (N:Nat) -> functor(M:Rec) -> functor (R:A.T) -> M(N(M)(R))

  (* module One : A = Succ(Zero) *)

  module Add
    (* : functor (X:Nat) -> functor (Y:Nat) -> *)
    (* functor(S:Rec) -> functor (R:A.T) -> A.T with type t = X(S)(Y(S)(R)).t *)
    = functor (X:Nat) -> functor (Y:Nat) -> functor (S:Rec) -> functor (R:A.T) ->
      X(S)(Y(S)(R))

  module Mul =
    (* : functor (X:Nat) -> functor (Y:Nat) -> *)
    (* functor(S:Rec) -> functor (R:A.T) -> A.T with type t = X(Y(S))(R).t *)
    functor (X:Nat) -> functor (Y:Nat) -> functor (S:Rec) -> functor (R:A.T) ->
      X(Y(S))(R)

end


module Base = struct
  type 'a cons = 'a nat
  module type T = sig
    type t
    type x = t nat
    val v : t nat
  end
end

module O : Base = Base

module Z : Base.T with type t = zero = struct
  type t = zero
  type x = t nat
  let v = Zero
end

module S(A:Base.T) : Base.T with type t = A.t succ = struct
  type t = (unit -> A.t)
  type x = t nat
  let v = Succ A.v
end

module Nums = Make(Base)

module One = Nums.Succ(Nums.Zero)
module Two = Nums.Add(One)(One)
module Two' = Nums.Succ(One)
module Two'' = Nums.Mul(One)(Two)

(* Test 1 *)
module One_ = One(S)(Z)
module Two_ = Two(S)(Z)
module Two'_ = Two'(S)(Z)
module Two''_ = Two''(S)(Z)

let () = assert(Two_.v = Two'_.v)
let () = assert(Two_.v = Two''_.v)
(* / *)

module N4 = Nums.Add(Two)(Two)
module N8 = Nums.Add(N4)(N4)

module N64 = Nums.Mul(N8)(N8)
module N65 = Nums.Succ(N64)
module N65' = Nums.Add(One)(N64)
module N65'' = Nums.Add(N64)(One)

(* Test 2 *)
module N65_ = N65(S)(Z)
module N65'_ = N65'(S)(Z)
module N65''_ = N65''(S)(Z)

let () = assert(N65_.v = N65'_.v)
let () = assert(N65_.v = N65''_.v)
(* / *)

(* Test 128 *)
module N128 = Nums.Add(N64)(N64)
module N129 = Nums.Add(N128)(One)
module N129' = Nums.Add(One)(N128)

module N129_ = N129(S)(Z)
module N129'_ = N129'(S)(Z)
let () = assert (N129_.v = N129'_.v)

(* Test 256 *)
module N256 = Nums.Add(N128)(N128)
module N257 = Nums.Add(N256)(One)
module N257' = Nums.Add(One)(N256)

module N257_ = N257(S)(Z)
module N257'_ = N257'(S)(Z)
let () = assert (N257_.v = N257'_.v) (* [@debug] *)

(* Test 512 *)
module N512 = Nums.Add(N256)(N256)
(* module N513 = Nums.Add(N512)(One) *)
(* module N513' = Nums.Add(One)(N512) *)

(* module N513_ = N513(S)(Z) *)
(* module N513'_ = N513'(S)(Z) *)
(* let () = assert (N513_.v = N513'_.v) *)

(* Test 1024 *)
module N1024 = Nums.Add(N512)(N512)
(* module N1025 = Nums.Add(N1024)(One) *)
(* module N1025' = Nums.Add(One)(N1024) *)

(* module N1025_ = N1025(S)(Z) *)
(* module N1025'_ = N1025'(S)(Z) *)
(* let () = assert (N1025_.v = N1025'_.v) *)

(* Test 256 *)
module N2048 = Nums.Add(N1024)(N1024)
(* module N2049 = Nums.Add(N2048)(One) *)
(* module N2049' = Nums.Add(One)(N2048) *)

(* module N2049_ = N2049(S)(Z) *)
(* module N2049'_ = N2049'(S)(Z) *)
(* let () = assert (N2049_.v = N2049'_.v) *)

(* Test 256 *)
(* module N4096 = Nums.Add(N2048)(N2048) *)
(* module N4097 = Nums.Add(N4096)(One) *)
(* module N4097' = Nums.Add(One)(N4096) *)

(* module N4097_ = N4097(S)(Z) *)
(* module N4097'_ = N4097'(S)(Z) *)
(* let () = assert (N4097_.v = N4097'_.v) *)

(* Test 3 *)
module N4096m = Nums.Mul(N64)(N64)
(* (\* module N16777216 = Nums.Mul(N4096m)(N4096m) *\) *)

(* module N4097m = Nums.Add(N4096m)(One) *)
(* module N4097m' = Nums.Add(One)(N4096m) *)

(* module N4097m_ = N4097m(S)(Z) *)
(* module N4097m'_ = N4097m'(S)(Z) *)
(* let () = assert (N4097m'_.v = N4097m_.v) *)

(* let () = assert (N4097_.v = N4097m_.v) *)
