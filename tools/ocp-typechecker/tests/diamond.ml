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

(* Some functors applications resulting in two module types that are
   equivalent.
   Not ready yet, still needs to figure out what must be a good example.
*)

module type S = sig
  module type T
end

module S : S = struct
  module type T
end

module M1 = struct
  include S
end

module M2 (Arg: S) = struct
  include Arg
end

module Compare (A1: S) (A2: S) = struct
  include A1
end

module R1 = Compare(M1)(M2(S))
