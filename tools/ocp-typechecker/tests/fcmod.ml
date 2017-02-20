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

module type S = sig
  type t
  val x : t
end

module M : S = struct
  type t = int
  let x = 42
end

(* M :> S *)

let m =
  let module M = struct let create () = 42 end in
  M.create ()

(* Takes a module and returns it. The annotation "with type t = a" ensures that
   the type the module returns is compatible with the one given *)
let f : 'a. (module S with type t = 'a) -> (module S with type t = 'a) =
  fun m -> m

let f' (module M : S) = ()

let m2 = (f (module M))

let equals () =
  let module M1 : S = M in
  let module M2 = (val f (module M1)) in
  M1.x = M2.x

module M2 = (val m2)

let () =
  ignore @@ (M2.x = M.x)
