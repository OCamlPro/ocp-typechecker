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

let revapply x f = f x

module Contravariant : sig
  type -'a t
  val create : unit -> [< `Foo] t
end = struct
  type 'a t = unit
  let create () = ()
end

module M : sig
  val int_to_string : [ `Bar of int ] -> string
end = struct
  let int_to_string x =
    let x =
      revapply x (fun (`Bar int) -> (`Bar int), Contravariant.create ())
    in
    revapply x (fun ((`Bar int), _) -> (int : string))
end

let () = Printf.printf "%s" (M.int_to_string (`Bar 0))
