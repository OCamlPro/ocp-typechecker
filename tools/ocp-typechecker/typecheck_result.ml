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

let return v = Ok v

let bind : 'a 'b 'c. ('a, 'c) result -> ('a -> ('b, 'c) result) -> ('b, 'c) result =
  fun v f ->
    match v with
      Ok v' -> f v'
    | Error e -> Error e

let (>>=) = bind

let get ?(fail=fun _ -> failwith "Error result") = function
    Ok res -> res
  | Error e ->
    (* Printf.printf "Error: %s.\n%!" @@ Printexc.to_string exn; *)
    fail e
