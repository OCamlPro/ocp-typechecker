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

let seq (f: 'a -> unit) g x =
  f x; f x; g x

let while_do p f v =
  let value = ref v in
  while p !value do
    value := f !value
  done;
  !value

let for_do init last (f : int -> unit) =
  for i = init to last do
    f i
  done
