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

let f = object (self)
  method m = 42
end

let f' = object (self)
  method m = 42 + self#n
  method private n = 2
end

let g = object (self)
  method p x = x + 1
  method r c = self#p c
end

let e = object
  method m : 'a. 'a -> 'a = fun x -> x
  method n = 2
end

let h = object (self : < m : int; .. >)
  method m = 42
  method n = 2
end

(* simple class, no instance variable *)
class p = object
  method m y = y + y
end

(* class with instance variable *)
class p' v = object
  val x : int = v
  method m = x
end

class ['a] x =
  let v : 'a -> 'a = fun x -> x in
  object
    method m = v
  end

(* class with type parameter *)
class ['a] id = object
  method id : 'a -> 'a = fun x -> x
end
let x = let o : 'a id = object method id x = x end in o

(* class with polymorphic instance variable *)
class ['a] q (v : 'a) = object
  val x = v
  method m = x
end

(* class with mutually recursive methods *)
class n = object (self)
  method rec1 b = if b then self#rec2 false else "rec1"
  method rec2 b = if b then self#rec1 false else "rec2"
end

(* let p1 = new p *)
(* let p2 = new p' 2 *)
(* let q = new q 3 *)
(* let n = new n *)


class m = object (self)
  val z = 42
  method x () = print_endline "Hello world!"
  method y = object val x = z end
end

(* class o v = object (self : < m : int -> int; .. >) *)
(*   val i = ref v *)
(*   method m j = i := !i + j; !i *)
(*   method copy () = {< >} *)
(* end *)

(* let o1 = new o 2 *)
(* let o2 = o1#copy () *)

(* Class types *)
class type t = object
  method m : int -> int
end

class type t2 = t

class type t3 = object
  inherit t
end

class type ['a] t4 = object
  method p : 'a -> 'a
end

class type t5 = object
  inherit [int] t4
end

class type t6 = object (< m : int; .. >)
  method m : int
  method n : int -> int
end
