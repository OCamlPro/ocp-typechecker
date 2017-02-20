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

type zero = unit
type 'a succ = unit -> 'a
type one = zero succ

type 'a plus_1 = 'a succ
type 'a plus_2 = 'a plus_1 plus_1
type 'a plus_4 = 'a plus_2 plus_2
type 'a plus_8 = 'a plus_4 plus_4
type 'a plus_16 = 'a plus_8 plus_8
type 'a plus_32 = 'a plus_16 plus_16

type 'a plus_31 = 'a plus_1 plus_2 plus_4 plus_8 plus_16
type 'a plus_63 = 'a plus_31 plus_32

type s_31 = zero plus_31
type s_63 = zero plus_63

type (_, _, _) size =
  | Zero : ('a, 'a, zero) size
  | Succ : ('a, 'b, 'c) size -> ('a succ, 'b, 'c succ) size

let s_1 v = Succ v
let s_2 v = s_1 (s_1 v)
let s_4 v = s_2 (s_2 v)
let s_8 v = s_4 (s_4 v)
let s_16 v = s_8 (s_8 v)
let s_32 v = s_16 (s_16 v)

let t_31 _ = s_16 @@ s_8 @@ s_4 @@ s_2 @@ s_1 @@ Zero
let t_63 _ = s_32 @@ t_31 ()

let t_28 _ = s_16 @@ s_8 @@ s_4 @@ Zero

type ('in_size, 'out_size, 'field_size, 'field_type) field =
  | Bool : ('a, 'a succ, one, bool) field
  | Int : ('b, 'a, 'c) size -> ('a, 'b, 'c, int) field

type ('a, 'b, 't) packed =
  | End : (zero, 'b, 'b, 't) field -> ('b, 'b, 't) packed
  | Acc : ('a, 'b, 'c, 't) field * ('a, 's, 'rt) packed -> ('b, 'c * 's, 't * 'rt) packed

type _ seal_size =
  | Seal31 : s_31 seal_size
  | Seal63 : s_63 seal_size

type ('sizes, 'types) t = T : 'a seal_size * ('a, 'sizes, 't) packed -> ('sizes, 't) t

let rec size_to_int : type a b c. (a, b, c) size -> int = ((function
  | Zero -> 0
  | Succ n -> 1 + (size_to_int n)))
  (* [@@debug] *)

(* 2 ^ size - 1 *)
let rec size_to_mask : type a b c. (a, b, c) size -> int = function
  | Zero -> 0
  | Succ n -> 1 + ((size_to_mask n) lsl 1)

let get_field : type in_s out_s f_s f_t. pos:int -> input:int -> (in_s, out_s,
  f_s, f_t) field -> f_t * int =
  fun ~pos ~input field ->
    match field with
    | Bool ->
      ((input lsr pos) land 1 == 1), pos + 1
    | Int size ->
      let mask = size_to_mask size in
      let shift = size_to_int size in
      (input lsr pos) land mask, pos + shift

let get_first_field : type in_s out_s f_s f_t. pos:int -> input:int -> (in_s, out_s, f_s, f_t) field -> f_t =
  fun ~pos ~input field ->
    match field with
    | Bool ->
      input lsr pos == 1
    | Int size ->
      input lsr pos

let rec aux_get : type s sl ts. input:int -> (s, sl, ts) packed -> ts * int =
  fun ~input packed ->
    match packed with
    | End field ->
      get_field ~pos:0 ~input field
    | Acc (field, packed) ->
      let tail, pos = aux_get ~input packed in
      let value, pos = get_field ~pos ~input field in
      (value, tail), pos

let get_sealed : type sl ts. input:int -> (sl, ts) t -> ts =
  fun ~input (T (seal_size, t)) ->
    match t with
    | End field ->
      get_first_field ~pos:0 ~input field
    | (Acc(field, fields) (* [@debug] *)) ->
      let r, pos = aux_get ~input fields in
      let v = get_first_field ~pos:0 ~input field in
      (v, r)

module Test : sig
  val get : int -> int * int * bool
end= struct
  let i5 _ = Int (s_4 @@ s_1 Zero)
  let i6 _ = Int (s_4 @@ s_2 Zero)
  let i7 _ = Int (s_4 @@ s_2 @@ s_1 Zero)
  let i8 _ = Int (s_8 Zero)
  let i13 _ = Int (s_8 @@ s_4 @@ s_1 Zero)

  let rgba = T (Seal31, (Acc (i7 (), (Acc (i8 (), (Acc (i8 (), (End (i8
  ())))))))))
  let stuff = T (Seal31, Acc (i13 (), (Acc (i8 (), (Acc (Bool, (Acc (i8 (), (End Bool)))))))))

  let get input =
    let (a, (b, (c, (d, e)))) = get_sealed ~input stuff in
    a, d, e
end

(* (\* get: *)
(* flambda: *)
(* (set_of_closures (fun Test_gadt.get/1287 Test_gadt.input/1290 *)
(*   (let *)
(*     (Test_gadt.block_field/1820 (== (and (lsr Test_gadt.input/1290 0) 1) 1) *)
(*      Test_gadt.block_field/1863 (and (lsr Test_gadt.input/1290 1) 255) *)
(*      Test_gadt.v/1682 (lsr Test_gadt.input/1290 0)) *)
(*     (makeblock 0 Test_gadt.v/1682 Test_gadt.block_field/1863 *)
(*       Test_gadt.block_field/1820))) ) *)

(* cmm: *)
(* (function camlTest_gadt__get_1287 (Test_gadt_input/1290: addr) *)
(*  (let *)
(*    (Test_gadt_block_field/1820 *)
(*       (+ (<< (== (and (or Test_gadt_input/1290 1) 3) 3) 1) 1) *)
(*     Test_gadt_block_field/1863 (and (or (>>u Test_gadt_input/1290 1) 1) 511) *)
(*     Test_gadt_v/1682 (or Test_gadt_input/1290 1)) *)
(*    (alloc 3072 Test_gadt_v/1682 Test_gadt_block_field/1863 *)
(*      Test_gadt_block_field/1820))) *)

(* amd64 assembly: *)
(* camlTest_gadt__get_1287: *)
(* 	.cfi_startproc *)
(* 	subq	$8, %rsp *)
(* 	.cfi_adjust_cfa_offset 8 *)
(* .L100: *)
(* 	movq	%rax, %rbx *)
(* 	movq	%rbx, %rdi *)
(* 	orq	$1, %rdi *)
(* 	movq	%rdi, %rax *)
(* 	andq	$3, %rax *)
(* 	cmpq	$3, %rax *)
(* 	sete	%al *)
(* 	movzbq	%al, %rax *)
(* 	leaq	1(%rax,%rax), %rsi *)
(* 	shrq	$1, %rbx *)
(* 	orq	$1, %rbx *)
(* 	andq	$511, %rbx *)
(* .L101: *)
(* 	subq	$32, %r15 *)
(* 	movq	caml_young_limit@GOTPCREL(%rip), %rax *)
(* 	cmpq	(%rax), %r15 *)
(* 	jb	.L102 *)
(* 	leaq	8(%r15), %rax *)
(* 	movq	$3072, -8(%rax) *)
(* 	movq	%rdi, (%rax) *)
(* 	movq	%rbx, 8(%rax) *)
(* 	movq	%rsi, 16(%rax) *)
(* 	addq	$8, %rsp *)
(* 	.cfi_adjust_cfa_offset -8 *)
(* 	ret *)
(* 	.cfi_adjust_cfa_offset 8 *)
(* .L102: *)
(* 	call	caml_call_gc@PLT *)
(* .L103: *)
(* 	jmp	.L101 *)
(* *\) *)

let n =
  let v = 0x1234567890123456 in
  let r = ref 0 in
  for i = 0 to 10000000 do
    let a, b, _ = Test.get v in
    r := !r + a + b;
  done;
  !r

let () =
  (Printf.printf "res: %i\n%!" n)

(* ocamlopt -inline 10000: ~1s *)
(*    flambda -inline 100 -unroll 5 -rounds 5: ~5ms *)
