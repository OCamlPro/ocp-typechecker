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

open Typecheck.IO
open Typecheck.Flags
open Typecheck_result

let if_set flag fmt f v =
  if !flag then f fmt v; Ok v

let code = ref 0

(* let annotated_implementation = *)

let parse_implementation fmt file =
  try Ok (Pparse.parse_implementation fmt ~tool_name file, file)
  with exn -> Error exn

let initial_env modulename =
    Env.set_unit_name modulename;
    Compmisc.init_path false;
    Compmisc.initial_env()

let type_implementation fmt (ast, filename) =
  try
    let outputprefix = Filename.basename @@ Filename.chop_extension filename in
    let modulename = Compenv.module_of_filename fmt filename outputprefix in
    let env = initial_env modulename in
    (* Ctype.init_def(Ident.current_time()); *)
    Typecheck_ctype.init_def(Ident.current_time());
    Clflags.dont_write_files := true;
    let ast, _ =
      Typemod.type_implementation filename outputprefix modulename env ast in
    Ok (ast, modulename)
  with exn -> Error exn

let compute_file fmt filename =
  if Filename.check_suffix filename ".cmt" then
    let open Cmt_format in
    try
      let cmt = read_cmt filename in
      let impl = match cmt.cmt_annots with
          Implementation s -> s
        | _ -> assert false in
      Ok (impl, cmt.cmt_modname)
    with exn -> Error exn
  else if Filename.check_suffix filename ".ml" then
    parse_implementation fmt filename
    >>= type_implementation fmt
  else
    Error (Invalid_argument
             (Printf.sprintf "Unsupported extension of %s" filename))

let print_typedtree fmt (ast, str) =
  Printtyped.implementation fmt ast

let print_annotated_typedtree fmt (ast, modulename) =
  Format.fprintf fmt "module %s = %a\n\n%!" modulename
    Typecheck.Pretty.structure ast

let print_filename_header fmt file result =
  Format.fprintf fmt "(* %s *)\n%!" file; Ok result

let typecheck_typedtree fmt (ast, modname) =
  if !typecheck then begin
    Typecheck_ctype.init_def(Ident.current_time());
    let env = initial_env modname in
    (* Misc.debug := !Typecheck.Flags.debug; (\* Only available in the modified *)
    (*                                          compiler-libs *\) *)
    let sg, _ =
      Typecheck.Typemod.type_structure
        (Typecheck_types.create_context env) None ast in
    (* Misc.debug := false; *)
    Printtyp.signature fmt sg
  end;
  Ok ast

let type_typedtree fmt file =
  compute_file fmt file
  >>= print_filename_header fmt file
  >>= if_set print_dtypedtree fmt print_typedtree
  >>= if_set print_annotated fmt print_annotated_typedtree
  >>= typecheck_typedtree fmt

let type_typedtree' fmt file =
  type_typedtree fmt file
  >>= (fun _ -> Format.fprintf fmt "\n%!"; Ok ())

let print_exn' fmt exn =
  try Location.report_exception fmt exn
  with exn -> Format.fprintf fmt "Uncatched exn: %s" @@
    Printexc.to_string exn

let print_trace fmt tr =
  Format.fprintf fmt "Ctype.Unify:\n";
  List.iter (fun (t1, t2) ->
      Format.fprintf fmt "%a <> %a\n"
        Printtyp.raw_type_expr t1
        Printtyp.raw_type_expr t2) tr

let print_exn fmt exn =
  match exn with
    Typecheck_expr.Expr_error e -> Typecheck_expr.print_error fmt e
  | Typecheck_typing.Typing_error e -> Typecheck_typing.print_error fmt e
  | Typecheck_typexpr.Typexpr_error e -> Typecheck_typexpr.print_error fmt e
  | Typecheck_typedecl.Typedecl_error e -> Typecheck_typedecl.print_error fmt e
  | Typecheck_typemod.Typemod_error e -> Typecheck_typemod.print_error fmt e
  | Typecheck_class.Class_error e -> Typecheck_class.print_error fmt e
  | Ctype.Unify trace -> print_trace fmt trace
  | x -> print_exn' fmt x

  (* try Location.report_exception fmt exn *)
  (* with exn -> *)
  (*   Printexc.to_string exn |> Format.fprintf fmt "%s\n%!" *)

let print_exn_with_backtrace ~with_bt fmt exn bt =
  let print_bt fmt bt =
    if with_bt then Format.fprintf fmt "%s\n" bt in
  Format.fprintf fmt "%a\n\n%a" print_exn exn print_bt bt

let annotate_files fmt files =
  let with_bt = !backtrace in
  let fail e = raise e in
  List.iter
    (fun f -> try
        get ~fail @@ type_typedtree' fmt f
      with exn ->
        code := 2;
        print_exn_with_backtrace
          ~with_bt Format.std_formatter exn (Printexc.get_backtrace ())
    ) files

let () =
  let fail e = raise e in
  try
    Arg.parse Typecheck_args.spec push_file "";
    files := List.rev !files;
    (* if !Typecheck_flags.debug then Printexc.record_backtrace true; *)
    begin
      match !output with
        None ->
        annotate_files Format.std_formatter !files
      | Some output ->
        safe_open_out
          (fun oc ->
             let fmt = Format.formatter_of_out_channel oc in
             annotate_files fmt !files ) output
        |> get ~fail
    end;
    exit !code
  with exn ->
    print_exn_with_backtrace
      ~with_bt:(!backtrace)
      Format.std_formatter exn (Printexc.get_backtrace());
    exit 2
  (*   Typecheck_expr.Expr_error e -> *)
  (*   Typecheck_expr.print_error e; *)
  (*   exit 2 *)
  (* | x -> *)
  (*   Format.fprintf Format.std_formatter *)
  (*     "Backtrace:\n  %s\n%a" *)
  (*     (Printexc.get_backtrace ()) *)
  (*     Location.report_exception x; *)
  (*   exit 2 *)
