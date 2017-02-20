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

let print_exn_with_backtrace ~with_bt fmt exn bt =
  let print_bt fmt bt =
    if with_bt then Format.fprintf fmt "%s\n" bt in
  Format.fprintf fmt "%a\n\n%a" print_exn exn print_bt bt

let write_report ?outdir filename exns =
  let outdir = match outdir with
      Some s -> s
    | None -> Filename.dirname filename in
  let name =
    let name =
      try Filename.chop_extension filename
      with Invalid_argument _ -> filename in
    Printf.sprintf "%s.%s.tcrep" name (Filename.basename Sys.argv.(0))
  in
  let output =
    Typecheck_iO.safe_open_out
      (fun ch -> Format.fprintf (Format.formatter_of_out_channel ch)
         "[Typechecking %s]\n%a%!" name
         (fun fmt l -> List.iter (print_exn fmt) l) exns) @@
      Filename.concat outdir name
  in
  match output with
    Typecheck_result.Ok () -> ()
  | Typecheck_result.Error exn ->
    raise exn
