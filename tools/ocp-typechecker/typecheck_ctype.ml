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

include Ctype
open Types

(* Temporary workaround for cyclic deps *)
let eq = ref (fun (_ : Env.t) _ _ -> assert false)

let begin_def () =
  Typecheck_flags.print_debug
    (Format.sprintf "begin_def, level: %d" @@
     (Ctype.get_current_level () + 1));
  begin_def()


let end_def () =
  Typecheck_flags.print_debug
    (Format.sprintf "end_def, level: %d" @@
     Ctype.get_current_level ());
  end_def()

let init_def level =
  Typecheck_flags.print_debug (Format.sprintf "init_def at level: %d" level);
  Ctype.init_def level

(* let unify env t1 t2 = *)
(*   Typecheck_flags.print_debug @@ lazy *)
(*   (Format.asprintf "unify %a (%a) with %a (%a)" *)
(*     Printtyp.raw_type_expr t1 Typecheck_pretty.Types.print_type_simple t1.desc *)
(*     Printtyp.raw_type_expr t2 Typecheck_pretty.Types.print_type_simple t2.desc); *)
(*   (\* unify env t1 t2 *\) *)
(*   if !eq env t1 t2 then () else *)
(*     raise (Unify [t1, t2]) *)


(* let unify' env t1 t2 = *)
(*   Typecheck_flags.print_debug @@ lazy *)
(*   (Format.asprintf "REALLY unify %a (%a) with %a (%a)" *)
(*     Printtyp.raw_type_expr t1 Typecheck_pretty.Types.print_type_simple t1.desc *)
(*     Printtyp.raw_type_expr t2 Typecheck_pretty.Types.print_type_simple t2.desc); *)
(*   (\* unify env t1 t2 *\) *)
(*   Ctype.unify env t1 t2 *)
