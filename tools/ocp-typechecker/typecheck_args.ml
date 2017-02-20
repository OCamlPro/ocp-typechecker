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

open Typecheck_iO
open Typecheck_flags
open Typecheck_result

module Driver_export = struct
  open OCaml.Config
  open OCaml.Compenv
  open OCaml.Clflags

  let process_interface_file ppf name =
    Compile.interface ppf name (output_prefix name)

  let process_implementation_file ppf name =
    let opref = output_prefix name in
    Compile.implementation ppf name opref;
    objfiles := (opref ^ ".cmo") :: !objfiles

  let process_file ppf name =
    if Filename.check_suffix name ".ml"
       || Filename.check_suffix name ".mlt" then begin
      let opref = output_prefix name in
      Compile.implementation ppf name opref;
      objfiles := (opref ^ ".cmo") :: !objfiles
    end
    else if Filename.check_suffix name !Config.interface_suffix then begin
      let opref = output_prefix name in
      Compile.interface ppf name opref;
      if !make_package then objfiles := (opref ^ ".cmi") :: !objfiles
    end
    else if Filename.check_suffix name ".cmo"
            || Filename.check_suffix name ".cma" then
      objfiles := name :: !objfiles
    else if Filename.check_suffix name ".cmi" && !make_package then
      objfiles := name :: !objfiles
    else if Filename.check_suffix name ext_obj
            || Filename.check_suffix name ext_lib then
      ccobjs := name :: !ccobjs
    else if Filename.check_suffix name ext_dll then
      dllibs := name :: !dllibs
    else if Filename.check_suffix name ".c" then begin
      Compile.c_file name;
      ccobjs := (Filename.chop_suffix (Filename.basename name) ".c" ^ ext_obj)
                :: !ccobjs
    end
    else
      raise(Arg.Bad("don't know what to do with " ^ name))


  let ppf = Format.err_formatter

  (* Error messages to standard error formatter *)
  let anonymous filename =
    readenv ppf Before_compile; process_file ppf filename;;
  let impl filename =
    readenv ppf Before_compile; process_implementation_file ppf filename;;
  let intf filename =
    readenv ppf Before_compile; process_interface_file ppf filename;;

  let show_config () =
    Config.print_config stdout;
    exit 0;
  ;;
end

module OCaml_options = Main_args.Make_bytecomp_options (struct
    open OCaml.Clflags
    open OCaml.Compenv
    open Driver_export
  let set r () = r := true
  let unset r () = r := false
  let _a = set make_archive
  let _absname = set Location.absname
  let _annot = set annotations
  let _binannot = set binary_annotations
  let _c = set compile_only
  let _cc s = c_compiler := Some s
  let _cclib s = ccobjs := Misc.rev_split_words s @ !ccobjs
  let _ccopt s = first_ccopts := s :: !first_ccopts
  let _compat_32 = set bytecode_compatible_32
  let _config = show_config
  let _custom = set custom_runtime
#if OCAML_VERSION >= "4.02.3"
 let _no_check_prims = set no_check_prims
  let _keep_locs = set keep_locs
  let _keep_docs = set keep_docs
  let _output_complete_obj () =
    output_c_object := true; output_complete_object := true; custom_runtime := true
#elif OCAML_VERSION >= "4.02"
  let _keep_locs _ = ()
#endif
  let _dllib s = dllibs := Misc.rev_split_words s @ !dllibs
  let _dllpath s = dllpaths := !dllpaths @ [s]
  let _for_pack s = for_package := Some s
  let _g = set debug
  let _i () = print_types := true; compile_only := true
  let _I s = include_dirs := s :: !include_dirs
  let _impl = impl
  let _intf = intf
  let _intf_suffix s = Config.interface_suffix := s
  let _labels = unset classic
  let _linkall = set link_everything
  let _make_runtime () =
    custom_runtime := true; make_runtime := true; link_everything := true
  let _no_alias_deps = set transparent_modules
  let _no_app_funct = unset applicative_functors
  let _noassert = set noassert
  let _nolabels = set classic
  let _noautolink = set no_auto_link
  let _nostdlib = set no_std_include
  let _o s = output_name := Some s
  let _open s = open_modules := s :: !open_modules
  let _output_obj () = output_c_object := true; custom_runtime := true
  let _pack = set make_package
  let _pp s = preprocessor := Some s
  let _ppx s = first_ppx := s :: !first_ppx
  let _principal = set principal
  let _rectypes = set recursive_types
  let _runtime_variant s = runtime_variant := s
  let _safe_string = unset unsafe_string
  let _short_paths = unset real_paths
  let _strict_sequence = set strict_sequence
  let _strict_formats = set strict_formats
  let _thread = set use_threads
  let _vmthread = set use_vmthreads
  let _unsafe = set fast
  let _unsafe_string = set unsafe_string
  let _use_prims s = use_prims := s
  let _use_runtime s = use_runtime := s
  let _v () = print_version_and_library "compiler"
  let _version = print_version_string
  let _vnum = print_version_string
  let _w = (Warnings.parse_options false)
  let _warn_error = (Warnings.parse_options true)
  let _warn_help = Warnings.help_warnings
  let _where = print_standard_library
  let _verbose = set verbose
  let _nopervasives = set nopervasives
  let _dsource = set dump_source
  let _dparsetree = set dump_parsetree
  let _dtypedtree = set dump_typedtree
  let _drawlambda = set dump_rawlambda
  let _dlambda = set dump_lambda
  let _dinstr = set dump_instr

  (* let _dlambda_types = set dump_lambda_types *)
  (* let _dlambda_infos = set dump_lambda_infos *)
  (* let _o_rawlambda = set output_rawlambda *)
  (* let _o_lambda = set output_lambda *)

  let anonymous = anonymous
end)


let spec = [
  "-dtypedtree", Arg.Set print_dtypedtree, "Prints typedtree";
  "-dannot", Arg.Set print_annotated, "Prints \"annotated\" program";
  "-dannot-full", Arg.Unit (fun () -> print_annotated := true;
                             Typecheck_pretty.full := true),
  "Prints the annotedted program with all information";
  "-debug", Arg.Set debug, "Debug flag";
  "-o", Arg.String (fun s -> output := Some s), "Prints the result into the
  given file.";
  "-no-typecheck", Arg.Clear typecheck, "Does not typecheck";
  "-I", Arg.String (fun dir ->
      Clflags.include_dirs := dir :: !Clflags.include_dirs),
  "Adds searchable paths";
  "-bt", Arg.Unit (fun () ->
      Printexc.record_backtrace true;
      backtrace := true),
  "Prints the backtrace in case of error";
  "-warnmode", Arg.Set warn_mode, "Warning mode";

] @ OCaml_options.list
