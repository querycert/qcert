(*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

open Util
open QcertConfig
open Compiler.EnhancedCompiler
open Logger
open LoggerToSexp

(* Command line args *)

let args_list gconf =
  Arg.align
    [ ("-source", Arg.String (QcertArg.set_source gconf),
       "<lang> Indicates the language for of thesource file (default: Rule)");
      ("-target", Arg.String (QcertArg.set_target gconf),
       "<lang> Indicates the language for the target query (default: js)");
      ("-path", Arg.String (QcertArg.add_path gconf),
       "<lang> Specify an intermediate language in the compilation path");
      ("-exact-path", Arg.Unit (QcertArg.set_exact_path gconf),
       " Use exactly the given path (do not infer intermediate steps nor add optimization)");
      ("-dir", Arg.String (QcertArg.set_dir gconf),
       "<dir> Directory for the emited code");
      ("-dir-target", Arg.String (QcertArg.set_dir_target gconf),
       "<dir> Directory for the emitied code of target (if not specified use the one given by -dir)");
      ("-js-runtime", Arg.String (CloudantUtil.set_harness gconf.gconf_cld_conf),
       "<harness.js> JavaScript runtime");
      ("-io", Arg.String (QcertArg.set_io gconf),
       "<file.io> Schema and inputs data for evaluation");
      ("-io-use-world", Arg.Unit (QcertArg.set_io_use_world gconf),
       "Declare 'CONST$WORLD' as a distributed variable");
      ("-emit-all", Arg.Unit (QcertArg.set_emit_all gconf),
       " Emit generated code of all intermediate queries");
      ("-emit-sexp", Arg.Unit (QcertArg.set_emit_sexp gconf),
       " Emit the target query as an s-expression");
      ("-emit-sexp-all", Arg.Unit (QcertArg.set_emit_sexp_all gconf),
       " Emit all intermediate queries as s-expressions");
      ("-eval", Arg.Unit (QcertArg.set_eval gconf),
       " Evaluate the target query on the input data");
      ("-eval-all", Arg.Unit (QcertArg.set_eval_all gconf),
       " Evaluate all intermediate queries on the input data");
      ("-eval-debug", Arg.Unit (QcertArg.set_eval_debug gconf),
       " Evaluate the target query in debug mode");
      ("-eval-validate", Arg.Unit (QcertArg.set_eval_validate gconf),
       " Checks the result of evaluation against the expected result");
      ("-source-sexp", Arg.Unit (QcertArg.set_source_sexp gconf),
       " Indicate that the source file is expected to be an s-expression");
      ("-stat", Arg.Unit (QcertArg.set_stat gconf),
         " Produce statistics for the target query");
      ("-stat-all", Arg.Unit (QcertArg.set_stat_all gconf),
         " Produce statistics for all intermediate queries");
      ("-stat-tree", Arg.Unit (QcertArg.set_stat_tree gconf),
       " Produce statistics for paths following starting from the source");
      (*  " Logs the optimizations/rewrites during compilation"); *)
      ("-log-optims", Arg.String
			(fun s -> Logger.nra_set_trace logger_nra_to_sexp s;
				  Logger.nrc_set_trace logger_nrc_to_sexp s;
				  Logger.dnrc_set_trace logger_nrc_to_sexp s),
       " Enable optimization logging");
      ("-log-optims-nra", Arg.String (Logger.nra_set_trace logger_nra_to_sexp),
       " Enable optimization logging for nra");
      ("-log-optims-nrc", Arg.String (Logger.nrc_set_trace logger_nrc_to_sexp),
       " Enable optimization logging for nrc");
      ("-log-optims-dnrc", Arg.String (Logger.dnrc_set_trace logger_dnrc_to_sexp),
       " Enable optimization logging for dnrc");
      ("-ascii", Arg.Unit (PrettyIL.set_ascii gconf.gconf_pretty_config),
       " Avoid unicode symbols in emited queries");
      ("-margin", Arg.Int (PrettyIL.set_margin gconf.gconf_pretty_config),
       "<n> Set right margin for emited queries");
      ("-cld-prefix", Arg.String (CloudantUtil.set_prefix gconf.gconf_cld_conf),
       "<pref> Cloudant DB prefix");
      ("-java-imports", Arg.String (QcertArg.set_java_imports gconf),
       "<imports> Additional imports for the Java runtime");
      (* ("-eval", Arg.Unit XXX, "Evaluate the target query"); *)
      (* ("-eval-all", Arg.Unit XXX, "Evaluate all the intermediate queries"); *)
      ("-vinit", Arg.String (QcertArg.set_vinit gconf),
       "<init> Set the name init variable for the map-reduce backends");
      ("-vdistr", Arg.String (QcertArg.add_vdirst gconf),
       "<x> Declare x as a distributed variable");
      ("-vlocal", Arg.String (QcertArg.add_vlocal gconf),
       "<x> Declare x as a local variable");
    ]

let anon_args input_files f = input_files := f :: !input_files

let languages =
  [ Compiler.L_rule;
    Compiler.L_camp;
    Compiler.L_oql;
    Compiler.L_sql;
    Compiler.L_lambda_nra;
    Compiler.L_nra;
    Compiler.L_nraenv_core;
    Compiler.L_nraenv;
    Compiler.L_nnrc;
    Compiler.L_nnrcmr;
    Compiler.L_cldmr;
    Compiler.L_dnnrc_dataset;
    Compiler.L_dnnrc_typed_dataset;
    Compiler.L_javascript;
    Compiler.L_java;
    Compiler.L_spark;
    Compiler.L_spark2;
    Compiler.L_cloudant; ]


let languages_string =
  QcertUtil.string_of_path ", " languages

let usage =
  "Q*cert - Query compiler\n"^
  "Supported languages are:\n"^
  "  "^languages_string^
  "\n"^
  "Usage: "^Sys.argv.(0)^" [options] query1 query2 ..."


let parse_args () =
  let input_files = ref [] in
  let gconf =
    { gconf_source = Compiler.L_rule;
      gconf_target = Compiler.L_javascript;
      gconf_path = [];
      gconf_exact_path = false;
      gconf_dir = None;
      gconf_dir_target = None;
      gconf_io = None;
      gconf_io_use_world = false;
      gconf_schema = TypeUtil.empty_schema;
      gconf_data = Compiler.Ev_in_world [];
      gconf_expected_output_data = [];
      gconf_cld_conf = CloudantUtil.default_cld_config ();
      gconf_emit_all = false;
      gconf_emit_sexp = false;
      gconf_emit_sexp_all = false;
      gconf_eval = false;
      gconf_eval_all = false;
      gconf_eval_debug = false;
      gconf_eval_validate = false;
      gconf_source_sexp = false;
      gconf_pretty_config = PrettyIL.default_pretty_config ();
      gconf_java_imports = "";
      gconf_mr_vinit = "init";
      gconf_vdbindings = [];
      gconf_stat = false;
      gconf_stat_all = false;
      gconf_stat_tree = false; }
  in
  Arg.parse (args_list gconf) (anon_args input_files) usage;
  (complet_configuration gconf, List.rev !input_files)



let () =
  let gconf, input_files = parse_args () in
  (* XXX qcert goes quiet if in eval-validate mode... - to be discussed with Louis XXX *)
  if gconf.gconf_eval_validate then () else Format.printf "%a" QcertCore.fprint_compilation_path gconf;
  let results =
    List.map
      (fun file_name -> QcertCore.main gconf (file_name, string_of_file file_name))
      input_files
  in
  let output_res file_res =
    if file_res.QcertCore.res_file <> "" then
      make_file file_res.QcertCore.res_file file_res.QcertCore.res_content
  in
  let output_stats res =
    if res.QcertCore.res_stat <> "" then
      Format.printf "%s@." res.QcertCore.res_stat;
    if res.QcertCore.res_stat_all <> [] then
      Format.printf "[ @[%a@] ]@."
        (Format.pp_print_list
           ~pp_sep:(fun ff () -> Format.fprintf ff ",@\n")
           (fun ff stat -> Format.fprintf ff "%s" stat))
        res.QcertCore.res_stat_all;
    output_res res.QcertCore.res_stat_tree
  in
  List.iter
    (fun res ->
      output_res res.QcertCore.res_emit;
      List.iter output_res res.QcertCore.res_emit_all;
      output_res res.QcertCore.res_eval;
      List.iter output_res res.QcertCore.res_eval_all;
      output_res res.QcertCore.res_emit_sexp;
      List.iter output_res res.QcertCore.res_emit_sexp_all;
      output_stats res)
    results
