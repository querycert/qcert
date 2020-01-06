(*
 * Copyright 2015-2017 IBM Corporation
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

open Qcert_lib

open Util
open Logger
open Config
open Compiler.EnhancedCompiler
open Logger_to_sexp

(* Command line args *)

let args_list gconf =
  Stdlib.Arg.align
    [ ("-version", Stdlib.Arg.Unit Compiler_util.get_version,
       " Prints the compiler version");
      ("-source", Stdlib.Arg.String (Args.set_source gconf),
       "<lang> Indicates the language for of thesource file (default: Rule)");
      ("-target", Stdlib.Arg.String (Args.set_target gconf),
       "<lang> Indicates the language for the target query (default: js)");
      ("-path", Stdlib.Arg.String (Args.add_path gconf),
       "<lang> Specify an intermediate language in the compilation path");
      ("-exact-path", Stdlib.Arg.Unit (Args.set_exact_path gconf),
       " Use exactly the given path (do not infer intermediate steps nor add optimization)");
      ("-dir", Stdlib.Arg.String (Args.set_dir gconf),
       "<dir> Directory for the emited code");
      ("-dir-target", Stdlib.Arg.String (Args.set_dir_target gconf),
       "<dir> Directory for the emitied code of target (if not specified use the one given by -dir)");
      ("-schema", Stdlib.Arg.String (Args.set_schema_file gconf),
       "<file.schema> Schema");
      ("-input", Stdlib.Arg.String (Args.set_input_file gconf),
       "<file.input> Input");
      ("-output", Stdlib.Arg.String (Args.set_output_file gconf),
       "<file.output> Expected output");
      ("-io", Stdlib.Arg.String (Args.set_io_file gconf),
       "<file.io> I/O file (Schema,input data,expected output) for evaluation");
      ("-emit-all", Stdlib.Arg.Unit (Args.set_emit_all gconf),
       " Emit generated code of all intermediate queries");
      ("-emit-sexp", Stdlib.Arg.Unit (Args.set_emit_sexp gconf),
       " Emit the target query as an s-expression");
      ("-emit-sexp-all", Stdlib.Arg.Unit (Args.set_emit_sexp_all gconf),
       " Emit all intermediate queries as s-expressions");
      ("-eval", Stdlib.Arg.Unit (Args.set_eval gconf),
       " Evaluate the target query on the input data");
      ("-eval-all", Stdlib.Arg.Unit (Args.set_eval_all gconf),
       " Evaluate all intermediate queries on the input data");
      ("-eval-debug", Stdlib.Arg.Unit (Args.set_eval_debug gconf),
       " Evaluate the target query in debug mode");
      ("-eval-validate", Stdlib.Arg.Unit (Args.set_eval_validate gconf),
       " Checks the result of evaluation against the expected result");
      ("-source-sexp", Stdlib.Arg.Unit (Args.set_source_sexp gconf),
       " Indicate that the source file is expected to be an s-expression");
      ("-stat", Stdlib.Arg.Unit (Args.set_stat gconf),
         " Produce statistics for the target query");
      ("-stat-all", Stdlib.Arg.Unit (Args.set_stat_all gconf),
         " Produce statistics for all intermediate queries");
      ("-stat-tree", Stdlib.Arg.Unit (Args.set_stat_tree gconf),
       " Produce statistics for paths following starting from the source");
      ("-optim-config", Stdlib.Arg.String (Args.set_optim_config_file gconf),
       " Optimizer configuration (JSON format)");
      ("-emit-optim-config", Stdlib.Arg.Unit (Args.set_emit_optim_config gconf),
       " Emit the optimizer configuration (JSON format)");
      ("-log-optims", Stdlib.Arg.String
			(fun s -> nraenv_set_trace logger_nraenv_to_sexp s;
				  nnrc_set_trace logger_nnrc_to_sexp s;
				  dnnrc_set_trace logger_dnnrc_to_sexp s;
        nnrs_imp_all_set_trace logger_nnrs_imp_expr_to_sexp logger_nnrs_imp_stmt_to_sexp logger_nnrs_imp_to_sexp s
      ),
       " Enable optimization logging");
      ("-log-optims-nra", Stdlib.Arg.String (nraenv_set_trace logger_nraenv_to_sexp),
       " Enable optimization logging for nra");
      ("-log-optims-nrc", Stdlib.Arg.String (nnrc_set_trace logger_nnrc_to_sexp),
       " Enable optimization logging for nrc");
      ("-log-optims-nnrs-imp", Stdlib.Arg.String (nnrs_imp_all_set_trace logger_nnrs_imp_expr_to_sexp logger_nnrs_imp_stmt_to_sexp logger_nnrs_imp_to_sexp),
       " Enable optimization logging for nnrs-imp");
      ("-log-optims-nnrs-imp-expr", Stdlib.Arg.String (nnrs_imp_expr_set_trace logger_nnrs_imp_expr_to_sexp),
       " Enable optimization logging for nnrs-imp-expr");
      ("-log-optims-nnrs-imp-stmt", Stdlib.Arg.String (nnrs_imp_stmt_set_trace logger_nnrs_imp_stmt_to_sexp),
       " Enable optimization logging for nnrs-imp-stmt");
      ("-log-optims-nnrs-imp-top", Stdlib.Arg.String (nnrs_imp_set_trace logger_nnrs_imp_to_sexp),
       " Enable optimization logging for nnrs-imp top level");
      ("-log-optims-dnrc", Stdlib.Arg.String (dnnrc_set_trace logger_dnnrc_to_sexp),
       " Enable optimization logging for dnrc");
      ("-ascii", Stdlib.Arg.Unit (Pretty_common.set_ascii gconf.gconf_pretty_config),
       " Avoid unicode symbols in emited queries");
      ("-type-annotations", Stdlib.Arg.Unit (Pretty_common.set_type_annotations gconf.gconf_pretty_config),
       " Print type annotations on ILs");
      ("-margin", Stdlib.Arg.Int (Pretty_common.set_margin gconf.gconf_pretty_config),
       "<n> Set right margin for emited queries");
      ("-link-js-runtime", Stdlib.Arg.Unit (Args.set_link_js_runtime gconf),
       " Link the JavaScript runtime (only for JavaScript and Cloudant targets)");
      ("-java-imports", Stdlib.Arg.String (Args.set_java_imports gconf),
       "<imports> Additional imports for the Java runtime (only for Java target)");
      ("-vinit", Stdlib.Arg.String (Args.set_vinit gconf),
       "<init> Set the name of the init variable (only for SparkRDD and Cloudant targets)");
      ("-quiet", Stdlib.Arg.Unit (Args.set_quiet gconf),
       " compile quietly");
    ]

let anon_args input_files f = input_files := f :: !input_files

let languages =
  [ Compiler.L_camp_rule;
    Compiler.L_camp;
    Compiler.L_tech_rule;
    Compiler.L_designer_rule;
    Compiler.L_oql;
    Compiler.L_sql;
    Compiler.L_sqlpp;
    Compiler.L_lambda_nra;
    Compiler.L_nra;
    Compiler.L_nraenv;
    Compiler.L_nraenv_core;
    Compiler.L_nnrc;
    Compiler.L_nnrc_core;
    Compiler.L_nnrs;
    Compiler.L_nnrs_core;
    Compiler.L_imp_qcert;
    Compiler.L_imp_ejson;
    Compiler.L_nnrcmr;
    Compiler.L_dnnrc;
    Compiler.L_dnnrc_typed;
    Compiler.L_js_ast;
    Compiler.L_javascript;
    Compiler.L_java;
    Compiler.L_spark_df; ]


let languages_string =
  Compiler_util.string_of_path ", " languages

let usage =
  "Q*cert - Query compiler\n"^
  "Supported languages are:\n"^
  "  "^languages_string^
  "\n"^
  "Usage: "^Sys.argv.(0)^" [options] query1 query2 ..."


let parse_args () =
  let input_files = ref [] in
  let gconf =
    { gconf_qname = None;
      gconf_source = Compiler.L_camp_rule;
      gconf_target = Compiler.L_javascript;
      gconf_path = [];
      gconf_exact_path = false;
      gconf_dir = None;
      gconf_dir_target = None;
      gconf_io = None;
      gconf_schema = Type_util.empty_schema;
      gconf_input = [];
      gconf_output = QData.dunit;
      gconf_emit_all = false;
      gconf_emit_sexp = false;
      gconf_emit_sexp_all = false;
      gconf_eval = false;
      gconf_eval_all = false;
      gconf_eval_debug = false;
      gconf_eval_validate = false;
      gconf_quiet = false;
      gconf_source_sexp = false;
      gconf_pretty_config = Pretty_common.default_pretty_config ();
      gconf_java_imports = "";
      gconf_mr_vinit = "init";
      gconf_stat = false;
      gconf_stat_all = false;
      gconf_stat_tree = false;
      gconf_optim_config_file = None;
      gconf_emit_optim_config = false;
      gconf_optim_config = [];
      gconf_prefix = ""; }
  in
  Stdlib.Arg.parse (args_list gconf) (anon_args input_files) usage;
  (complete_configuration gconf, List.rev !input_files)

let process_file f file_name =
  let file_content = string_of_file file_name in
  try f (file_name,file_content) with
  | Qcert_Error msg ->
      raise (Qcert_Error ("In file [" ^ file_name ^ "] " ^ msg))

let () =
  let gconf, input_files = parse_args () in
  (* XXX qcert goes quiet if in eval-validate mode... - to be discussed with Louis XXX *)
  if gconf.gconf_eval_validate then () else Format.printf "%a" Core.fprint_compilation_path gconf;
  let results = List.map (process_file (Core.main gconf)) input_files in
  let output_res file_res =
    if file_res.Core.res_file <> "" then
      make_file file_res.Core.res_file file_res.Core.res_content
  in
  let output_stats res =
    if res.Core.res_stat <> "" then
      Format.printf "%s@." res.Core.res_stat;
    if res.Core.res_stat_all <> [] then
      Format.printf "[ @[%a@] ]@."
        (Format.pp_print_list
           ~pp_sep:(fun ff () -> Format.fprintf ff ",@\n")
           (fun ff stat -> Format.fprintf ff "%s" stat))
        res.Core.res_stat_all;
    output_res res.Core.res_stat_tree
  in
  let res_validates = ref true in
  List.iter
    (fun res ->
      res_validates := !res_validates && res.Core.res_validates;
      output_res res.Core.res_emit;
      List.iter output_res res.Core.res_emit_all;
      output_res res.Core.res_eval;
      List.iter output_res res.Core.res_eval_all;
      output_res res.Core.res_emit_sexp;
      List.iter output_res res.Core.res_emit_sexp_all;
      output_stats res;
      output_res res.Core.res_optim_config;)
    results;
  if !res_validates
  then exit 0
  else exit 1

