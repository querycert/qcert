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

open QcertExtracted
open QcertLib

open Util
open QcertConfig
open QcertCompiler.EnhancedCompiler
open LoggerToSexp

(* Command line args *)

let args_list gconf =
  Arg.align
    [ ("-version", Arg.Unit QcertUtil.get_version,
       " Prints the compiler version");
      ("-source", Arg.String (QcertArg.set_source gconf),
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
      ("-schema", Arg.String (QcertArg.set_schema_file gconf),
       "<file.schema> Schema");
      ("-input", Arg.String (QcertArg.set_input_file gconf),
       "<file.input> Input");
      ("-output", Arg.String (QcertArg.set_output_file gconf),
       "<file.output> Expected output");
      ("-io", Arg.String (QcertArg.set_io_file gconf),
       "<file.io> I/O file (Schema,input data,expected output) for evaluation");
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
      ("-optim-config", Arg.String (QcertArg.set_optim_config_file gconf),
       " Optimizer configuration (JSON format)");
      ("-emit-optim-config", Arg.Unit (QcertArg.set_emit_optim_config gconf),
       " Emit the optimizer configuration (JSON format)");
      ("-log-optims", Arg.String
			(fun s -> Logger.nra_set_trace logger_nra_to_sexp s;
				  Logger.nrc_set_trace logger_nrc_to_sexp s;
				  Logger.dnrc_set_trace logger_dnrc_to_sexp s;
                                  Logger.nnrs_imp_all_set_trace logger_nnrs_imp_expr_to_sexp logger_nnrs_imp_stmt_to_sexp logger_nnrs_imp_to_sexp s
                        ),
       " Enable optimization logging");
      ("-log-optims-nra", Arg.String (Logger.nra_set_trace logger_nra_to_sexp),
       " Enable optimization logging for nra");
      ("-log-optims-nrc", Arg.String (Logger.nrc_set_trace logger_nrc_to_sexp),
       " Enable optimization logging for nrc");
      ("-log-optims-nnrs-imp", Arg.String (Logger.nnrs_imp_all_set_trace logger_nnrs_imp_expr_to_sexp logger_nnrs_imp_stmt_to_sexp logger_nnrs_imp_to_sexp),
       " Enable optimization logging for nnrs-imp");
      ("-log-optims-nnrs-imp-expr", Arg.String (Logger.nnrs_imp_expr_set_trace logger_nnrs_imp_expr_to_sexp),
       " Enable optimization logging for nnrs-imp-expr");
      ("-log-optims-nnrs-imp-stmt", Arg.String (Logger.nnrs_imp_stmt_set_trace logger_nnrs_imp_stmt_to_sexp),
       " Enable optimization logging for nnrs-imp-stmt");
      ("-log-optims-nnrs-imp-top", Arg.String (Logger.nnrs_imp_set_trace logger_nnrs_imp_to_sexp),
       " Enable optimization logging for nnrs-imp top level");
      ("-log-optims-dnrc", Arg.String (Logger.dnrc_set_trace logger_dnrc_to_sexp),
       " Enable optimization logging for dnrc");
      ("-ascii", Arg.Unit (PrettyCommon.set_ascii gconf.gconf_pretty_config),
       " Avoid unicode symbols in emited queries");
      ("-type-annotations", Arg.Unit (PrettyCommon.set_type_annotations gconf.gconf_pretty_config),
       " Print type annotations on ILs");
      ("-margin", Arg.Int (PrettyCommon.set_margin gconf.gconf_pretty_config),
       "<n> Set right margin for emited queries");
      ("-link-js-runtime", Arg.Unit (QcertArg.set_link_js_runtime gconf),
       " Link the JavaScript runtime (only for JavaScript and Cloudant targets)");
      ("-java-imports", Arg.String (QcertArg.set_java_imports gconf),
       "<imports> Additional imports for the Java runtime (only for Java target)");
      ("-vinit", Arg.String (QcertArg.set_vinit gconf),
       "<init> Set the name of the init variable (only for SparkRDD and Cloudant targets)");
    ]

let anon_args input_files f = input_files := f :: !input_files

let languages =
  [ QcertCompiler.L_camp_rule;
    QcertCompiler.L_camp;
    QcertCompiler.L_tech_rule;
    QcertCompiler.L_designer_rule;
    QcertCompiler.L_oql;
    QcertCompiler.L_sql;
    QcertCompiler.L_sqlpp;
    QcertCompiler.L_lambda_nra;
    QcertCompiler.L_nra;
    QcertCompiler.L_nraenv;
    QcertCompiler.L_nraenv_core;
    QcertCompiler.L_nnrc;
    QcertCompiler.L_nnrc_core;
    QcertCompiler.L_nnrs;
    QcertCompiler.L_nnrs_core;
    QcertCompiler.L_imp_qcert;
    QcertCompiler.L_imp_json;
    QcertCompiler.L_nnrcmr;
    QcertCompiler.L_dnnrc;
    QcertCompiler.L_dnnrc_typed;
    QcertCompiler.L_js_ast;
    QcertCompiler.L_javascript;
    QcertCompiler.L_java;
    QcertCompiler.L_spark_df; ]


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
    { gconf_qname = None;
      gconf_source = QcertCompiler.L_camp_rule;
      gconf_target = QcertCompiler.L_javascript;
      gconf_path = [];
      gconf_exact_path = false;
      gconf_dir = None;
      gconf_dir_target = None;
      gconf_io = None;
      gconf_schema = TypeUtil.empty_schema;
      gconf_input = [];
      gconf_output = QData.dunit;
      gconf_emit_all = false;
      gconf_emit_sexp = false;
      gconf_emit_sexp_all = false;
      gconf_eval = false;
      gconf_eval_all = false;
      gconf_eval_debug = false;
      gconf_eval_validate = false;
      gconf_source_sexp = false;
      gconf_pretty_config = PrettyCommon.default_pretty_config ();
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
  Arg.parse (args_list gconf) (anon_args input_files) usage;
  (complete_configuration gconf, List.rev !input_files)

let process_file f file_name =
  let file_content = string_of_file file_name in
  try f (file_name,file_content) with
  | Qcert_Error msg ->
      raise (Qcert_Error ("In file [" ^ file_name ^ "] " ^ msg))

let () =
  let gconf, input_files = parse_args () in
  (* XXX qcert goes quiet if in eval-validate mode... - to be discussed with Louis XXX *)
  if gconf.gconf_eval_validate then () else Format.printf "%a" QcertCore.fprint_compilation_path gconf;
  let results = List.map (process_file (QcertCore.main gconf)) input_files in
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
  let res_validates = ref true in
  List.iter
    (fun res ->
      res_validates := !res_validates && res.QcertCore.res_validates;
      output_res res.QcertCore.res_emit;
      List.iter output_res res.QcertCore.res_emit_all;
      output_res res.QcertCore.res_eval;
      List.iter output_res res.QcertCore.res_eval_all;
      output_res res.QcertCore.res_emit_sexp;
      List.iter output_res res.QcertCore.res_emit_sexp_all;
      output_stats res;
      output_res res.QcertCore.res_optim_config;)
    results;
  if !res_validates
  then exit 0
  else exit 1

