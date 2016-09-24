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
      (* ("-stats", Arg.Unit (set_stats conf), *)
      (*    " Produce statistics for the target query"); *)
      (* ("-stats-all", Arg.Unit (set_stats conf), *)
      (*    " Produce statistics for all intermediate queries"); *)
      ("-emit-all", Arg.Unit (QcertArg.set_emit_all gconf),
       " Emit generated code of all intermediate queries");
      ("-emit-sexp", Arg.Unit (QcertArg.set_emit_sexp gconf),
       " Emit the target query as an s-expression");
      ("-emit-sexp-all", Arg.Unit (QcertArg.set_emit_sexp_all gconf),
       " Emit all intermediate queries as s-expressions");
      (* ("-log-optims", Arg.Unit (Logger.set_trace), *)
      (*  " Logs the optimizations/rewrites during compilation"); *)
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
  [ CompDriver.L_rule;
    CompDriver.L_camp;
    CompDriver.L_oql;
    CompDriver.L_nra;
    CompDriver.L_nraenv;
    CompDriver.L_nnrc;
    CompDriver.L_nnrcmr;
    CompDriver.L_cldmr;
    CompDriver.L_dnnrc_dataset;
    CompDriver.L_dnnrc_typed_dataset;
    CompDriver.L_javascript;
    CompDriver.L_java;
    CompDriver.L_spark;
    CompDriver.L_spark2;
    CompDriver.L_cloudant; ]


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
    { gconf_source = CompDriver.L_rule;
      gconf_target = CompDriver.L_javascript;
      gconf_path = [];
      gconf_exact_path = false;
      gconf_dir = None;
      gconf_dir_target = None;
      gconf_io = None;
      gconf_schema = TypeUtil.empty_schema;
      gconf_cld_conf = CloudantUtil.default_cld_config ();
      gconf_emit_all = false;
      gconf_emit_sexp = false;
      gconf_emit_sexp_all = false;
      gconf_pretty_config = PrettyIL.default_pretty_config ();
      gconf_java_imports = "";
      gconf_mr_vinit = "init";
      gconf_vdbindings = []; }
  in
  Arg.parse (args_list gconf) (anon_args input_files) usage;
  (complet_configuration gconf, List.rev !input_files)



let () =
  let gconf, input_files = parse_args () in
  Format.printf "%a" QcertCore.fprint_comilation_path gconf;
  let results =
    List.map
      (fun file_name -> QcertCore.main gconf (file_name, string_of_file file_name))
      input_files
  in
  let output_res (file_name, s) =
    if file_name <> "" then
      make_file file_name s
  in
  List.iter
    (fun res ->
      output_res res.QcertCore.res_emit;
      List.iter output_res res.QcertCore.res_emit_all;
      output_res res.QcertCore.res_emit_sexp;
      List.iter output_res res.QcertCore.res_emit_sexp_all)
    results
