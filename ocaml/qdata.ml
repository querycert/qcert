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

(* This is main for the Camp Data processor *)

open Util
open QcertConfig
open ParseFile

open QcertCompiler.EnhancedCompiler

let verbose = ref false
  
(* Command line args *)
let args_list gconf =
  Arg.align
    [ ("-dir", Arg.String (QcertArg.set_dir gconf),
       "<dir> Directory for the emited");
      ("-schema", Arg.String (QcertArg.set_schema_file gconf),
       "<file.schema> Schema");
      ("-io", Arg.String (QcertArg.set_io_file gconf),
       "<file.io> I/O file (Schema,input data,expected output) for evaluation") ]

let anon_args input_files f = input_files := f :: !input_files

let usage =
  "Q*cert - Data processor\n"^
  "Usage: "^Sys.argv.(0)^" [options]"

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

let anon_args gconf f = ()

(* Main *)
let () =
  let gconf, input_files = parse_args () in
  let file_name =
    begin match gconf.gconf_io with
    | Some (IO_file (Some fio)) -> fio
    | Some (IO_components (Some finput,_,_)) -> finput
    | _ -> raise (Qcert_Error "qdata requires I/O file or schema/input files")
    end
  in 
  let results = QcertCore.main_data gconf file_name in
  let output_res file_res =
    if file_res.QcertCore.res_file <> "" then
      make_file file_res.QcertCore.res_file file_res.QcertCore.res_content
  in
  List.iter output_res results
