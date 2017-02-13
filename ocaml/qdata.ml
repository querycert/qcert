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
open Compiler.EnhancedCompiler

let verbose = ref false
  
(* Command line args *)
let args gconf =
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
    { gconf_source = Compiler.L_rule;
      gconf_target = Compiler.L_javascript;
      gconf_path = [];
      gconf_exact_path = false;
      gconf_dir = None;
      gconf_dir_target = None;
      gconf_io = None;
      gconf_schema = TypeUtil.empty_schema;
      gconf_input = [];
      gconf_output = [];
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
      gconf_stat = false;
      gconf_stat_all = false;
      gconf_stat_tree = false; }
  in
  Arg.parse (args_list gconf) (anon_args input_files) usage;
  (complet_configuration gconf, List.rev !input_files)

let process_data_file gconf f : string list =
  begin
    let io : QData.json = parse_io_from_file f in
    let json_schema_io =
      match get_data_schema conf with
      | Some sio -> sio
      | None -> io
    in
    let sch = TypeUtil.schema_of_io_json json_schema_io in
    let (brand_model,wmTypeC) =
      (sch.TypeUtil.sch_brand_model,
       sch.TypeUtil.sch_camp_type)
    in
    let datalist = (DataUtil.get_input (get_data_format conf) (Some io)) in
    List.map (fun d ->
      match QType.data_to_sjson brand_model d wmTypeC with
      | Some sdata ->
	  let sdata = Util.string_of_char_list sdata in
	  sdata
      | None ->
	  raise (Failure "Spark I/O serialization failed"))
      datalist
  end

let anon_args gconf f =
  let sdata_list = process_data_file gconf f in
  DataUtil.display_sdata (get_data_dir conf) f sdata_list (suffix_sdata ())

(* Main *)
let () =
  let gconf, input_files = parse_args () in
  DataUtil.display_sdata gconf.gconf_dir "file" sdata_list (suffix_sdata ())
