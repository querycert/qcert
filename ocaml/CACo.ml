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

(* This is main for the Camp Compiler *)

open Util
open ConfigUtil
open CloudantUtil
open Compiler.EnhancedCompiler

(* Compile from NRAEnv *)

let compile_nraenv_to_string (conf:comp_config) (nrule:string) (basename:string) (op:CALib.nraenv) =
  let lconf = get_comp_lang_config conf in
  match language_of_name (get_target_lang lconf) with
  | CompDriver.L_java ->
      (* this uses 'basename': the file name since the java class name needs to be the same as the file name *)
      (CALib.nnrc_to_java basename (get_java_imports conf) (CALib.compile_nraenv_to_nnrc op), None)
  | CompDriver.L_javascript ->
      (CALib.nnrc_to_js (CALib.compile_nraenv_to_nnrc op), None)
  | CompDriver.L_spark ->
      (CALib.compile_nraenv_to_spark nrule op, None)
  | CompDriver.L_spark2 ->
      let io =
	match get_comp_io conf with
	| Some io -> io
	| None -> raise (CACo_Error "Spark2 target requires a schema I/O file")
      in
      let schema = CALib.schema_of_io io in
      let e = CALib.translate_nraenv_to_dnnrc_typed_dataset schema op in
      (CALib.dnnrc_typed_dataset_to_spark2 nrule schema e, Some schema)
  | CompDriver.L_cloudant ->
      let cld_conf = get_cld_config lconf in
      begin
	match get_comp_io conf with
	| Some io ->
	    (CALib.compile_nraenv_to_cloudant_with_harness (get_harness cld_conf) (idioticize (get_prefix cld_conf) nrule) op io, None)
	| None ->
	    (CALib.compile_nraenv_to_cloudant_with_harness_no_hierarchy (get_harness cld_conf) (idioticize (get_prefix cld_conf) nrule) op, None)
      end
  | _ ->
      raise (CACo_Error ("Unsupported target language: " ^ (get_target_lang lconf)))

let compile_nraenv_top conf (fname,sname,op) =
  let fpref = Filename.chop_extension fname in
  let (scomp,rest) = compile_nraenv_to_string conf sname (Filename.basename fpref) op in
  let fout = outname (target_f (get_dir conf) fpref) (suffix_target (get_comp_lang_config conf)) in
  make_file fout scomp;
  rest

(* Command line args *)
let margin = ref 120
let charsetbool = ref true

let args conf =
  [ ("-target", Arg.String (change_target (get_comp_lang_config conf)), "(Java/JS/Spark/Spark2/Cloudant)");
    ("-source", Arg.String (change_source (get_comp_lang_config conf)), "(Rule/OQL)");
    ("-dir", Arg.String (set_dir conf), "Target directory");
    ("-harness", Arg.String (set_harness (get_cld_config (get_comp_lang_config conf))), "Javascript Harness");
    ("-io", Arg.String (fun f -> set_comp_io conf (Util.string_of_file f)), "Schema");
    ("-stats", Arg.Unit (set_stats conf), "Produce statistics for produced query plans");
    ("-display-ils", Arg.Unit (set_display conf), "Display Intermediate Languages (NRAEnv, NNRC, NNRCMR)");
    ("-display-sexps", Arg.Unit (set_display_sexp conf), "Display Intermediate Languages (NRA) in S-expr form");
    ("-log-optims", Arg.Unit (Logger.set_trace), "Logs the optimizations/rewrites during compilation");
    ("-test-sexps", Arg.Unit (set_test_sexp conf), "Test Intermediate Languages (NRA) translation to/from S-expr");
    ("-display-ascii", Arg.Clear charsetbool, "Avoid unicode symbols");
    ("-display-margin", Arg.Set_int margin, "Set right margin for pretty printer");
    ("-display-dir", Arg.String (set_display_dir conf), "Target directory for IL files");
    ("-prefix", Arg.String (set_prefix (get_cld_config (get_comp_lang_config conf))), "Cloudant DB prefix");
    ("-java-imports", Arg.String (set_java_imports conf), "Additional imports for the Java runtime") ]

let anon_args conf f = set_comp_input conf f

let usage = "CaCo [-target language] [-source language] [-dir output] [-harness file] [-io file] [-display-ils] [-prefix name] rule1 rule2 ..."

(* Main *)

let nraenv_of_input lconf f : (string * CALib.nraenv) =
  match language_of_name (get_source_lang lconf) with
  | CompDriver.L_rule ->
      let s = Util.string_of_file f in
      (CALib.rule_to_nraenv_name s, CALib.rule_to_nraenv s)
  | CompDriver.L_oql ->
      let s = Util.string_of_file f in
      (CALib.oql_to_nraenv_name s, CALib.rule_to_nraenv s)
  | _ ->
      raise (CACo_Error ("Unsupported source language: " ^ (get_source_lang lconf)))

let display_dispatch charsetbool margin modelandtype conf fname op =
  match (modelandtype,get_comp_io conf) with
  | (Some schema,Some io) ->
      CALib.display_nraenv charsetbool margin schema io (DisplayUtil.get_display_fname conf fname) op
  | (None,Some io) ->
      CALib.display_nraenv_no_schema charsetbool margin io (DisplayUtil.get_display_fname conf fname) op
  | (Some schema,None) ->
      CALib.display_nraenv_no_io charsetbool margin schema (DisplayUtil.get_display_fname conf fname) op
  | (None,None) ->
      CALib.display_nraenv_no_schema_no_io charsetbool margin (DisplayUtil.get_display_fname conf fname) op
	
let compile_main conf fname =
  if fname <> "" then
    let (sname,op) = nraenv_of_input (get_comp_lang_config conf) fname in
    begin
      let modelandtype = compile_nraenv_top conf (fname,sname,op) in
      if !(get_target_display conf) then display_dispatch !charsetbool !margin modelandtype conf fname op else ();
      if !(get_target_display_sexp conf) then CALib.display_nraenv_sexp (DisplayUtil.get_display_fname conf fname) op else ();
      if !(get_target_stats conf) then Stats.display_stats conf fname else ()
    end

let () =
  let conf = default_comp_config () in
  begin
    Arg.parse (args conf) (anon_args conf) usage;
    List.iter (compile_main conf) (get_comp_inputs conf)
  end
