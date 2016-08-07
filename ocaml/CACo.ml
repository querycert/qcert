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
open ParseUtil
open CloudantUtil
open DisplayUtil
open FrontUtil
open Compiler.EnhancedCompiler

(* Compile from NRAEnv *)

let compile_algenv_to_string (conf:comp_config) (nrule:string) (basename:string) op =
  let op = if !(get_test_sexp conf) then TestUtil.sexp_algenv_top_test (basename,op) else op in
  let lconf = get_comp_lang_config conf in
  match get_target_lang lconf with
  | Java ->
      (* this uses 'basename': the file name since the java class name needs to be the same as the file name *)
      (string_of_char_list (CompBack.nrc_to_java_code_gen (Util.char_list_of_string basename) (Util.char_list_of_string (get_java_imports conf)) (CompCore.tcompile_nraenv_to_nnrc_typed_opt op)), None)
  | JS ->
     (string_of_char_list (CompBack.nrc_to_js_code_gen (CompCore.tcompile_nraenv_to_nnrc_typed_opt op)), None)
  | Spark ->
     (let (env_var,mr) = CompCore.tcompile_nraenv_to_nnrcmr_chain_typed_opt op in
      string_of_char_list (CompBack.mrchain_to_spark_code_gen_with_prepare (Util.char_list_of_string nrule) mr), None)
  | Spark2 ->
     let io =
	match get_comp_io conf with
	| Some io -> io
	| None -> raise (Failure "Spark2 target requires a schema I/O file")
      in
      let (schema_content,wmType) = TypeUtil.extract_schema io in
      let (brand_model,wmRType) = TypeUtil.process_schema schema_content wmType in
      let oe = CompCore.tcompile_nraenv_to_dnnrc_dataset_opt
                brand_model
                (Enhanced.Model.foreign_typing brand_model)
                op
                wmRType
      in
      begin
        match oe with
          Some e ->
          (string_of_char_list
	    (CompBack.dnrc_to_scala_code_gen
               brand_model
               (Enhanced.Model.foreign_typing brand_model)
	       wmRType (Util.char_list_of_string nrule) e),
	   Some (brand_model, wmRType))
        | None -> raise (CACo_Error ("Type inference failed"))
      end
  | Cloudant ->
     (let cld_conf = get_cld_config lconf in
      cloudant_compile_from_nra (get_cld cld_conf) (get_harness cld_conf) (idioticize (get_prefix cld_conf) nrule) op (DataUtil.get_hierarchy_cloudant (get_comp_io conf)), None)
  | _ ->
      raise (CACo_Error ("Target not supported by CACo"))

let compile_algenv_top conf (fname,sname,alg) =
  let fpref = Filename.chop_extension fname in
  let (scomp,rest) = compile_algenv_to_string conf sname (Filename.basename fpref) alg in
  let fout = outname (target_f (get_dir conf) fpref) (suffix_target (get_comp_lang_config conf)) in
  make_file fout scomp;
  rest

(* Command line args *)
let args conf =
  [ ("-target", Arg.String (change_target (get_comp_lang_config conf)), "(Java/JS/Spark/Spark2/Cloudant)");
    ("-source", Arg.String (change_source (get_comp_lang_config conf)), "(Rule/OQL)");
    ("-dir", Arg.String (set_dir conf), "Target directory");
    ("-harness", Arg.String (set_harness (get_cld_config (get_comp_lang_config conf))), "Javascript Harness");
    ("-io", Arg.String (fun f -> set_comp_io conf (ParseFile.parse_io_from_file f)), "Schema");
    ("-stats", Arg.Unit (set_stats conf), "Produce statistics for produced query plans");
    ("-display-ils", Arg.Unit (set_display conf), "Display Intermediate Languages (NRAEnv, NNRC, NNRCMR)");
    ("-display-sexps", Arg.Unit (set_display_sexp conf), "Display Intermediate Languages (NRA) in S-expr form");
    ("-log-optims", Arg.Unit (Logger.set_trace), "Logs the optimizations/rewrites during compilation");
    ("-test-sexps", Arg.Unit (set_test_sexp conf), "Test Intermediate Languages (NRA) translation to/from S-expr");
    ("-display-ascii", Arg.Unit (PrettyIL.set_ascii (get_pretty_config conf)), "Avoid unicode symbols");
    ("-display-margin", Arg.Int (PrettyIL.set_margin (get_pretty_config conf)), "Set right margin for pretty printer");
    ("-display-dir", Arg.String (set_display_dir conf), "Target directory for IL files");
    ("-prefix", Arg.String (set_prefix (get_cld_config (get_comp_lang_config conf))), "Cloudant DB prefix");
    ("-java-imports", Arg.String (set_java_imports conf), "Additional imports for the Java runtime");
    ("-curl", Arg.Unit (set_curl (get_cld_config (get_comp_lang_config conf))), "Uses Curl for Cloudant") ]

let anon_args conf f = set_comp_input conf f

let usage = "CaCo [-target language] [-source language] [-dir output] [-harness file] [-io file] [-display-ils] [-prefix name] [-curl] rule1 rule2 ..."

(* Main *)

let compile_main conf f =
  if f <> "" then
    let (fname,sname,op) = alg_of_input (get_comp_lang_config conf) f in
    begin
      let modelandtype = compile_algenv_top conf (fname,sname,op) in
      if !(get_target_display conf) then display_algenv_top conf modelandtype (fname,op) else ();
      if !(get_target_display_sexp conf) then sexp_algenv_top conf (fname,op) else ();
      if !(get_target_stats conf) then Stats.display_stats conf fname else ()
    end

let () =
  let conf = default_comp_config () in
  begin
    Arg.parse (args conf) (anon_args conf) usage;
    List.iter (compile_main conf) (get_comp_inputs conf)
  end
