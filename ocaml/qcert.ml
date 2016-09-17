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
open Compiler.EnhancedCompiler
open ConfigUtil
open CloudantUtil

(* Command line args *)

let margin = ref 120
let charsetbool = ref true

let args_list conf =
  [ ("-target", Arg.String (change_target (get_comp_lang_config conf)), "(Java/JS/Spark/Spark2/Cloudant)");
    ("-source", Arg.String (change_source (get_comp_lang_config conf)), "(Rule/OQL)");
    ("-path", Arg.String (add_path  (get_comp_lang_config conf)), "(rule/camp/oql/nra/nraenv/nnrc/nnrcmr/cldmr/dnnrc/dnnrc_typed/js/java/spark/spark2/cloudant)");
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

let usage =
  Sys.argv.(0)
  ^" [-target language] [-source language] [-dir output] [-harness file] [-io file] [-display-ils] [-prefix name] rule1 rule2 ..."


let parse_args () =
  let qconf = default_comp_config () in
  Arg.parse (args_list qconf) (anon_args qconf) usage;
  qconf

(* Parsing *)

let parse_file (qconf: comp_config) (file_name: string) =
  let slang =
    begin match get_path (get_comp_lang_config qconf) with
    | name :: _ -> language_of_name name
    | [] ->
        raise (CACo_Error "The language of the source file must be specified")
    end
  in
  let qname, q =
    ParseFile.parse_query_from_file slang file_name
  in
  (qname, q)

(* Compilation *)

let compile_file (dv_conf: CompDriver.driver_config) schema (q: CompDriver.query) : CompDriver.query list =
  let brand_model, camp_type, foreign_typing = schema (* CompDriver.get_schema dv_conf *) in
  let dv = CompDriver.driver_of_conf brand_model foreign_typing dv_conf in
  let dv = CompDriver.fix_driver brand_model foreign_typing dv q in
  CompDriver.compile brand_model foreign_typing dv q

(* Emit *)

let emit_file conf schema file_name q =
  let brand_model, camp_type, foreign_typing = schema (* CompDriver.get_schema dv_conf *) in
  let s = PrettyIL.pretty_query !charsetbool !margin q in
  let fpref = Filename.chop_extension file_name in
  let ext = suffix_of_language (CompDriver.language_of_query brand_model q) in
  let fout = outname (target_f (get_dir conf) fpref) ext in
  make_file fout s


(* Main *)

let main_one_file qconf schema file_name =
  let brand_model, camp_type, foreign_typing = schema (* CompDriver.get_schema dv_conf *) in
  let (qname, q_source) = parse_file qconf file_name in
  let dv_conf = driver_conf_of_args qconf (* schema *) qname in
  let queries = compile_file dv_conf schema q_source in
  let q_target =
    begin match List.rev queries with
    | q :: _ -> q
    | _ -> raise (CACo_Error "No compilation result!")
    end
  in
  begin match !(get_target_display qconf) with
  | true ->
      let _ =
        List.fold_left
          (fun fname q ->
            emit_file qconf schema fname q;
            let suff =
              suffix_of_language (CompDriver.language_of_query brand_model q)
            in
            (Filename.chop_extension fname)^suff)
          file_name queries
      in ()
  | false -> emit_file qconf schema file_name q_target
  end

let () =
  let qconf = parse_args () in
  let schema =
    begin match get_comp_io qconf with
    | Some io ->
        let (schema_content, camp_type) =
          TypeUtil.extract_schema (ParseString.parse_io_from_string io)
        in
        let brand_model, camp_type =
          TypeUtil.process_schema schema_content camp_type
        in
        (brand_model, camp_type, Enhanced.Model.foreign_typing brand_model)
    | None ->
        (* XXX TODO XXX *)
        (* (RType.make_brand_model brand_rel [], []) *)
        assert false
    end
  in
  List.iter
    (fun file_name -> main_one_file qconf schema file_name)
    (get_comp_inputs qconf)
