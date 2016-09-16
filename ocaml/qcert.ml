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
open CompDriver
open CompConfig
open ConfigUtil
open CloudantUtil

(* Command line args *)

let margin = ref 120
let charsetbool = ref true

let args_list conf =
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

let usage =
  Sys.argv.(0)
  ^" [-target language] [-source language] [-dir output] [-harness file] [-io file] [-display-ils] [-prefix name] rule1 rule2 ..."


(* Compilation *)

let compile (conf: comp_config) (file_name: string) : query list =
  let slang =
    begin match get_path (get_comp_lang_config conf) with
    | name :: _ ->
        begin match language_or_optim_of_name name with
        | LoO_language lang -> lang
        | _ ->
            raise (CACo_Error "The language of the source file must be specified")
        end
    | [] ->
        raise (CACo_Error "The language of the source file must be specified")
    end
  in
  let qname, q =
    ParseFile.parse_query_from_file slang file_name
  in
  let dv_conf = driver_conf_of_args conf qname in
  let dv = driver_of_conf dv_conf in
  let brand_model, camp_type = get_schema dv_conf in
  CompDriver.compile brand_model (Enhanced.Model.foreign_typing brand_model) dv q

(* Emit *)

let emit conf fname q =
  let fpref = Filename.chop_extension fname in
  let s = PrettyIL.pretty_query !charsetbool !margin q in
  let fout = outname (target_f (get_dir conf) fpref) (suffix_target (get_comp_lang_config conf)) in
  make_file fout s


(* Display *)

let display_dispatch charsetbool margin schema conf fname op =
  begin match (schema, get_comp_io conf) with
  | (Some schema, Some io) ->
      CALib.display_nraenv charsetbool margin
        schema io
        (DisplayUtil.get_display_fname conf fname) op
  | (None, Some io) ->
      CALib.display_nraenv_no_schema charsetbool margin
        io
        (DisplayUtil.get_display_fname conf fname) op
  | (Some schema, None) ->
      CALib.display_nraenv_no_io charsetbool margin
        schema
        (DisplayUtil.get_display_fname conf fname) op
  | (None, None) ->
      CALib.display_nraenv_no_schema_no_io charsetbool margin
        (DisplayUtil.get_display_fname conf fname) op
  end

(* Main *)

let () =
  let qconf = default_comp_config () in
  Arg.parse (args_list qconf) (anon_args qconf) usage;
  let schema =
    begin match get_comp_io qconf with
    | Some io -> Some (CALib.schema_of_io io)
    | None -> None
    end
  in
  let queries =
    List.map
      (fun file_name -> compile qconf)
      (get_comp_inputs qconf)
  in
  (* begin match !(get_target_display qconf) with *)
  (* | true -> *)
  (*     List.iter *)
  (*       (fun fname -> *)
  (*         display_dispatch !charsetbool !margin schema qconf fname op) *)
  (* | false -> () *)
  (* end; *)
  assert false (* XXX TODO XXX *)
