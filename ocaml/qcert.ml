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

(* Command line args *)

let args_list qconf =
  [ ("-target", Arg.String (QcertArg.set_target qconf), "(Java/JS/Spark/Spark2/Cloudant)");
    ("-source", Arg.String (QcertArg.set_source qconf), "(Rule/OQL)");
    ("-path", Arg.String (QcertArg.add_path qconf), "(rule/camp/oql/nra/nraenv/nnrc/nnrcmr/cldmr/dnnrc/dnnrc_typed/js/java/spark/spark2/cloudant)");
    ("-dir", Arg.String (QcertArg.set_dir qconf), "Target directory");
    ("-harness", Arg.String (CloudantUtil.set_harness qconf.QcertArg.qconf_cld_conf), "Javascript Harness");
    ("-io", Arg.String (QcertArg.set_io qconf), "Schema");
    (* ("-stats", Arg.Unit (set_stats conf), "Produce statistics for produced query plans"); *)
    ("-display-ils", Arg.Unit (QcertArg.set_display qconf), "Display Intermediate Languages (NRAEnv, NNRC, NNRCMR)");
    (* ("-display-sexps", Arg.Unit (set_display_sexp conf), "Display Intermediate Languages (NRA) in S-expr form"); *)
    (* ("-log-optims", Arg.Unit (Logger.set_trace), "Logs the optimizations/rewrites during compilation"); *)
    (* ("-test-sexps", Arg.Unit (set_test_sexp conf), "Test Intermediate Languages (NRA) translation to/from S-expr"); *)
    ("-display-ascii", Arg.Unit (PrettyIL.set_ascii qconf.QcertArg.qconf_display_config), "Avoid unicode symbols");
    ("-display-margin", Arg.Int (PrettyIL.set_margin qconf.QcertArg.qconf_display_config), "Set right margin for pretty printer");
    ("-display-dir", Arg.String (QcertArg.set_display_dir qconf), "Target directory for IL files");
    ("-prefix", Arg.String (CloudantUtil.set_prefix qconf.QcertArg.qconf_cld_conf), "Cloudant DB prefix");
    ("-java-imports", Arg.String (QcertArg.set_java_imports qconf), "Additional imports for the Java runtime") ]

let anon_args qconf f = QcertArg.add_input_file qconf f

let usage =
  Sys.argv.(0)
  ^" [-target language] [-source language] [-dir output] [-harness file] [-io file] [-display-ils] [-prefix name] rule1 rule2 ..."


let parse_args () =
  let qconf = QcertArg.default_qconf () in
  Arg.parse (args_list qconf) (anon_args qconf) usage;
  begin match qconf.QcertArg.qconf_source, qconf.QcertArg.qconf_target, qconf.QcertArg.qconf_path with
  | None, None, ((source :: _) as path) ->
      let target =
        begin match List.rev path with
        | target :: _ -> target
        | [] -> assert false
        end
      in
      qconf.QcertArg.qconf_source <- (Some source);
      qconf.QcertArg.qconf_target <- (Some target)
  | source_opt, target_opt, [] ->
      let source =
        begin match source_opt with
        | Some s -> s
        | None -> CompDriver.L_rule
        end
      in
      let target =
        begin match target_opt with
        | Some t -> t
        | None -> CompDriver.L_javascript
        end
      in
      let path =
        CompDriver.get_path_from_source_target source target
      in
      qconf.QcertArg.qconf_source <- (Some source);
      qconf.QcertArg.qconf_target <- (Some target);
      qconf.QcertArg.qconf_path <- path
  | Some _, _, _ :: _ ->
      raise (CACo_Error "options -source and -path can not be used simultaneously")
  | _, Some _, _ :: _ ->
      raise (CACo_Error "options -target and -path can not be used simultaneously")
  end;
  qconf

(* Parsing *)

let parse_file (qconf: QcertArg.qcert_config) (file_name: string) =
  let slang =
    begin match qconf.QcertArg.qconf_source with
    | Some lang -> lang
    | None -> assert false
    end
  in
  let qname, q =
    ParseFile.parse_query_from_file slang file_name
  in
  (qname, q)

(* Compilation *)

let compile_file (dv_conf: CompDriver.driver_config) (* XXX *)schema(* XXX *) (q: CompDriver.query) : CompDriver.query list =
  let brand_model, camp_type, foreign_typing = schema (* CompDriver.get_schema dv_conf *) in
  let dv = CompDriver.driver_of_conf brand_model foreign_typing dv_conf in
  let dv = CompDriver.fix_driver brand_model foreign_typing dv q in
  CompDriver.compile brand_model foreign_typing dv q

(* Emit *)

let emit_file (dv_conf: CompDriver.driver_config) (* XXX *)schema(* XXX *) display_conf dir file_name q =
  let brand_model, camp_type, foreign_typing = schema(* CompDriver.get_schema dv_conf *) in
  let s = PrettyIL.pretty_query display_conf q in
  let fpref = Filename.chop_extension file_name in
  let ext = ConfigUtil.suffix_of_language (CompDriver.language_of_query brand_model q) in
  let fout = outname (target_f dir fpref) ext in
  make_file fout s

(* S-expr *)
(* XXX TODO XXX *)
let emit_sexp_file conf schema file_name q = ()
  (* let brand_model, camp_type, foreign_typing = schema (\* CompDriver.get_schema dv_conf *\) in *)
  (* let s = PrettyIL.pretty_query !charsetbool !margin q in *)
  (* let fpref = Filename.chop_extension file_name in *)
  (* let ext = suffix_of_language (CompDriver.language_of_query brand_model q) in *)
  (* let fout = outname (target_f (get_dir conf) fpref) ext in *)
  (* make_file fout s *)


(* Main *)

let main_one_file qconf schema file_name =
  let brand_model, camp_type, foreign_typing = schema (* CompDriver.get_schema dv_conf *) in
  let (qname, q_source) = parse_file qconf file_name in
  let dv_conf = QcertArg.driver_conf_of_qcert_conf qconf (* schema *) qname in
  let queries = compile_file dv_conf schema q_source in
  let q_target =
    begin match List.rev queries with
    | q :: _ -> q
    | _ -> raise (CACo_Error "No compilation result!")
    end
  in
  let () =
    (* emit compiled query *)
    let dconf = qconf.QcertArg.qconf_display_config in
    let dir = qconf.QcertArg.qconf_dir in
    emit_file dv_conf schema dconf dir file_name q_target
  in
  let () =
    (* display intermediate languages *)
    begin match qconf.QcertArg.qconf_display with
    | true ->
        let _ =
          List.fold_left
            (fun fname q ->
              let dconf = qconf.QcertArg.qconf_display_config in
              let dir = qconf.QcertArg.qconf_display_dir in
              emit_file dv_conf schema dconf dir fname q;
              let suff =
                ConfigUtil.suffix_of_language (CompDriver.language_of_query brand_model q)
              in
              (Filename.chop_extension fname)^suff)
            file_name queries
        in ()
    | false -> ()
    end
  in
  (* let () = *)
  (*   (\* Display S-expr *\) *)
  (*   begin match !(get_target_display_sexp qconf) with *)
  (*   | true -> *)
  (*       let _ = *)
  (*         List.fold_left *)
  (*           (fun fname q -> *)
  (*             emit_sexp_file qconf schema fname q; *)
  (*             let suff = *)
  (*               suffix_of_language (CompDriver.language_of_query brand_model q) *)
  (*             in *)
  (*             (Filename.chop_extension fname)^suff) *)
  (*           file_name queries *)
  (*       in () *)
  (*   | false -> () *)
  (*   end *)
  (* in *)
  ()

let () =
  let qconf = parse_args () in
  let schema =
    begin match qconf.QcertArg.qconf_io with
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
    qconf.QcertArg.qconf_input_files
