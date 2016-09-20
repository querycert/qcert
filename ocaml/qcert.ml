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
  Arg.align
    [ ("-source", Arg.String (QcertArg.set_source qconf),
       "<lang> Indicates the language for of thesource file (default: Rule)");
      ("-target", Arg.String (QcertArg.set_target qconf),
       "<lang> Indicates the language for the target query (default: js)");
      ("-path", Arg.String (QcertArg.add_path qconf),
       "<lang> Use to define compilation path");
      ("-dir", Arg.String (QcertArg.set_dir qconf),
       "<dir> Target directory for the emited code");
      ("-js-runtime", Arg.String (CloudantUtil.set_harness qconf.QcertArg.qconf_cld_conf),
       "<harness.js> JavaScript runtime");
      ("-io", Arg.String (QcertArg.set_io qconf),
       "<file.io> Schema and inputs data for evaluation");
      (* ("-stats", Arg.Unit (set_stats conf), *)
      (*    " Produce statistics for the target query"); *)
      (* ("-stats-all", Arg.Unit (set_stats conf), *)
      (*    " Produce statistics for all intermediate queries"); *)
      ("-emit-all", Arg.Unit (QcertArg.set_emit_all qconf),
       " Emit generated code of all intermediate queries");
      (* ("-emit-sexp", Arg.Unit (QcertArg.set_sexpr qconf), *)
      (*  " Emit the target query as an s-expression"); *)
      (* ("-emit-sexp-all", Arg.Unit (QcertArg.set_sexprs qconf), *)
      (*  " Emit all intermediate queries as s-expressions"); *)
      (* ("-log-optims", Arg.Unit (Logger.set_trace), *)
      (*  " Logs the optimizations/rewrites during compilation"); *)
      ("-ascii", Arg.Unit (PrettyIL.set_ascii qconf.QcertArg.qconf_pretty_config),
       " Avoid unicode symbols in emited queries");
      ("-margin", Arg.Int (PrettyIL.set_margin qconf.QcertArg.qconf_pretty_config),
       "<n> Set right margin for emited queries");
      ("-cld-prefix", Arg.String (CloudantUtil.set_prefix qconf.QcertArg.qconf_cld_conf),
       "<pref> Cloudant DB prefix");
      ("-java-imports", Arg.String (QcertArg.set_java_imports qconf),
       "<imports> Additional imports for the Java runtime");
      (* ("-eval", Arg.Unit XXX, "Evaluate the target query"); *)
      (* ("-eval-all", Arg.Unit XXX, "Evaluate all the intermediate queries"); *)
      ("-vinit", Arg.String (QcertArg.add_vdirst qconf),
       "<init> Set the name init variable for the map-reduce backends");
      ("-vdistr", Arg.String (QcertArg.add_vdirst qconf),
       "<x> Declare x as a distributed variable");
      ("-vlocal", Arg.String (QcertArg.add_vlocal qconf),
       "<x> Declare x as a local variable");
    ]

let anon_args qconf f = QcertArg.add_input_file qconf f

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
  let buff = Buffer.create 128 in
  let str_ff = Format.formatter_of_buffer buff in
  let () =
    Format.fprintf str_ff "%a"
      (Format.pp_print_list
         ~pp_sep:(fun ff () -> Format.fprintf ff ", ")
         (fun ff lang -> Format.fprintf ff "%s" (ConversionUtil.name_of_language lang)))
      languages
  in
  Format.pp_print_flush str_ff ();
  Buffer.contents buff

let usage =
  "Q*cert - Query compiler\n"^
  "Supported languages are:\n"^
  "  "^languages_string^
  "\n"^
  "Usage: "^Sys.argv.(0)^" [options] query1 query2 ..."


let parse_args () =
  let qconf = QcertArg.default_qconf () in
  Arg.parse (args_list qconf) (anon_args qconf) usage;
  let _schema =
    begin match qconf.QcertArg.qconf_io with
    | Some io ->
        qconf.QcertArg.qconf_schema <- TypeUtil.schema_of_io_json (ParseString.parse_io_from_string io)
    | None ->
        ()
    end
  in
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

let compile_file (dv_conf: CompDriver.driver_config) (schema: TypeUtil.schema) (path: CompDriver.language list) (q: CompDriver.query) : CompDriver.query list =
  let brand_model = schema.TypeUtil.sch_brand_model in
  let foreign_typing = schema.TypeUtil.sch_foreign_typing in
  let dv = CompDriver.driver_of_path brand_model foreign_typing dv_conf path in
  let dv = CompDriver.fix_driver brand_model foreign_typing dv q in
  CompDriver.compile brand_model foreign_typing dv q

(* Emit *)

let emit_file (dv_conf: CompDriver.driver_config) (schema: TypeUtil.schema) pretty_conf dir file_name q =
  let brand_model = schema.TypeUtil.sch_brand_model (* CompDriver.get_schema dv_conf *) in
  let s = PrettyIL.pretty_query pretty_conf q in
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

let main_one_file qconf file_name =
  let schema = qconf.QcertArg.qconf_schema in
  let brand_model = schema.TypeUtil.sch_brand_model (* CompDriver.get_schema dv_conf *) in
  let (qname, q_source) = parse_file qconf file_name in
  let dv_conf = QcertArg.driver_conf_of_qcert_conf qconf (* schema *) qname in
  let queries = compile_file dv_conf schema qconf.QcertArg.qconf_path q_source in
  let q_target =
    begin match List.rev queries with
    | q :: _ -> q
    | _ -> raise (CACo_Error "No compilation result!")
    end
  in
  let () =
    (* emit compiled query *)
    let pconf = qconf.QcertArg.qconf_pretty_config in
    let dir = qconf.QcertArg.qconf_dir in
    emit_file dv_conf schema pconf dir file_name q_target
  in
  let () =
    (* Emit intermediate queries *)
    begin match qconf.QcertArg.qconf_emit_all with
    | true ->
        let _ =
          List.fold_left
            (fun fname q ->
              let pconf = qconf.QcertArg.qconf_pretty_config in
              let dir = qconf.QcertArg.qconf_dir in
              emit_file dv_conf schema pconf dir fname q;
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
  List.iter
    (fun file_name -> main_one_file qconf file_name)
    qconf.QcertArg.qconf_input_files
