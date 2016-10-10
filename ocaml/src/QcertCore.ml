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


type result = {
    res_emit : result_file;
    res_emit_all : result_file list;
    res_emit_sexp : result_file;
    res_emit_sexp_all : result_file list;
    res_eval : result_file;
    res_eval_all : result_file list;
    res_stat : string;
    res_stat_all : string list;
    res_stat_tree : result_file;
  }
and result_file = {
    res_file : string;
    res_content : string;
  }

let no_result_file =
  { res_file = ""; res_content = ""; }

(******************)
(* Core functions *)
(******************)

(* Message *)

let fprint_comilation_path ff gconf =
  let spath = QcertUtil.string_of_path " -> " gconf.gconf_path in
  Format.fprintf ff "Compiling from %s to %s:@\n"
    (QcertUtil.name_of_language gconf.gconf_source)
    (QcertUtil.name_of_language gconf.gconf_target);
  Format.fprintf ff "  %s@." spath

(* Parsing *)

let parse_string (gconf: QcertConfig.global_config) (query_s: string) =
  let slang = gconf.gconf_source in
  let qname, q =
    begin match gconf.gconf_source_sexp with
    | false ->
        ParseString.parse_query_from_string slang query_s
    | true ->
        let sexp = ParseString.parse_sexp_from_string query_s in
        let name = QcertUtil.name_of_language slang in (* XXX Is it a good name? XXX *)
        let q = AstsToSExp.sexp_to_query slang sexp in
        (name, q)
    end
  in
  (qname, q)

(* Compilation *)

let compile_query (dv_conf: QDriver.driver_config) (schema: TypeUtil.schema) (path: QLang.language list) (q: QLang.query) : QLang.query list =
  let brand_model = schema.TypeUtil.sch_brand_model in
  let foreign_typing = schema.TypeUtil.sch_foreign_typing in
  let dv = QDriver.driver_of_path brand_model dv_conf path in
  let () = QcertUtil.driver_no_error dv in
  let dv = QDriver.fix_driver brand_model dv q in
  let queries = QDriver.compile brand_model foreign_typing dv q in
  let () = List.iter QcertUtil.query_no_error queries in
  queries

(* Emit *)

let emit_string (dv_conf: QDriver.driver_config) (schema: TypeUtil.schema) pretty_conf dir file_name q =
  let s = PrettyIL.pretty_query pretty_conf q in
  let brand_model = schema.TypeUtil.sch_brand_model in
  let fpref = Filename.chop_extension file_name in
  let ext = ConfigUtil.suffix_of_language (QLang.language_of_query brand_model q) in
  let fout = outname (target_f dir fpref) ext in
  { res_file = fout; res_content = s; }

(* Emit s-expr *)

let emit_sexpr_string (schema: TypeUtil.schema) dir file_name q =
  let sexp = AstsToSExp.query_to_sexp q in
  let s = SExp.sexp_to_string sexp in
  let brand_model = schema.TypeUtil.sch_brand_model in
  let fpref = Filename.chop_extension file_name in
  let fpost = QcertUtil.name_of_language (QLang.language_of_query brand_model q) in
  let fout = outname (target_f dir (fpref^"_"^fpost)) ".sexp" in
  { res_file = fout; res_content = s; }

(* Eval *)

let eval_string (data:DataUtil.io_input) (schema: TypeUtil.schema) dir file_name q =
  let ev_input = Compiler.Ev_in_world data in
  let brand_model = schema.TypeUtil.sch_brand_model in
  let brand_relation = TypeUtil.brand_relation_of_brand_model brand_model in
  let language_name = QcertUtil.name_of_language (QLang.language_of_query brand_model q) in
  let ev_output = QEval.eval_query brand_relation brand_model q ev_input in
  let ev_data =
    begin match ev_output with
    | Compiler.Ev_out_unsupported ->
	QData.drec [(Util.char_list_of_string "error", QData.dstring (Util.char_list_of_string ("Eval not supported for" ^ language_name)))]
    | Compiler.Ev_out_failed ->
	QData.drec [(Util.char_list_of_string "error", QData.dstring (Util.char_list_of_string "Eval failed"))]
    | Compiler.Ev_out_returned d ->
	d
    end
  in
  let s = Util.string_of_char_list (QData.dataToJS (Util.char_list_of_string "\"") ev_data) in
  let fpref = Filename.chop_extension file_name in
  let fpost = language_name in
  let fout = outname (target_f dir (fpref^"_"^fpost)) ".json" in
  { res_file = fout; res_content = s; }

(* Stats *)

let stat_query (schema: TypeUtil.schema) q =
  let brand_model = schema.TypeUtil.sch_brand_model in
  string (QStat.json_stat_of_query brand_model q)

(* Stats tree *)

let stat_tree_query (schema: TypeUtil.schema) dir file_name q =
  let name = char_list_of_string (Filename.chop_extension file_name) in
  let brand_model = schema.TypeUtil.sch_brand_model in
  let stats = QStat.json_stat_tree_of_query brand_model name q in
  let fpref = Filename.chop_extension file_name in
  let fout = outname (target_f dir fpref) "_stats.json" in
  { res_file = fout; res_content = string stats; }

(* Main *)

let main gconf (file_name, query_s) =
  let schema = gconf.gconf_schema in
  let data = gconf.gconf_data in
  let brand_model = schema.TypeUtil.sch_brand_model in
  let (qname, q_source) = parse_string gconf query_s in
  let class_name =
    (* for Java code generation *)
    Filename.basename (Filename.chop_extension file_name)
  in
  let dv_conf = QcertConfig.driver_conf_of_global_conf gconf qname class_name in
  let queries = compile_query dv_conf schema gconf.gconf_path q_source in
  let q_target =
    begin match List.rev queries with
    | q :: _ -> q
    | _ -> raise (Qcert_Error "No compilation result!")
    end
  in
  let res_emit =
    (* emit compiled query *)
    let pconf = gconf.gconf_pretty_config in
    let dir =
      begin match gconf.gconf_dir_target with
      | Some dir -> Some dir
      | None -> gconf.gconf_dir
      end
    in
    emit_string dv_conf schema pconf dir file_name q_target
  in
  let res_emit_all =
    (* Emit intermediate queries *)
    if gconf.gconf_emit_all then
      let _, l =
        List.fold_left
          (fun (fname, acc) q ->
            let pconf = gconf.gconf_pretty_config in
            let dir = gconf.gconf_dir in
            let res = emit_string dv_conf schema pconf dir fname q in
            let suff =
              ConfigUtil.suffix_of_language (QLang.language_of_query brand_model q)
            in
            let fname = (Filename.chop_extension fname)^suff in
            (fname, res::acc))
          (file_name, []) queries
      in
      List.rev l
    else
      []
  in
  let res_emit_sexp =
    (* emit-sexp compiled query *)
    if gconf.gconf_emit_sexp then
      emit_sexpr_string schema gconf.gconf_dir file_name q_target
    else
      no_result_file
  in
  let res_emit_sexp_all =
    (* emit-sexp-all intermediate queries *)
    if gconf.gconf_emit_sexp_all then
      let _, l =
        List.fold_left
          (fun (fname, acc) q ->
            let res = emit_sexpr_string schema gconf.gconf_dir fname q in
            let suff =
              ConfigUtil.suffix_of_language (QLang.language_of_query brand_model q)
            in
            let fname = (Filename.chop_extension fname)^suff in
            (fname, res::acc))
          (file_name, []) queries
      in
      List.rev l
    else
      []
  in
  let res_eval =
    (* eval compiled query *)
    if gconf.gconf_eval then
      eval_string data schema gconf.gconf_dir file_name q_target
    else
      no_result_file
  in
  let res_eval_all =
    (* eval-all intermediate queries *)
    if gconf.gconf_eval_all then
      let _, l =
        List.fold_left
          (fun (fname, acc) q ->
            let res = eval_string data schema gconf.gconf_dir fname q in
            let suff =
              ConfigUtil.suffix_of_language (QLang.language_of_query brand_model q)
            in
            let fname = (Filename.chop_extension fname)^suff in
            (fname, res::acc))
          (file_name, []) queries
      in
      List.rev l
    else
      []
  in
  let res_stat =
    if gconf.gconf_stat then
      stat_query schema q_target
    else
      ""
  in
  let res_stat_all =
    if gconf.gconf_stat_all then
      List.map (fun q -> stat_query schema q) queries
    else
      []
  in
  let res_stat_tree =
    if gconf.gconf_stat_tree then
      stat_tree_query schema gconf.gconf_dir file_name q_source
    else
      no_result_file
  in
  { res_emit = res_emit;
    res_emit_all = res_emit_all;
    res_emit_sexp = res_emit_sexp;
    res_emit_sexp_all = res_emit_sexp_all;
    res_eval = res_eval;
    res_eval_all = res_eval_all;
    res_stat = res_stat;
    res_stat_all = res_stat_all;
    res_stat_tree = res_stat_tree; }

