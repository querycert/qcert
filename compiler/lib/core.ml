(*
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

open Config

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
    res_optim_config : result_file;
    res_validates : bool;
  }
and result_file = {
    res_file : string;
    res_lang : string;
    res_content : string;
  }

let no_result_file =
  { res_file = ""; res_lang = ""; res_content = ""; }

(******************)
(* Core functions *)
(******************)

(* Message *)

let fprint_compilation_path ff gconf =
  if not gconf.gconf_quiet then
    begin
      let spath = Compiler_util.string_of_path " -> " gconf.gconf_path in
      Format.fprintf ff "Compiling from %s to %s:@\n"
        (Compiler_util.name_of_language gconf.gconf_source)
        (Compiler_util.name_of_language gconf.gconf_target);
      Format.fprintf ff "  %s@." spath
    end

(* Parsing *)

let src_and_schema (src: string) (schema: string) = 
  Format.sprintf "{\"source\":\"%s\", \"schema\":%s}" (String.escaped src) schema

let parse_string (gconf: global_config) (query_s: string) =
  let schema =
    begin match gconf.gconf_io with
    | None -> "{}"
    | Some (IO_file f) ->
  begin match f with
  | Some s -> string_of_file s
  | None -> "{}"
  end 
    | Some (IO_components (fin,fout,fschema)) ->
  begin match fschema with
  | Some s -> s
  | None -> "{}"
  end
    end
  in
  let slang = gconf.gconf_source in
  let the_query =
    begin match slang with
    | Compiler.L_tech_rule -> src_and_schema query_s schema
    | _ -> query_s
    end in
  if gconf.gconf_source_sexp
  then
    let sexp = Parse_string.parse_sexp_from_string query_s in
    Ast_to_sexp.sexp_to_query slang sexp
  else
    snd (Parse_string.parse_query_from_string slang the_query)

(* Compilation *)

let compile_query (dv_conf: QDriver.driver_config) (schema: Type_util.schema) (path: QLang.language list) (q: QLang.query) : QLang.query list =
  let brand_model = schema.Type_util.sch_brand_model in
  let foreign_typing = schema.Type_util.sch_foreign_typing in
  let dv = QDriver.driver_of_path brand_model dv_conf path in
  let () = Compiler_util.driver_no_error dv in
  let queries = QDriver.compile brand_model foreign_typing dv q in
  let () = List.iter Compiler_util.query_no_error queries in
  queries

(* Emit *)

let emit_string (dv_conf: QDriver.driver_config) (schema: Type_util.schema) pretty_conf dir file_name q =
  let h = Type_util.raw_inheritance_of_schema schema in
  Pretty_common.set_inheritance pretty_conf h; (* Add inheritance to pretty printing configuration for Cloudant code emition *)
  let s = Output.output_query pretty_conf q in
  let brand_model = schema.Type_util.sch_brand_model in
  let fpref = Filename.chop_extension file_name in
  let lang = QLang.language_of_query brand_model q in
  let ext = Config_util.suffix_of_language lang in
  let fout = outname (target_f dir fpref) ext in
  { res_file = fout; res_lang = Compiler_util.name_of_language lang; res_content = s; }

(* Emit s-expr *)

let emit_sexpr_string (schema: Type_util.schema) dir file_name q =
  let sexp = Ast_to_sexp.query_to_sexp q in
  let s = Sexp.sexp_to_string sexp in
  let brand_model = schema.Type_util.sch_brand_model in
  let fpref = Filename.chop_extension file_name in
  let lang = QLang.language_of_query brand_model q in
  let fpost = Compiler_util.name_of_language lang in
  let fout = outname (target_f dir (fpref^"_"^fpost)) ".sexp" in
  { res_file = fout; res_lang = Compiler_util.name_of_language lang; res_content = s; }

(* Emit sio file *)

let emit_one_sio file_name dir one_sdata =
  let (const_name,const_sio) = one_sdata in
  let fpref = Filename.chop_extension file_name in
  let fout = outname (target_f dir (fpref^"."^(string_of_char_list const_name))) ".sio" in
  { res_file = fout; res_lang = "sio"; res_content = string_of_char_list const_sio; }

let emit_sio (ev_input:Data_util.content_input) (schema: Type_util.schema) (file_name:string) dir =
  let sdata = Type_util.content_sdata_of_data schema ev_input in
  List.map (emit_one_sio file_name dir) sdata

(* Eval *)

let lift_data_to_ddata globals (var:char list * QData.qdata) =
  let vname = fst var in
  let data = snd var in
  let loc =
    begin try (List.assoc vname globals).Compiler.constant_localization with
    | Not_found -> Compiler.Vlocal
    end
  in
  begin match loc with
  | Compiler.Vlocal -> (vname,QData.dlocal data)
  | Compiler.Vdistr ->
      begin match QData.ddistr data with
      | Some dd -> (vname,dd)
      | None -> raise  (Qcert_Error ("Distributed variable " ^ (string_of_char_list vname) ^ " should be initialized with an input collection"))
      end
  end

(* Debug *)

let get_dist (dd:QData.qddata) =
  begin match dd with
  | Compiler.Ddistr _ -> "distributed"
  | Compiler.Dlocal _ -> "local"
  end

let get_value (dd:QData.qddata) =
  begin match dd with
  | Compiler.Ddistr d ->
      string_of_char_list (QData.qdataStringify (char_list_of_string "\"") (QData.dcoll d))
  | Compiler.Dlocal d ->
      string_of_char_list (QData.qdataStringify (char_list_of_string "\"") d)
  end
    
let print_input_var (v:char list * QData.qddata) =
  Printf.printf "Var: %s is %s and has value:\n" (string_of_char_list (fst v)) (get_dist (snd v));
  Printf.printf "%s\n" (get_value (snd v))
    
let print_input ev_input =
  List.iter print_input_var ev_input

let eval_string (validate:bool) (debug:bool) (quiet:bool) (ev_input:Data_util.content_input) (expected_output:Data_util.content_output) (schema: Type_util.schema) dir file_name q =
  let brand_model = schema.Type_util.sch_brand_model in
  let brand_relation = Type_util.brand_relation_of_brand_model brand_model in
  let globals = schema.Type_util.sch_globals in
  let ev_input = List.map (lift_data_to_ddata globals) ev_input in
  (* print_input ev_input; *)
  let language_name = Compiler_util.name_of_language (QLang.language_of_query brand_model q) in
  let ev_output =
    begin match debug with
    | false -> QEval.eval_query brand_relation brand_model q ev_input
    | true -> QEval.eval_query_debug brand_relation brand_model q ev_input
    end
  in
  let ev_data =
    begin match ev_output with
    | Compiler.Ev_out_unsupported msg ->
        QData.drec [(char_list_of_string "error", QData.dstring msg)]
    | Compiler.Ev_out_failed ->
        QData.drec [(char_list_of_string "error", QData.dstring (char_list_of_string "Eval failed"))]
    | Compiler.Ev_out_returned d ->
        d
    | Compiler.Ev_out_returned_debug s ->
        QData.drec [(char_list_of_string "debug", QData.dstring s)]
    end
  in
  let queryname = Filename.chop_extension file_name in
  let res_validates =
    if validate
    then Check_util.validate_result quiet queryname language_name expected_output (Some ev_data)
    else true
  in
  let s = string_of_char_list (QData.qdataStringify (char_list_of_string "\"") ev_data) in
  let fpref = queryname in
  let fpost = language_name in
  let fout = outname (target_f dir (fpref^"_"^fpost)) ".json" in
  ({ res_file = fout; res_lang = language_name; res_content = s; }, res_validates)

(* Stats *)

let stat_query (schema: Type_util.schema) q =
  let brand_model = schema.Type_util.sch_brand_model in
  string (QStat.json_stat_of_query brand_model q)

(* Stats tree *)

let stat_tree_query (schema: Type_util.schema) dir file_name q =
  let name = char_list_of_string (Filename.chop_extension file_name) in
  let brand_model = schema.Type_util.sch_brand_model in
  let language_name = Compiler_util.name_of_language (QLang.language_of_query brand_model q) in
  let stats = QStat.json_stat_tree_of_query brand_model name q in
  let fpref = Filename.chop_extension file_name in
  let fout = outname (target_f dir fpref) "_stats.json" in
  { res_file = fout; res_lang = language_name; res_content = string stats; }

(* Optim config *)
let json_of_optim_config (optim_config:Compiler.optim_config) =
  let optim_config =
    if optim_config = []
    then
      QDriver.optim_config_default
    else
      optim_config
  in
  QDriver.optim_config_to_json optim_config
let emit_optim_config optim_config dir file_name =
  let fpref = Filename.chop_extension file_name in
  let fout = outname (target_f dir fpref) "_optim.json" in
  let optims_data = json_of_optim_config optim_config in
  let optims = string_of_char_list (QData.json_to_string optims_data) in
  { res_file = fout; res_lang = "json"; res_content = optims; }
    
(* Main *)

let main_data gconf file_name =
  let schema = gconf.gconf_schema in
  let input = gconf.gconf_input in
  let sinput = (* emit sio *)
    let dir =
      begin match gconf.gconf_dir_target with
      | Some dir -> Some dir
      | None -> gconf.gconf_dir
      end
    in
    emit_sio input schema file_name dir
  in
  sinput

let main gconf (file_name, query_s) =
  let schema = gconf.gconf_schema in
  let input = gconf.gconf_input in
  let expected_output = gconf.gconf_output in
  let brand_model = schema.Type_util.sch_brand_model in
  let basename =
    (* for Java code generation *)
    Filename.basename (Filename.chop_extension file_name)
  in
  let q_source = parse_string gconf query_s in
  let qname =
    begin match gconf.gconf_qname with
    | None -> basename
    | Some name -> name
    end
  in
  let class_name = gconf.gconf_class_name in
  let dv_conf = driver_conf_of_global_conf gconf qname class_name in
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
              Config_util.suffix_of_language (QLang.language_of_query brand_model q)
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
              Config_util.suffix_of_language (QLang.language_of_query brand_model q)
            in
            let fname = (Filename.chop_extension fname)^suff in
            (fname, res::acc))
          (file_name, []) queries
      in
      List.rev l
    else
      []
  in
  let (res_eval, res_validates) =
    (* eval compiled query *)
    if gconf.gconf_eval then
      eval_string
        gconf.gconf_eval_validate
        gconf.gconf_eval_debug
        gconf.gconf_quiet
        input
        expected_output
        schema
        gconf.gconf_dir
        file_name
        q_target
    else
      (no_result_file, true)
  in
  let res_validates_all = ref res_validates in
  let res_eval_all =
    (* eval-all intermediate queries *)
    if gconf.gconf_eval_all then
      let _, l =
        List.fold_left
          (fun (fname, acc) q ->
            let (res,res_validates) =
              eval_string
                gconf.gconf_eval_validate
                gconf.gconf_eval_debug
                gconf.gconf_quiet
                input
                expected_output
                schema
                gconf.gconf_dir
                fname
                q
            in
            res_validates_all := !res_validates_all && res_validates;
            let suff =
              Config_util.suffix_of_language (QLang.language_of_query brand_model q)
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
  let res_optim_config =
    if gconf.gconf_emit_optim_config then
      emit_optim_config gconf.gconf_optim_config gconf.gconf_dir file_name
    else
      no_result_file
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
    res_stat_tree = res_stat_tree;
    res_optim_config = res_optim_config;
    res_validates = !res_validates_all }

