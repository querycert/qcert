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
open QcertUtil
open ConfigUtil
open ParseFile
open Compiler.EnhancedCompiler
open QcertArg

(* Frontend Eval *)

let eval_rule h world f : QData.data list option * string =
  let h = List.map (fun (x,y) -> (Util.char_list_of_string x, Util.char_list_of_string y)) h in
  let (rn,ru) = parse_rule_from_file f in
  match ru with
  | Compiler.Q_rule ru ->
      (QEval.rule_eval_top h ru world, Util.string_of_char_list (QEval.rule_eval_top_debug h false ru world))
  | Compiler.Q_camp ru ->
      (QEval.pattern_eval_top h ru world, Util.string_of_char_list (QEval.pattern_eval_top_debug h false ru world))
  | _ ->
      raise (CACo_Error "Input language not supported")

let eval_oql h world f : QData.data option * string =
  let o = parse_oql_from_file f in
  (QEval.oql_eval_top (List.map (fun (x,y) -> (Util.char_list_of_string x, Util.char_list_of_string y)) h) o world, "[OQL Debug]")
  
(* Core Eval *)

exception OQL_eval of string

let eval_nraenv conf schema h world op : QData.data option =
  let h = List.map (fun (x,y) -> (Util.char_list_of_string x, Util.char_list_of_string y)) h in
  match language_of_name (get_target_lang_caev conf) with
  | Compiler.L_rule ->
      raise (CACo_Error "Rule eval not supported once compiled into algebra")
  | Compiler.L_oql ->
      raise (OQL_eval "OQL eval not supported once compiled into algebra")
  | Compiler.L_nraenv ->
      let op = QDriver.nraenv_optim op in
      QEval.algenv_eval_top h op world
  | Compiler.L_nnrc ->
      let nrc = QDriver.nraenv_optim_to_nnrc_optim op in
      QEval.nrc_eval_top h nrc world
  | Compiler.L_dnnrc_dataset ->
      let brand_model =
	begin match schema with
	| Some sc ->
	    begin try
              let sch = TypeUtil.schema_of_io_json (ParseString.parse_io_from_string sc) in
              sch.TypeUtil.sch_brand_model
	    with
	    | _ -> raise (CACo_Error "Spark2 target requires a valid schema I/O file")
	    end
	| None -> raise (CACo_Error "Spark2 target requires a schema I/O file")
	end
      in
      let nrc = QDriver.nraenv_optim_to_nnrc_optim_to_dnnrc Compiler.mkDistLoc op in
      QEval.dnrc_eval_top brand_model h nrc world
  | Compiler.L_nnrcmr ->
      let mrchain = QDriver.nraenv_optim_to_nnrc_optim_to_nnrcmr_comptop_optim op in
      QEval.nrcmr_chain_eval_top h mrchain world
  | Compiler.L_cldmr ->
      let mrchain = QDriver.nraenv_optim_to_nnrc_optim_to_nnrcmr_comptop_optim op in
      let mrchain = QDriver.nnrcmr_to_cldmr [] mrchain in
      QEval.cldmr_chain_eval_top h mrchain world
  | _ ->
      Printf.fprintf stderr "Target not supported in CAEv: %s\n" (get_target_lang_caev conf);
      raise (CACo_Error ("Target not supported in CAEv: " ^ (get_target_lang_caev conf)))

