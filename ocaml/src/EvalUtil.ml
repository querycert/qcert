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
open ConfigUtil
open ParseFile
open Compiler.EnhancedCompiler

(* Frontend Eval *)

let eval_rule h world f : Data.data list option * string =
  let h = List.map (fun (x,y) -> (Util.char_list_of_string x, Util.char_list_of_string y)) h in
  let (rn,ru) = parse_rule_from_file f in
  match ru with
  | CompDriver.Q_rule ru ->
      (EvalTop.rule_eval_top h ru world, Util.string_of_char_list (EvalTop.rule_eval_top_debug h false ru world))
  | CompDriver.Q_camp ru ->
      (EvalTop.pattern_eval_top h ru world, Util.string_of_char_list (EvalTop.pattern_eval_top_debug h false ru world))
  | _ ->
      raise (CACo_Error "Input language not supported")

let eval_oql h world f : Data.data option * string =
  let o = parse_oql_from_file f in
  (EvalTop.oql_eval_top (List.map (fun (x,y) -> (Util.char_list_of_string x, Util.char_list_of_string y)) h) o world, "[OQL Debug]")
  
(* Core Eval *)

exception OQL_eval of string
      
let eval_nraenv conf h world op : Data.data option =
  let h = List.map (fun (x,y) -> (Util.char_list_of_string x, Util.char_list_of_string y)) h in
  match language_of_name (get_target_lang conf) with
  | CompDriver.L_rule ->
      raise (CACo_Error "Rule eval not supported once compiled into algebra")
  | CompDriver.L_oql ->
      raise (OQL_eval "OQL eval not supported once compiled into algebra")
  | CompDriver.L_nraenv ->
      let op = CompDriver.nraenv_optim op in
      EvalTop.algenv_eval_top h op world
  | CompDriver.L_nnrc ->
      let nrc = CompCore.tcompile_nraenv_to_nnrc_typed_opt op in
      EvalTop.nrc_eval_top h nrc world
  | CompDriver.L_dnnrc_dataset ->
      let nrc = CompCore.tcompile_nraenv_to_dnnrc_typed_opt op in
      EvalTop.dnrc_eval_top h nrc world
  | CompDriver.L_nnrcmr ->
      let mrchain = CompCore.tcompile_nraenv_to_nnrcmr_chain_typed_opt op in
      EvalTop.nrcmr_chain_eval_top h mrchain world
  | CompDriver.L_cldmr ->
      let mrchain = CompCore.tcompile_nraenv_to_nnrcmr_chain_typed_opt op in
      let mrchain = CompDriver.nnrcmr_to_cldmr [] mrchain in
      EvalTop.cldmr_chain_eval_top h mrchain world
  | _ ->
      Printf.fprintf stderr "Target not supported in CAEv: %s\n" (get_target_lang conf);
      raise (CACo_Error ("Target not supported in CAEv: " ^ (get_target_lang conf)))

