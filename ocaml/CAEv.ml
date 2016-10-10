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

(* This is main for the Camp Evaluator *)

open Format
open Util
open QcertUtil
open QcertArg
open ConfigUtil
open ParseUtil
open ParseFile
open DataUtil
open EvalUtil
open CheckUtil

module Hack = Compiler
open Compiler.EnhancedCompiler


(* Command line args *)
let args conf =
  [ ("-target", Arg.String (change_target (get_eval_lang_config conf)), "(Orig/NRAEnv/NNRC/DNNRC/NNRCMR/CLDMR)");
    ("-source", Arg.String (change_source (get_eval_lang_config conf)), "(Rule/OQL)");
    ("-io", Arg.String (fun f -> set_eval_schema conf (Util.string_of_file f); set_eval_io conf (ParseFile.parse_io_from_file f)), "Working Memory and hierarchy");
    ("-io-format", Arg.String (set_format conf), "(META/ENHANCED)");
    ("-eval-only", Arg.Set (get_eval_only conf), "Do not perform expected result check");
    ("-debug", Arg.Set (get_debug conf), "Print debug version of evaluation in case of error") ]

let anon_args conf f = set_input conf f

let usage = Sys.argv.(0)^" [-target language] [-source language] [-eval-only] [-debug] -io jsonfile rule1 rule2 ..."

(* Some utility *)

(* Parse/translate input *)

let nraenv_of_rule f =
  let (rn,ru) = parse_rule_from_file f in
  match ru with
  | Compiler.Q_rule ru ->
      (rn,QDriver.rule_to_nraenv ru)
  | Compiler.Q_camp ru ->
      (rn,QDriver.camp_to_nraenv ru)
  | _ ->
      raise (Qcert_Error "Input language not supported")

let nraenv_of_oql f =
  let o = parse_oql_from_file f in
  ("OQL",QDriver.oql_to_nraenv o)
  
let nraenv_of_input conf f =
  match language_of_name (get_source_lang_caco conf) with
  | Compiler.L_rule ->
      nraenv_of_rule f
  | Compiler.L_oql ->
      nraenv_of_oql f
  | _ ->
      raise (Qcert_Error "Input language not supported")

(* Main *)
let rule_main conf io schema h world f =
  let lconf = get_eval_lang_config conf in
  let (source_result, debug_result) = eval_rule h world f in
  match language_of_name (get_target_lang_caev lconf) with
  | Compiler.L_rule ->
      check_rule_result conf (get_output io) f source_result debug_result
  | _ ->
      let (sname,op) = nraenv_of_input lconf f in
      let actual_result = eval_nraenv lconf schema h world op in
      check_nraenv_result conf (get_output io) f actual_result debug_result

let oql_main conf io schema h world f =
  let lconf = get_eval_lang_config conf in
  let (source_result, debug_result) = eval_oql h world f in
  match language_of_name (get_target_lang_caev lconf) with
  | Compiler.L_rule | Compiler.L_oql -> (* XXX TODO : Fix the default target for OQL XXX *)
      check_oql_result (get_output io) f source_result debug_result
  | _ ->
      let (sname,op) = nraenv_of_input lconf f in
      let actual_result = eval_nraenv lconf schema h world op in
      check_nraenv_result conf (get_output io) f actual_result "[OQL]"

let eval_main conf schema io f =
  if f <> "" then
    let lconf = get_eval_lang_config conf in
    let h = build_hierarchy (get_hierarchy io) in
    let world = get_input (get_format conf) io in
    begin
      match language_of_name (get_source_lang_caev lconf) with
      | Compiler.L_rule -> rule_main conf io schema h world f
      | Compiler.L_oql -> oql_main conf io schema h world f
      | _ ->
	  raise (Qcert_Error "Source language not supported")
    end

let () =
  let conf = default_eval_config () in
  begin
    Arg.parse (args conf) (anon_args conf) usage;
    List.iter (eval_main conf (get_eval_schema conf) (get_eval_io conf)) (get_eval_inputs conf)
  end
