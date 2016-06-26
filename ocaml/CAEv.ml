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
open ConfigUtil
open ParseUtil
open DataUtil
open FrontUtil
open EvalUtil
open CheckUtil

module Hack = Compiler
open Compiler.EnhancedCompiler


(* Command line args *)
let args conf =
  [ ("-target", Arg.String (change_target (get_eval_lang_config conf)), "(Orig/NRAEnv/NNRC/DNNRC/NNRCMR/CLDMR)");
    ("-source", Arg.String (change_source (get_eval_lang_config conf)), "(Rule/OQL)");
    ("-io", Arg.String (fun f -> set_eval_io conf (ParseFile.parse_io_from_file f)), "Working Memory and hierarchy");
    ("-io-format", Arg.String (set_format conf), "(META/ENHANCED)");
    ("-eval-only", Arg.Set (get_eval_only conf), "Do not perform expected result check");
    ("-debug", Arg.Set (get_debug conf), "Print debug version of evaluation in case of error") ]

let anon_args conf f = set_input conf f

let usage = Sys.argv.(0)^" [-target language] [-source language] [-eval-only] [-debug] -io jsonfile rule1 rule2 ..."

(* Main *)
let rule_main conf io h world f =
  let lconf = get_eval_lang_config conf in
  let (source_result, debug_result) = eval_rule h world f in
  match get_target_lang lconf with
  | ORIG ->
      check_rule_result conf (get_output io) f source_result debug_result
  | _ ->
      let (fname,sname,op) = alg_of_input lconf f in
      let actual_result = eval_alg lconf h world op in
      check_alg_result conf (get_output io) f actual_result debug_result

let oql_main conf io h world f =
  let lconf = get_eval_lang_config conf in
  let (source_result, debug_result) = eval_oql h world f in
  match get_target_lang lconf with
  | ORIG ->
      check_oql_result (get_output io) f source_result debug_result
  | _ ->
      let (fname,sname,op) = alg_of_input lconf f in
      let actual_result = eval_alg lconf h world op in
      check_alg_result conf (get_output io) f actual_result "[OQL]"

let eval_main conf io f =
  if f <> "" then
    let lconf = get_eval_lang_config conf in
    let h = build_hierarchy (get_hierarchy io) in
    let world = get_input conf io in
    begin match get_source_lang lconf with
      | RULE -> rule_main conf io h world f
      | OQL -> oql_main conf io h world f
    end

let () =
  let conf = default_eval_config () in
  begin
    Arg.parse (args conf) (anon_args conf) usage;
    List.iter (eval_main conf (get_eval_io conf)) (get_eval_inputs conf)
  end
