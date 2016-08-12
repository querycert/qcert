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

(* Front end utilities *)

open Util
open ConfigUtil
open ParseFile
open ParseString
open EvalUtil
open Compiler.EnhancedCompiler

(* Parse/translate input *)

let camp_of_rule_string s =
  let (rn,ru) = parse_rule_from_string s in
  match ru with
  | CompDriver.Q_rule ru ->
      (rn,CompFront.translate_rule_to_pat ru)
  | CompDriver.Q_camp ru ->
      (rn,ru)
  | _ ->
      raise (CACo_Error "Input language not supported")

let nraenv_of_camp p =
  CompFront.translate_pat_to_algenv p

let nraenv_of_rule_string s =
  let (rn,ru) = parse_rule_from_string s in
  match ru with
  | CompDriver.Q_rule ru ->
      (rn,CompFront.translate_rule_to_algenv ru)
  | CompDriver.Q_camp ru ->
      (rn,CompFront.translate_pat_to_algenv ru)
  | _ ->
      raise (CACo_Error "Input language not supported")

let nraenv_of_rule f =
  let (rn,ru) = parse_rule_from_file f in
  match ru with
  | CompDriver.Q_rule ru ->
      (rn,CompFront.translate_rule_to_algenv ru)
  | CompDriver.Q_camp ru ->
      (rn,CompFront.translate_pat_to_algenv ru)
  | _ ->
      raise (CACo_Error "Input language not supported")

let nraenv_of_oql_string s =
  let o = parse_oql_from_string s in
  ("OQL",CompFront.translate_oql_to_algenv o)
  
let nraenv_of_oql f =
  let o = parse_oql_from_file f in
  ("OQL",CompFront.translate_oql_to_algenv o)
  
let nraenv_of_input conf f =
  match get_source_lang conf with
  | RULE ->
      nraenv_of_rule f
  | OQL ->
      nraenv_of_oql f

