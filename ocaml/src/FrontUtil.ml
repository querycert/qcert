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
open QcertUtil
open QcertArg
open ConfigUtil
open ParseFile
open ParseString
open EvalUtil
open Compiler.EnhancedCompiler

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

