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

open ConfigUtil
open ParseFile
open Compiler.EnhancedCompiler

(* ILs Stats *)

let make_stats conf f =
  match get_source_lang conf with
  | RULE ->
      let (rn,ru) = parse_rule_from_file f in
      begin
	match ru with
	| Asts.RuleAst ru ->
	    CompStat.json_stats_rule (Util.char_list_of_string rn) ru
	| Asts.CampAst ru ->
	    CompStat.json_stats_pattern (Util.char_list_of_string rn) ru
      end
  | OQL ->
      let o = parse_oql_from_file f in
      CompStat.json_stats_oql (Util.char_list_of_string "[OQL]") o

