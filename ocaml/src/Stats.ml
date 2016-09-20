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
open ConversionUtil
open QcertArg
open ConfigUtil
open ParseFile
open Compiler.EnhancedCompiler

(* ILs Stats *)

let make_stats conf f =
  match language_of_name (get_source_lang_caco conf) with
  | CompDriver.L_rule ->
      let (rn,ru) = parse_rule_from_file f in
      begin
	match ru with
	| CompDriver.Q_rule ru ->
	    CompStat.json_stats_rule (Util.char_list_of_string rn) ru
	| CompDriver.Q_camp ru ->
	    CompStat.json_stats_pattern (Util.char_list_of_string rn) ru
	| _ ->
	    raise (CACo_Error "Input language not supported")
      end
  | CompDriver.L_oql ->
      let o = parse_oql_from_file f in
      CompStat.json_stats_oql (Util.char_list_of_string "[OQL]") o
  | _ ->
      raise (CACo_Error "Input language not supported")

let display_stats conf fname =
  let stats = make_stats (get_comp_lang_config conf) fname in
  let fpref = Filename.chop_extension fname in
  let fout = outname (target_f (get_display_dir conf) fpref) (suffix_stats ()) in
  make_file fout (string_of_char_list stats)

