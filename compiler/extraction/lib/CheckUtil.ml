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

(* Result checking *)

open QcertExtracted

open Format

open ConfigUtil

open QcertCompiler.EnhancedCompiler

(* Check result *)

let print_nraenv_result fname actual_res =
  match actual_res with
  | None -> Format.printf "Evaluation for file %s : [Type Error]@." fname
  | Some res ->
      let res_string = PrettyCommon.pretty_data str_formatter res; flush_str_formatter () in
      Format.printf "Evaluation for file %s : %s@." fname res_string

let print_error_opt_data d =
  begin match d with
  | None ->
      Format.eprintf "[NOTHING]@."
  | Some d ->
      Format.eprintf "%a@." PrettyCommon.pretty_data d
  end

let validate_result quiet queryname targetname expected_res actual_res =
  let ok = QUtil.validate_data actual_res (Some expected_res) in
  if ok then
    begin
      if not quiet then Format.printf "[%s %s] OK@." queryname targetname;
      true
    end
  else
    begin
      if not quiet then
        begin
          Format.eprintf "[%s %s] ERROR@." queryname targetname;
          Format.eprintf "Expected:@.";
          print_error_opt_data (Some expected_res);
          Format.eprintf "Actual:@.";
          print_error_opt_data actual_res;
        end;
      false
    end
	
let validate_result_debug conf expected_res actual_res debug_res =
  let ok = QUtil.validate_lifted_success actual_res expected_res in
  if ok then
    Format.printf "OK@."
  else
    begin
      if !(get_debug conf) then Format.printf "CAMP evaluation: %s@." debug_res else ();
      Format.printf "ERROR@."
    end
	
let check_nraenv_result conf expected_res fname actual_res debug_res =
  if !(get_eval_only conf) then
    print_nraenv_result fname actual_res
  else
    validate_result_debug conf expected_res actual_res debug_res

let print_rule_result fname (actual_res : QData.qdata option) =
  match actual_res with
  | None -> Format.printf "Evaluation for file %s : [Type Error]@." fname
  | Some res ->
      let res_string = PrettyCommon.pretty_data Format.str_formatter res; Format.flush_str_formatter () in
      Format.printf "Evaluation for file %s : %s@." fname res_string

let print_oql_result = print_nraenv_result

let check_rule_result conf expected_res fname actual_res debug_res =
  if !(get_eval_only conf) then
    print_rule_result fname actual_res
  else
    validate_result_debug conf expected_res actual_res debug_res

let check_oql_result output fname actual_res debug_result =
  print_oql_result fname actual_res

