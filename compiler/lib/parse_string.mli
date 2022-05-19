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

(* This module contains parsing utilities *)

open EnhancedCompiler.EnhancedCompiler

(*********************)
(* Parse from string *)
(*********************)

val parse_io_from_string : string -> QData.json
val parse_json_from_string : string -> QData.json

val parse_rule_from_string : string -> string * QLang.camp_rule
val parse_camp_from_string : string -> string * QLang.camp

val parse_oql_from_string : string -> QLang.oql

(****************)
(* S-Expr Parse *)
(****************)

val parse_sexp_from_string : string -> Sexp.sexp
val parse_io_sexp_from_string : string -> QData.qdata
val parse_camp_sexp_from_string : string -> QLang.camp
val parse_nraenv_sexp_from_string : string -> QLang.nraenv_core
val parse_nnrc_sexp_from_string : string -> QLang.nnrc
val parse_nnrs_sexp_from_string : string -> QLang.nnrs
val parse_nnrcmr_sexp_from_string : string -> QLang.nnrcmr

(*******************
 * Languages Parse *
 *******************)

val parse_query_from_string : QLang.language -> string -> string * QLang.query
