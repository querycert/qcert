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

(** This module contains pretty-printers for all languages *)

open EnhancedCompiler.EnhancedCompiler

open Pretty_common

(** Pretty queries *)

type 'a pretty_fun = bool -> int -> bool -> QData.json -> 'a -> string

val pretty_camp_rule : QLang.camp_rule pretty_fun
val pretty_tech_rule : QLang.tech_rule pretty_fun
val pretty_designer_rule : QLang.designer_rule pretty_fun
val pretty_camp : QLang.camp pretty_fun
val pretty_oql : QLang.oql pretty_fun
val pretty_sql : QLang.sql pretty_fun
val pretty_sqlpp : QLang.sqlpp pretty_fun
val pretty_lambda_nra : QLang.lambda_nra pretty_fun
val pretty_nra : QLang.nra pretty_fun
val pretty_nraenv_core : QLang.nraenv_core pretty_fun
val pretty_nraenv : QLang.nraenv pretty_fun
val pretty_nnrc_core : QLang.nnrc_core pretty_fun
val pretty_nnrc : QLang.nnrc pretty_fun
val pretty_nnrs : QLang.nnrs pretty_fun
val pretty_nnrs_core : QLang.nnrs_core pretty_fun
val pretty_nnrs_imp : QLang.nnrs_imp pretty_fun
val pretty_imp_data : QLang.imp_data pretty_fun
val pretty_imp_ejson : QLang.imp_ejson pretty_fun
val pretty_nnrcmr : QLang.nnrcmr pretty_fun
val pretty_dnnrc : QLang.dnnrc pretty_fun
val pretty_dnnrc_typed : QLang.dnnrc_typed pretty_fun
val pretty_js_ast : QLang.js_ast pretty_fun
val pretty_javascript : QLang.javascript pretty_fun
val pretty_java : QLang.java pretty_fun
val pretty_spark_df : QLang.spark_df pretty_fun
val pretty_wasm_ast : QLang.wasm_ast pretty_fun
val pretty_wasm : QLang.wasm pretty_fun
val pretty_error : string pretty_fun

val pretty_query : pretty_config -> 'a pretty_fun -> 'a -> string

