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

open Core.EnhancedCompiler

open Pretty_common

(** Pretty queries *)

type 'a pretty_fun = bool -> int -> bool -> QData.json -> bool -> 'a -> string

val pretty_camp_rule : Core.camp_rule pretty_fun
val pretty_tech_rule : Core.tech_rule pretty_fun
val pretty_designer_rule : Core.designer_rule pretty_fun
val pretty_camp : Core.camp pretty_fun
val pretty_oql : Core.oql pretty_fun
val pretty_sql : Core.sql pretty_fun
val pretty_sqlpp : Core.sqlpp pretty_fun
val pretty_lambda_nra : Core.lambda_nra pretty_fun
val pretty_nra : Core.nra pretty_fun
val pretty_nraenv_core : Core.nraenv_core pretty_fun
val pretty_nraenv : Core.nraenv pretty_fun
val pretty_nnrc_core : Core.nnrc_core pretty_fun
val pretty_nnrc : Core.nnrc pretty_fun
val pretty_nnrs : Core.nnrs pretty_fun
val pretty_nnrs_core : Core.nnrs_core pretty_fun
val pretty_nnrs_imp : Core.nnrs_imp pretty_fun
val pretty_imp_data : Core.imp_data pretty_fun
val pretty_imp_ejson : Core.imp_ejson pretty_fun
val pretty_nnrcmr : Core.nnrcmr pretty_fun
val pretty_dnnrc : Core.dnnrc pretty_fun
val pretty_dnnrc_typed : Core.dnnrc_typed pretty_fun
val pretty_js_ast : Core.js_ast pretty_fun
val pretty_javascript : Core.javascript pretty_fun
val pretty_java : Core.java pretty_fun
val pretty_spark_df : Core.spark_df pretty_fun
val pretty_error : (char list) pretty_fun

val pretty_query : pretty_config -> 'a pretty_fun -> 'a -> string

