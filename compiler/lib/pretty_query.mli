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

open Compiler.EnhancedCompiler

open Pretty_common

(** Pretty queries *)

type 'a pretty_fun = bool -> int -> bool -> QData.json -> bool -> 'a -> string

val pretty_camp_rule : Compiler.camp_rule pretty_fun
val pretty_tech_rule : Compiler.tech_rule pretty_fun
val pretty_designer_rule : Compiler.designer_rule pretty_fun
val pretty_camp : Compiler.camp pretty_fun
val pretty_oql : Compiler.oql pretty_fun
val pretty_sql : Compiler.sql pretty_fun
val pretty_sqlpp : Compiler.sqlpp pretty_fun
val pretty_lambda_nra : Compiler.lambda_nra pretty_fun
val pretty_nra : Compiler.nra pretty_fun
val pretty_nraenv_core : Compiler.nraenv_core pretty_fun
val pretty_nraenv : Compiler.nraenv pretty_fun
val pretty_nnrc_core : Compiler.nnrc_core pretty_fun
val pretty_nnrc : Compiler.nnrc pretty_fun
val pretty_nnrs : Compiler.nnrs pretty_fun
val pretty_nnrs_core : Compiler.nnrs_core pretty_fun
val pretty_nnrs_imp : Compiler.nnrs_imp pretty_fun
val pretty_imp_qcert : Compiler.imp_qcert pretty_fun
val pretty_imp_ejson : Compiler.imp_ejson pretty_fun
val pretty_nnrcmr : Compiler.nnrcmr pretty_fun
val pretty_dnnrc : Compiler.dnnrc pretty_fun
val pretty_dnnrc_typed : Compiler.dnnrc_typed pretty_fun
val pretty_js_ast : Compiler.js_ast pretty_fun
val pretty_javascript : Compiler.javascript pretty_fun
val pretty_java : Compiler.java pretty_fun
val pretty_spark_df : Compiler.spark_df pretty_fun
val pretty_error : (char list) pretty_fun

val pretty_query : pretty_config -> 'a pretty_fun -> 'a -> string

