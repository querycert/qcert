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

(** This module contains pretty-printers for all languages *)

open QcertCompiler.EnhancedCompiler

open PrettyCommon

(** Pretty queries *)

type 'a pretty_fun = bool -> int -> bool -> QData.json -> bool -> 'a -> string

val pretty_camp_rule : QcertCompiler.camp_rule pretty_fun
val pretty_tech_rule : QcertCompiler.tech_rule pretty_fun
val pretty_designer_rule : QcertCompiler.designer_rule pretty_fun
val pretty_camp : QcertCompiler.camp pretty_fun
val pretty_oql : QcertCompiler.oql pretty_fun
val pretty_sql : QcertCompiler.sql pretty_fun
val pretty_sqlpp : QcertCompiler.sqlpp pretty_fun
val pretty_lambda_nra : QcertCompiler.lambda_nra pretty_fun
val pretty_nra : QcertCompiler.nra pretty_fun
val pretty_nraenv_core : QcertCompiler.nraenv_core pretty_fun
val pretty_nraenv : QcertCompiler.nraenv pretty_fun
val pretty_nnrc_core : QcertCompiler.nnrc_core pretty_fun
val pretty_nnrc : QcertCompiler.nnrc pretty_fun
val pretty_nnrs : QcertCompiler.nnrs pretty_fun
val pretty_nnrs_core : QcertCompiler.nnrs_core pretty_fun
val pretty_nnrs_imp : QcertCompiler.nnrs_imp pretty_fun
val pretty_imp_qcert : QcertCompiler.imp_qcert pretty_fun
val pretty_imp_json : QcertCompiler.imp_json pretty_fun
val pretty_nnrcmr : QcertCompiler.nnrcmr pretty_fun
val pretty_dnnrc : QcertCompiler.dnnrc pretty_fun
val pretty_dnnrc_typed : QcertCompiler.dnnrc_typed pretty_fun
val pretty_js_ast : QcertCompiler.js_ast pretty_fun
val pretty_javascript : QcertCompiler.javascript pretty_fun
val pretty_java : QcertCompiler.java pretty_fun
val pretty_spark_df : QcertCompiler.spark_df pretty_fun
val pretty_error : (char list) pretty_fun

val pretty_query : pretty_config -> 'a pretty_fun -> 'a -> string

