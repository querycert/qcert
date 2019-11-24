(*
 * Copyright 2015-2017 IBM Corporation
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

(* This module contains parsing utilities *)

open SExp

open QcertCompiler.EnhancedCompiler

(******************
 * AST <-> S-Expr *
 ******************)

val sexp_to_data : sexp -> QData.qdata
val data_to_sexp : QData.qdata -> sexp

val sexp_to_camp_rule : sexp -> QLang.camp_rule
val camp_rule_to_sexp : QLang.camp_rule -> sexp

val sexp_to_camp : sexp -> QLang.camp
val camp_to_sexp : QLang.camp -> sexp

val sexp_to_nraenv : sexp -> QLang.nraenv_core
val nraenv_to_sexp : QLang.nraenv_core -> sexp

val sexp_to_sql : sexp -> QLang.sql
(* val sql_to_sexp : QLang.sql -> sexp *)

val sexp_to_sqlpp : sexp -> QLang.sqlpp
(* val sqlpp_to_sexp : QLang.sqlpp -> sexp *)

val sexp_to_nnrc : sexp -> QLang.nnrc
val nnrc_to_sexp : QLang.nnrc -> sexp

val sexp_to_nnrs : sexp -> QLang.nnrs
val nnrs_to_sexp : QLang.nnrs -> sexp

val sexp_to_nnrs_imp : sexp -> QLang.nnrs_imp
val nnrs_imp_expr_to_sexp : QLang.nnrs_imp_expr -> sexp
val nnrs_imp_stmt_to_sexp : QLang.nnrs_imp_stmt -> sexp
val nnrs_imp_to_sexp : QLang.nnrs_imp -> sexp


val sexp_to_imp_qcert : sexp -> QLang.imp_qcert
val imp_qcert_to_sexp : QLang.imp_qcert -> sexp

val sexp_to_imp_json : sexp -> QLang.imp_json
val imp_json_to_sexp : QLang.imp_json -> sexp


val sexp_to_nnrcmr : sexp -> QLang.nnrcmr
val nnrcmr_to_sexp : QLang.nnrcmr -> sexp

val sexp_to_query : QLang.language -> sexp -> QLang.query
val query_to_sexp : QLang.query -> sexp
