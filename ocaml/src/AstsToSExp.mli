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

(* This module contains parsing utilities *)

open Compiler.EnhancedCompiler
open SExp


(******************
 * AST <-> S-Expr *
 ******************)

val sexp_to_data : sexp -> QData.data
val data_to_sexp : QData.data -> sexp

val sexp_to_camp_rule : sexp -> QLang.camp_rule
val camp_rule_to_sexp : QLang.camp_rule -> sexp

val sexp_to_camp : sexp -> QLang.camp
val camp_to_sexp : QLang.camp -> sexp

val sexp_to_nraenv : sexp -> QLang.nraenv_core
val nraenv_to_sexp : QLang.nraenv_core -> sexp

val sexp_to_sql : sexp -> QLang.sql
(* val sql_to_sexp : QLang.sql -> sexp *)

val sexp_to_nnrc : sexp -> QLang.nnrc
val nnrc_to_sexp : QLang.nnrc -> sexp

val sexp_to_nnrcmr : sexp -> QLang.nnrcmr
val nnrcmr_to_sexp : QLang.nnrcmr -> sexp

val sexp_to_cldmr : sexp -> QLang.cldmr
val cldmr_to_sexp : QLang.cldmr -> sexp

val sexp_to_query : QLang.language -> sexp -> QLang.query
val query_to_sexp : QLang.query -> sexp
