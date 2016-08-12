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

val sexp_to_data : sexp -> Asts.data_ast
val data_to_sexp : Asts.data_ast -> sexp

val sexp_to_camp : sexp -> CompDriver.camp
val camp_to_sexp : CompDriver.camp -> sexp

val sexp_to_nraenv : sexp -> CompDriver.nraenv
val nraenv_to_sexp : CompDriver.nraenv -> sexp

val sexp_to_nnrc : sexp -> CompDriver.nnrc
val nnrc_to_sexp : CompDriver.nnrc -> sexp

val sexp_to_nnrcmr : sexp -> CompDriver.nnrcmr
val nnrcmr_to_sexp : CompDriver.nnrcmr -> sexp

val sexp_to_cldmr : sexp -> CompDriver.cldmr
val cldmr_to_sexp : CompDriver.cldmr -> sexp

