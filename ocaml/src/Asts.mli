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

(********)
(* ASTs *)
(********)

type camp = CompDriver.camp
type algenv = CompDriver.nraenv
type nrc = CompDriver.nnrc
type dnrc_dataset = CompDriver.dnnrc_dataset
type dnrc_typed_dataset = (unit Compiler.type_annotation, Compiler.dataset) Compiler.dnrc
type nrcmr = CompDriver.nnrcmr
type cldmr = CompDriver.cldmr

type sexp_ast = SExp.sexp

type data_ast = Data.data
type io_ast = Data.json
type json_ast = Data.json

type rule_ast = string * Rule.rule

type rORc_ast =
  | RuleAst of Rule.rule
  | CampAst of Compiler.pat
      
type oql_ast = OQL.expr

(* AST <-> S-Expr *)

val sexp_to_data : sexp_ast -> data_ast
val data_to_sexp : data_ast -> sexp_ast

val sexp_to_camp : sexp_ast -> camp
val camp_to_sexp : camp -> sexp_ast

val sexp_to_alg : sexp_ast -> algenv
val alg_to_sexp : algenv -> sexp_ast

val sexp_to_nrc : sexp_ast -> nrc
val nrc_to_sexp : nrc -> sexp_ast

val sexp_to_nrcmr : sexp_ast -> nrcmr
val nrcmr_to_sexp : nrcmr -> sexp_ast

val sexp_to_cldmr : sexp_ast -> cldmr
val cldmr_to_sexp : cldmr -> sexp_ast

