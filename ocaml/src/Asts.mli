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

type rule = CompDriver.rule
type camp = CompDriver.camp
type nraenv = CompDriver.nraenv
type nnrc = CompDriver.nnrc
type dnnrc_dataset = CompDriver.dnnrc_dataset
type dnnrc_typed_dataset = CompDriver.dnnrc_typed_dataset
type nnrcmr = CompDriver.nnrcmr
type cldmr = CompDriver.cldmr

type data_ast = Data.data
type io_ast = Data.json
type json_ast = Data.json

type rule_ast = string * rule

type rORc_ast =
  | RuleAst of rule
  | CampAst of camp
      
type oql_ast = OQL.expr

