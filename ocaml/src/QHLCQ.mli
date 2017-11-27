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

open QcertCompiler.EnhancedCompiler

val hlcquery_order_ASC : string -> hlcquery_order_col

val hlcquery_order_DESC : string -> hlcquery_order_col

val hlcquery_condition_expr_const : data -> hlcquery_condition_expr

val hlcquery_condition_expr_param : string -> hlcquery_condition_expr

val hlcquery_condition_expr_var : string -> hlcquery_condition_expr

val hlcquery_condition_expr_unop :
    unary_op -> hlcquery_condition_expr -> hlcquery_condition_expr

val hlcquery_condition_expr_binop :
    binary_op -> hlcquery_condition_expr -> hlcquery_condition_expr ->
      hlcquery_condition_expr

val hlcquery_condition_and :
    hlcquery_condition -> hlcquery_condition -> hlcquery_condition

val hlcquery_condition_or :
    hlcquery_condition -> hlcquery_condition -> hlcquery_condition

val hlcquery_condition_contains :
    hlcquery_condition_expr -> hlcquery_condition_expr -> hlcquery_condition

val hlcquery_condition_lifted_expr :
    hlcquery_condition_expr -> hlcquery_condition

val hlcquery_statement :
    brand -> registry_name option -> hlcquery_condition option ->
      hlcquery_ordering option -> int option -> int option ->
	hlcquery_statement

val hlcquery : string -> string -> hlcquery_statement -> hlcquery


