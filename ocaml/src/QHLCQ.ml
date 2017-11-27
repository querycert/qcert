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

let hlcquery_order_ASC s =
  hlcquery_order_ASC (Util.string_of_char_list s)

let hlcquery_order_DESC s =
  hlcquery_order_DESC (Util.string_of_char_list s)

let hlcquery_condition_expr_const d =
  hlcquery_condition_expr_const d

let hlcquery_condition_expr_param s =
  hlcquery_condition_expr_param (Util.string_of_char_list s)

let hlcquery_condition_expr_var s =
  hlcquery_condition_expr_var (Util.string_of_char_list s)

let hlcquery_condition_expr_unop u e =
  hlcquery_condition_expr_unop u e

let hlcquery_condition_expr_binop b e1 e2 =
  hlcquery_condition_expr_binop b e1 e2

let hlcquery_condition_and c1 c2 =
  hlcquery_condition_and c1 c2

let hlcquery_condition_or c1 c2 =
  hlcquery_condition_or c1 c2

let hlcquery_condition_contains c1 c2 =
  hlcquery_condition_contains c1 c2

let hlcquery_condition_lifted_expr e :
    hlcquery_condition_lifted_expr e

val hlcquery_statement :
    brand -> registry_name option -> hlcquery_condition option ->
      hlcquery_ordering option -> int option -> int option ->
	hlcquery_statement

val hlcquery : char list -> char list -> hlcquery_statement -> hlcquery


