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

Require Import String.
Require Import EJsonRuntime.
Require Import Imp.
Require Import ImpEJson.
Require Import ImpVars.

Section ImpEJsonVars.
  Context {foreign_ejson_model:Set}.
  Context {fejson:foreign_ejson foreign_ejson_model}.
  Context {foreign_ejson_runtime_op : Set}.
  Context {fejruntime:foreign_ejson_runtime foreign_ejson_runtime_op}.

  Definition imp_ejson_expr_free_vars (e:@imp_ejson_expr foreign_ejson_model foreign_ejson_runtime_op) : list var :=
    imp_expr_free_vars e.

  Definition imp_ejson_stmt_free_vars (stmt:@imp_ejson_stmt foreign_ejson_model foreign_ejson_runtime_op) : list var :=
    imp_stmt_free_vars stmt.

  Definition imp_ejson_stmt_bound_vars (stmt:@imp_ejson_stmt foreign_ejson_model foreign_ejson_runtime_op) : list var :=
    imp_stmt_bound_vars stmt.


End ImpEJsonVars.
