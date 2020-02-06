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
Require Import DataRuntime.
Require Import Imp.
Require Import ImpData.
Require Import ImpVars.

Section ImpDataVars.

  Context {fruntime:foreign_runtime}.

  Definition imp_data_expr_free_vars (e:imp_data_expr) : list var :=
    imp_expr_free_vars e.

  Definition imp_data_stmt_free_vars (stmt:imp_data_stmt) : list var :=
    imp_stmt_free_vars stmt.

  Definition imp_data_stmt_bound_vars (stmt:imp_data_stmt) : list var :=
    imp_stmt_bound_vars stmt.


End ImpDataVars.
