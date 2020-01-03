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
Require Import Omega.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import EJsonRuntime.
Require Import Imp.
Require Import ImpSize.
Require Import ImpEJson.

Section ImpEJsonSize.

  Context {ftoejson:foreign_ejson}.
  Context {fejruntime:foreign_ejson_runtime}.

  Definition imp_ejson_expr_size (e:imp_ejson_expr) : nat :=
    imp_expr_size e.

  Definition imp_ejson_stmt_size (stmt:imp_ejson_stmt) : nat :=
    imp_stmt_size stmt.

  Definition imp_ejson_function_size (q:imp_ejson_function) : nat :=
    imp_function_size q.

  Fixpoint imp_ejson_size (q: imp_ejson) : nat :=
    imp_size q.

End ImpEJsonSize.
