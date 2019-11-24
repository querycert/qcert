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

Require Import String.
Require Import Omega.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import CommonRuntime.
Require Import Imp.
Require Import ImpJson.
Require Import ImpSize.

Section ImpJsonSize.

  Context {fruntime:foreign_runtime}.

  Definition imp_json_expr_size (e:imp_json_expr) : nat :=
    imp_expr_size e.

  Definition imp_json_stmt_size (stmt:imp_json_stmt) : nat :=
    imp_stmt_size stmt.

  Definition imp_json_function_size (q:imp_json_function) : nat :=
    imp_function_size q.

  Fixpoint imp_json_size (q: imp_json) : nat :=
    imp_size q.

End ImpJsonSize.
