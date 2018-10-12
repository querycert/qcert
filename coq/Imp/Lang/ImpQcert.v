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

(** Imp with the Q*cert data model *)

Require Import String.

Require Import Imp.
Require Import Data.
Require Import Operators.
Require Import CommonRuntime.

Section Syntax.

  Context {fruntime:foreign_runtime}.

  Inductive runtime_op :=
  | RuntimeGroupby : string -> list string -> runtime_op
  | RuntimeEither : runtime_op
  | RuntimeToLeft : runtime_op
  | RuntimeToRight : runtime_op
  .

  Inductive op :=
  | Unary : unary_op -> op
  | Binary : binary_op -> op
  .

  Definition imp_qcert_expr := @imp_expr data op runtime_op.
  Definition imp_qcert_stmt := @imp_expr data op runtime_op.

End Syntax.
