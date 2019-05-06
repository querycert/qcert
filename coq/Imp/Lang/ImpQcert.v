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
Require Import Utils.
Require Import CommonRuntime.
Require Import Imp.

Section Syntax.

  Context {fruntime:foreign_runtime}.

  Definition imp_qcert_data := data.

  Inductive imp_qcert_op :=
  | QcertOpUnary : unary_op -> imp_qcert_op
  | QcertOpBinary : binary_op -> imp_qcert_op
  .

  Inductive imp_qcert_runtime_op :=
  | QcertRuntimeGroupby : string -> list string -> imp_qcert_runtime_op
  | QcertRuntimeEither : imp_qcert_runtime_op
  | QcertRuntimeToLeft : imp_qcert_runtime_op
  | QcertRuntimeToRight : imp_qcert_runtime_op
  | QcertRuntimeDeref : imp_qcert_runtime_op
  .

  Definition imp_qcert_expr := @imp_expr imp_qcert_data imp_qcert_op imp_qcert_runtime_op.
  Definition imp_qcert_stmt := @imp_stmt imp_qcert_data imp_qcert_op imp_qcert_runtime_op.
  Definition imp_qcert_function := @imp_function imp_qcert_data imp_qcert_op imp_qcert_runtime_op.
  Definition imp_qcert := @imp imp_qcert_data imp_qcert_op imp_qcert_runtime_op.
End Syntax.

Section Env.
  Context {fruntime:foreign_runtime}.

  (* bindings that may or may not be initialized (defined) *)
  Definition pd_bindings := list (string*option data).

End Env.
