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

(** Imp with the Json data model *)

Require Import Imp.

Require Import JSON.
Require Import CommonRuntime.

Section Syntax.

  Context {fruntime:foreign_runtime}.

  Definition imp_json_data := data.

  Inductive imp_json_op := (* XXX TODO XXX *)
  | OpPlus
  .

  Inductive imp_json_runtime_op := (* XXX TODO XXX *)
  | RuntimePlus
  .

  Definition imp_json_expr := @imp_expr imp_json_data imp_json_op.
  Definition imp_json_stmt := @imp_expr imp_json_data imp_json_op.
  Definition imp_json_function := @imp_function imp_json_data imp_json_op imp_json_runtime_op.
  Definition imp_json := @imp imp_json_data imp_json_op imp_json_runtime_op.

End Syntax.
