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

(** Imp with the Q*cert data model *)

Require Import String.
Require Import Utils.
Require Import DataRuntime.
Require Import Imp.

Section ImpData.
  Context {fruntime:foreign_runtime}.
  Section Syntax.

    Definition imp_data_data := data.

    Inductive imp_data_op :=
    | DataOpUnary : unary_op -> imp_data_op
    | DataOpBinary : binary_op -> imp_data_op
    .

    Inductive imp_data_runtime_op :=
    | DataRuntimeGroupby : string -> list string -> imp_data_runtime_op
    | DataRuntimeEither : imp_data_runtime_op
    | DataRuntimeToLeft : imp_data_runtime_op
    | DataRuntimeToRight : imp_data_runtime_op
    .

    Definition imp_data_expr := @imp_expr imp_data_data imp_data_op imp_data_runtime_op.
    Definition imp_data_stmt := @imp_stmt imp_data_data imp_data_op imp_data_runtime_op.
    Definition imp_data_function := @imp_function imp_data_data imp_data_op imp_data_runtime_op.
    Definition imp_data := @imp imp_data_data imp_data_op imp_data_runtime_op.
  End Syntax.

End ImpData.

Tactic Notation "imp_data_runtime_op_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "DataRuntimeGroupby"%string
  | Case_aux c "DataRuntimeEither"%string
  | Case_aux c "DataRuntimeLeft"%string
  | Case_aux c "DataRuntimeRight"%string
  ].
