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
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import DataRuntime.
Require Import Imp.

Section ImpData.
  Context {fruntime:foreign_runtime}.
  Section Syntax.

    Definition imp_data_model := data.
    Definition imp_data_constant := data.

    Inductive imp_data_op :=
    | DataOpUnary : unary_op -> imp_data_op
    | DataOpBinary : binary_op -> imp_data_op
    .

    Inductive imp_data_runtime_op :=
    | DataRuntimeGroupby : string -> list string -> imp_data_runtime_op
    | DataRuntimeEither : imp_data_runtime_op
    | DataRuntimeToLeft : imp_data_runtime_op
    | DataRuntimeToRight : imp_data_runtime_op
    | DataRuntimePush
    .

    Definition imp_data_expr := @imp_expr imp_data_constant imp_data_op imp_data_runtime_op.
    Definition imp_data_stmt := @imp_stmt imp_data_constant imp_data_op imp_data_runtime_op.
    Definition imp_data_function := @imp_function imp_data_constant imp_data_op imp_data_runtime_op.
    Definition imp_data := @imp imp_data_constant imp_data_op imp_data_runtime_op.
  End Syntax.

  Section dec.
    Global Instance imp_data_constant_eqdec : EqDec imp_data_constant eq.
    Proof.
      apply data_eqdec.
    Qed.

    Global Instance imp_data_op_eqdec : EqDec imp_data_op eq.
    Proof.
      change (forall x y : imp_data_op,  {x = y} + {x <> y}).
      decide equality.
      apply unary_op_eqdec.
      apply binary_op_eqdec.
    Qed.

    Global Instance imp_data_runtime_op_eqdec : EqDec imp_data_runtime_op eq.
    Proof.
      change (forall x y : imp_data_runtime_op,  {x = y} + {x <> y}).
      decide equality.
      - clear a.
        revert l0; induction l; intros; destruct l0; simpl in *; try solve[right; inversion 1].
        left; reflexivity.
        elim (IHl l0); intros; clear IHl.
        + subst; destruct (string_dec a s1); subst; [left; reflexivity| right; congruence].
        + right; congruence.
      - apply string_eqdec.
    Qed.

    Global Instance imp_data_expr_eqdec : EqDec imp_data_expr eq.
    Proof.
      apply (@imp_expr_eqdec imp_data_constant imp_data_op imp_data_runtime_op).
      apply imp_data_constant_eqdec.
      apply imp_data_op_eqdec.
      apply imp_data_runtime_op_eqdec.
    Qed.
  End dec.
End ImpData.

Tactic Notation "imp_data_runtime_op_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "DataRuntimeGroupby"%string
  | Case_aux c "DataRuntimeEither"%string
  | Case_aux c "DataRuntimeLeft"%string
  | Case_aux c "DataRuntimeRight"%string
  | Case_aux c "DataRuntimePush"%string
  ].
