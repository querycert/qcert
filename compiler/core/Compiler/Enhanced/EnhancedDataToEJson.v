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

Require Import List.
Require Import ZArith.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Equivalence.
Require Import String.
Require Import Utils.
Require Import EJsonSystem.
Require Import DataSystem.
Require Import ForeignDataToEJson.
Require Import ForeignToEJsonRuntime.

Require Import SqlDateComponent.
Require Import UriComponent.

Require Import EnhancedData.
Require Import EnhancedEJson.

Import ListNotations.
Local Open Scope list_scope.

Global Program Instance enhanced_foreign_to_ejson : foreign_to_ejson _ _ :=
  mk_foreign_to_ejson enhanced_ejson enhanced_foreign_ejson_runtime_op enhanced_foreign_ejson enhanced_foreign_runtime _ _ _ _.
Next Obligation.
  exact j. (* XXX enhanced_ejson is the same as enhanced_data *)
Defined.
Next Obligation.
  exact fd. (* XXX enhanced_ejson is the same as enhanced_data *)
Defined.

Definition unary_op_to_ejson (op:enhanced_unary_op) : enhanced_foreign_ejson_runtime_op :=
  match op with
  | enhanced_unary_sql_date_op dop =>
    match dop with
    | uop_sql_date_get_component sql_date_YEAR => enhanced_ejson_sql_date EJsonRuntimeDateGetYear
    | uop_sql_date_get_component sql_date_MONTH => enhanced_ejson_sql_date EJsonRuntimeDateGetMonth
    | uop_sql_date_get_component sql_date_DAY => enhanced_ejson_sql_date EJsonRuntimeDateGetDay
    | uop_sql_date_from_string => enhanced_ejson_sql_date EJsonRuntimeDateFromString
    | uop_sql_date_period_from_string => enhanced_ejson_sql_date EJsonRuntimePeriodFromString
    end
  | enhanced_unary_uri_op uop =>
    match uop with
    | uop_uri_encode => enhanced_ejson_uri EJsonRuntimeUriEncode
    | uop_uri_decode => enhanced_ejson_uri EJsonRuntimeUriDecode
    end
  end.

Lemma unary_op_to_ejson_correct (uop:enhanced_unary_op) :
  forall br d,
    lift DataToEJson.data_to_ejson (enhanced_unary_op_interp br uop d) =
    enhanced_foreign_ejson_runtime_op_interp (unary_op_to_ejson uop)
                                             [DataToEJson.data_to_ejson d].
Proof.
  intros.
  destruct uop.
  - destruct s; simpl; try (destruct d; simpl; try reflexivity);
      try (destruct s; simpl; try reflexivity;
           destruct d; try reflexivity; simpl;
           destruct f; reflexivity;
           destruct s; simpl; try reflexivity);
      destruct s; destruct f; simpl; try reflexivity.
  - destruct d; destruct u; simpl; try reflexivity.
Qed.

Definition binary_op_to_ejson (op:enhanced_binary_op) : enhanced_foreign_ejson_runtime_op :=
  match op with
  | enhanced_binary_sql_date_op dop =>
    match dop with
    | bop_sql_date_plus => enhanced_ejson_sql_date EJsonRuntimePeriodPlus
    | bop_sql_date_minus => enhanced_ejson_sql_date EJsonRuntimePeriodMinus
    | bop_sql_date_ne => enhanced_ejson_sql_date EJsonRuntimeDateNe
    | bop_sql_date_lt => enhanced_ejson_sql_date EJsonRuntimeDateLt
    | bop_sql_date_le => enhanced_ejson_sql_date EJsonRuntimeDateLe
    | bop_sql_date_gt => enhanced_ejson_sql_date EJsonRuntimeDateGt
    | bop_sql_date_ge => enhanced_ejson_sql_date EJsonRuntimeDateGe
    | bop_sql_date_period_between => enhanced_ejson_sql_date EJsonRuntimePeriodBetween
    | bop_sql_date_set_component sql_date_YEAR => enhanced_ejson_sql_date EJsonRuntimeDateSetYear
    | bop_sql_date_set_component sql_date_MONTH => enhanced_ejson_sql_date EJsonRuntimeDateSetMonth
    | bop_sql_date_set_component sql_date_DAY => enhanced_ejson_sql_date EJsonRuntimeDateSetDay
    end
  end.

Lemma binary_op_to_ejson_correct (bop:enhanced_binary_op) :
  forall br d1 d2,
    lift DataToEJson.data_to_ejson (enhanced_binary_op_interp br bop d1 d2) =
    enhanced_foreign_ejson_runtime_op_interp (binary_op_to_ejson bop)
                                             [DataToEJson.data_to_ejson d1;DataToEJson.data_to_ejson d2].
Proof.
  intros.
  destruct bop.
  destruct s; simpl;
    try (destruct d1; destruct d2; try reflexivity;
         destruct f; simpl; try reflexivity;
         destruct f0; try reflexivity).
  - destruct s; simpl;
      destruct d1; destruct d2; try reflexivity;
        destruct f; simpl; try reflexivity;
          destruct f0; try reflexivity.
Qed.

Lemma enhanced_foreign_data_to_string_correct:
  forall fd : foreign_data_model,
    toString fd = toString (foreign_to_ejson_from_data fd).
Proof.
  reflexivity.
Qed.

Global Program Instance enhanced_foreign_to_ejson_runtime : foreign_to_ejson_runtime :=
  mk_foreign_to_ejson_runtime
    enhanced_ejson
    enhanced_foreign_ejson_runtime_op
    enhanced_foreign_ejson
    enhanced_foreign_runtime
    enhanced_foreign_to_ejson
    enhanced_foreign_ejson_runtime
    _ _ _ _ _ _.
Next Obligation.
  exact (unary_op_to_ejson uop).
Defined.
Next Obligation.
  apply unary_op_to_ejson_correct.
Defined.
Next Obligation.
  exact (binary_op_to_ejson bop).
Defined.
Next Obligation.
  apply binary_op_to_ejson_correct.
Defined.
Next Obligation.
  specialize (default_to_ejson_tostring_correct enhanced_foreign_data_to_string_correct); intros.
  rewrite H.
  reflexivity.
Qed.
Next Obligation.
  specialize (default_to_ejson_tostring_correct enhanced_foreign_data_to_string_correct); intros.
  rewrite H.
  reflexivity.
Qed.
