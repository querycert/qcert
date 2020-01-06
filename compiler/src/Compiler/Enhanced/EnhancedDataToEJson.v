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
Require Import ToString.
Require Import String.
Require Import Utils.
Require Import EJsonSystem.
Require Import DataSystem.
Require Import ForeignEJson.
Require Import ForeignDataToEJson.
Require Import ForeignToEJsonRuntime.

Require Import SqlDateComponent.

Require Import EnhancedData.
Require Import EnhancedEJson.

Import ListNotations.
Local Open Scope list_scope.

Program Instance enhanced_foreign_to_ejson : foreign_to_ejson
  := mk_foreign_to_ejson enhanced_foreign_runtime enhanced_foreign_ejson _ _ _ _.
Next Obligation.
  exact j. (* XXX enhanced_ejson is the same as enhanced_data *)
Defined.
Next Obligation.
  exact fd. (* XXX enhanced_ejson is the same as enhanced_data *)
Defined.

Definition sql_date_unary_op_to_ejson (op:enhanced_unary_op) : enhanced_foreign_ejson_runtime_op
  := match op with
     | enhanced_unary_sql_date_op dop =>
       match dop with
       | uop_sql_date_get_component sql_date_YEAR => enhanced_EJsonRuntimeDateGetYear
       | uop_sql_date_get_component sql_date_MONTH => enhanced_EJsonRuntimeDateGetMonth
       | uop_sql_date_get_component sql_date_DAY => enhanced_EJsonRuntimeDateGetDay
       | uop_sql_date_from_string => enhanced_EJsonRuntimeDateFromString
       | uop_sql_date_interval_from_string => enhanced_EJsonRuntimeDurationFromString
       end
     end.

Lemma sql_date_unary_op_to_ejson_correct (uop:enhanced_unary_op) :
  forall br d,
    lift DataToEJson.data_to_ejson (enhanced_unary_op_interp br uop d) =
    enhanced_foreign_ejson_runtime_op_interp (sql_date_unary_op_to_ejson uop)
                                             [DataToEJson.data_to_ejson d].
Proof.
  intros.
  destruct uop.
  destruct s; simpl.
  - destruct s; simpl; try reflexivity;
      destruct d; try reflexivity; simpl;
        destruct f; reflexivity.
  - destruct d; simpl; try reflexivity.
  - destruct d; simpl; try reflexivity.
Qed.

Definition sql_date_binary_op_to_ejson (op:enhanced_binary_op) : enhanced_foreign_ejson_runtime_op
  := match op with
     | enhanced_binary_sql_date_op dop =>
       match dop with
       | bop_sql_date_plus => enhanced_EJsonRuntimeDurationPlus
       | bop_sql_date_minus => enhanced_EJsonRuntimeDurationMinus
       | bop_sql_date_ne => enhanced_EJsonRuntimeDateNe
       | bop_sql_date_lt => enhanced_EJsonRuntimeDateLt
       | bop_sql_date_le => enhanced_EJsonRuntimeDateLe
       | bop_sql_date_gt => enhanced_EJsonRuntimeDateGt
       | bop_sql_date_ge => enhanced_EJsonRuntimeDateGe
       | bop_sql_date_interval_between =>enhanced_EJsonRuntimeDurationBetween
       | bop_sql_date_set_component sql_date_YEAR => enhanced_EJsonRuntimeDateSetYear
       | bop_sql_date_set_component sql_date_MONTH => enhanced_EJsonRuntimeDateSetMonth
       | bop_sql_date_set_component sql_date_DAY => enhanced_EJsonRuntimeDateSetDay
       end
     end.

Lemma sql_date_binary_op_to_ejson_correct (bop:enhanced_binary_op) :
  forall br d1 d2,
    lift DataToEJson.data_to_ejson (enhanced_binary_op_interp br bop d1 d2) =
    enhanced_foreign_ejson_runtime_op_interp (sql_date_binary_op_to_ejson bop)
                                             [DataToEJson.data_to_ejson d1;DataToEJson.data_to_ejson d2].
Proof.
  intros.
  destruct bop.
  destruct s; simpl.
  - destruct d1; destruct d2; try reflexivity;
      destruct f; simpl; try reflexivity;
        destruct f0; try reflexivity.
  - destruct d1; destruct d2; try reflexivity;
      destruct f; simpl; try reflexivity;
        destruct f0; try reflexivity.
  - unfold rondboolsqldate2, lift, ondsqldate2; simpl.
    destruct d1; destruct d2; try reflexivity;
      destruct f; simpl; try reflexivity;
        destruct f0; try reflexivity.
  - unfold rondboolsqldate2, lift, ondsqldate2; simpl.
    destruct d1; destruct d2; try reflexivity;
      destruct f; simpl; try reflexivity;
        destruct f0; try reflexivity.
  - unfold rondboolsqldate2, lift, ondsqldate2; simpl.
    destruct d1; destruct d2; try reflexivity;
      destruct f; simpl; try reflexivity;
        destruct f0; try reflexivity.
  - unfold rondboolsqldate2, lift, ondsqldate2; simpl.
    destruct d1; destruct d2; try reflexivity;
      destruct f; simpl; try reflexivity;
        destruct f0; try reflexivity.
  - unfold rondboolsqldate2, lift, ondsqldate2; simpl.
    destruct d1; destruct d2; try reflexivity;
      destruct f; simpl; try reflexivity;
        destruct f0; try reflexivity.
  - destruct d1; destruct d2; try reflexivity;
      destruct f; simpl; try reflexivity;
        destruct f0; try reflexivity.
  - destruct s; simpl;
      destruct d1; destruct d2; try reflexivity;
        destruct f; simpl; try reflexivity;
          destruct f0; try reflexivity.
Qed.

Program Instance enhanced_foreign_to_ejson_runtime :
  foreign_to_ejson_runtime :=
  mk_foreign_to_ejson_runtime
    enhanced_foreign_runtime
    enhanced_foreign_ejson
    enhanced_foreign_to_ejson
    enhanced_foreign_ejson_runtime
    _ _ _ _.
Next Obligation.
  exact (sql_date_unary_op_to_ejson uop).
Defined.
Next Obligation.
  apply sql_date_unary_op_to_ejson_correct.
Defined.
Next Obligation.
  exact (sql_date_binary_op_to_ejson bop).
Defined.
Next Obligation.
  apply sql_date_binary_op_to_ejson_correct.
Defined.

