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
Require Import ToString.
Require Import Utils.
Require Import JSONSystem.
Require Import EJsonSystem.
Require Import DataSystem.
Require Import ForeignToJava.
Require Import ForeignToJavaScriptAst.
Require Import ForeignToScala.
Require Import ForeignEJson.
Require Import ForeignDataToEJson.
Require Import ForeignToEJsonRuntime.
Require Import ForeignEJsonToJSON.
Require Import ForeignTypeToJSON.
Require Import ForeignToSpark.
Require Import ForeignEJsonRuntime.
Require Import ForeignReduceOps.
Require Import ForeignToReduceOps.
Require Import CompilerRuntime.
Require Import CompilerModel.
Require Import SqlDateModelPart.
Require NNRCMR.
Require Import OptimizerLogger.
Require Import String.
Require Import cNRAEnv.
Require Import NRAEnv.
Require Import cNNRC.
Require Import NNRSimp.
Require Import DNNRCBase.
Require Import tDNNRC.
Require Import Dataframe.

Import ListNotations.

Local Open Scope list_scope.

Inductive enhanced_data : Set :=
| enhancedsqldate : SQL_DATE -> enhanced_data
| enhancedsqldateinterval : SQL_DATE_INTERVAL -> enhanced_data
.

Definition enhanced_ejson : Set := enhanced_data.

Inductive enhanced_type : Set :=
| enhancedTop : enhanced_type
| enhancedBottom : enhanced_type
| enhancedSqlDate : enhanced_type
| enhancedSqlDateInterval : enhanced_type
.

Definition enhanced_type_to_string (et:enhanced_type) : string :=
  match et with
  | enhancedTop => "ETop"
  | enhancedBottom => "EBottom"
  | enhancedSqlDate => "ESqlDate"
  | enhancedSqlDateInterval => "ESqlDateInterval"
  end.

Definition string_to_enhanced_type (s:string) : option enhanced_type :=
  match s with
  | "ETop"%string => Some enhancedTop
  | "EBottom"%string => Some enhancedBottom
  | "ESqlDate"%string => Some enhancedSqlDate
  | "ESqlDateInterval"%string => Some enhancedSqlDateInterval
  | _ => None
  end.

Require Import RelationClasses Equivalence.

Existing Instance sql_date_foreign_data.
Existing Instance sql_date_interval_foreign_data.

Program Instance enhanced_foreign_data : foreign_data
  := mk_foreign_data enhanced_data _ _ _ _ _ _.
Next Obligation.
  red.
  unfold equiv, complement.
  destruct x; destruct y; simpl; try solve [right; inversion 1].
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec sql_date_foreign_data) s s0).
    + left; congruence.
    + right; congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec sql_date_interval_foreign_data) s s0).
    + left; congruence.
    + right; congruence.
Defined.
Next Obligation.
  (* normalized? *)
  destruct a.
  - exact (@foreign_data_normalized sql_date_foreign_data s).
  - exact (@foreign_data_normalized sql_date_interval_foreign_data s).
Defined.
Next Obligation.
  destruct a.
  - exact (@foreign_data_normalize_normalizes sql_date_foreign_data s).
  - exact (@foreign_data_normalize_normalizes sql_date_interval_foreign_data s).
Defined.
Next Obligation.
  constructor.
  destruct 1.
  - exact (@toString _ (@foreign_data_tostring sql_date_foreign_data) s).
  - exact (@toString _ (@foreign_data_tostring sql_date_interval_foreign_data) s).
Defined.

Program Instance enhanced_foreign_ejson : foreign_ejson
  := mk_foreign_ejson enhanced_ejson _ _ _ _ _ _.
Next Obligation.
  red.
  unfold equiv, complement.
  destruct x; destruct y; simpl; try solve [right; inversion 1].
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec sql_date_foreign_data) s s0).
    + left; congruence.
    + right; congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec sql_date_interval_foreign_data) s s0).
    + left; congruence.
    + right; congruence.
Defined.
Next Obligation.
  (* normalized? *)
  destruct a.
  - exact (@foreign_data_normalized sql_date_foreign_data s).
  - exact (@foreign_data_normalized sql_date_interval_foreign_data s).
Defined.
Next Obligation.
  destruct a.
  - exact (@foreign_data_normalize_normalizes sql_date_foreign_data s).
  - exact (@foreign_data_normalize_normalizes sql_date_interval_foreign_data s).
Defined.
Next Obligation.
  constructor.
  destruct 1.
  - exact (@toString _ (@foreign_data_tostring sql_date_foreign_data) s).
  - exact (@toString _ (@foreign_data_tostring sql_date_interval_foreign_data) s).
Defined.

Definition denhancedsqldate td := dforeign (enhancedsqldate td).
Definition denhancedsqldateinterval td := dforeign (enhancedsqldateinterval td).

Inductive enhanced_unary_op :=
| enhanced_unary_sql_date_op : sql_date_unary_op -> enhanced_unary_op.

Definition ondsqldate {A} (f : SQL_DATE -> A) (d : data) : option A :=
  match d with
  | dforeign (enhancedsqldate fd) => Some (f fd)
  | _ => None
  end.



Definition ondstring {A} (f : String.string -> A) (d : data) : option A :=
  match d with
  | dstring s => Some (f s)
  | _ => None
  end.

Definition sql_date_unary_op_interp (op:sql_date_unary_op) (d:data) : option data :=
  match op with
  | uop_sql_date_get_component part =>
    lift dnat (ondsqldate (SQL_DATE_get_component part) d)
  | uop_sql_date_from_string =>
    lift denhancedsqldate (ondstring SQL_DATE_from_string d)
  | uop_sql_date_interval_from_string =>
    lift denhancedsqldateinterval (ondstring SQL_DATE_INTERVAL_from_string d)
  end.

Definition enhanced_unary_op_interp
           (br:brand_relation_t)
           (op:enhanced_unary_op)
           (d:data) : option data :=
  match op with
  | enhanced_unary_sql_date_op f => sql_date_unary_op_interp f d
  end.

Require Import String.

Inductive enhanced_binary_op :=
| enhanced_binary_sql_date_op : sql_date_binary_op -> enhanced_binary_op
.

Definition ondsqldate2 {A} (f : SQL_DATE -> SQL_DATE -> A) (d1 d2 : data) : option A
  := match d1, d2 with
     | dforeign (enhancedsqldate fd1), dforeign (enhancedsqldate fd2) => Some (f fd1 fd2)
     | _, _ => None
     end.

Definition ondsqldatez2 {A} (f : SQL_DATE -> Z -> A) (d1 d2 : data) : option A
  := match d1, d2 with
     | dforeign (enhancedsqldate fd1), dnat z => Some (f fd1 z)
     | _, _ => None
     end.

Definition rondboolsqldate2 (f: SQL_DATE -> SQL_DATE -> bool) (d1 d2:data) : option data
  := lift dbool (ondsqldate2 f d1 d2).

Definition sql_date_binary_op_interp
           (op:sql_date_binary_op) (d1 d2:data) : option data
  := match op with
     | bop_sql_date_plus
       => match d1, d2 with
          | dforeign (enhancedsqldate tp), dforeign (enhancedsqldateinterval td)
            => Some (denhancedsqldate (SQL_DATE_plus tp td))
          | _,_ => None
          end
     | bop_sql_date_minus
       => match d1, d2 with
          | dforeign (enhancedsqldate tp), dforeign (enhancedsqldateinterval td)
            => Some (denhancedsqldate (SQL_DATE_minus tp td))
          | _,_ => None
          end
     | bop_sql_date_ne => rondboolsqldate2 SQL_DATE_ne d1 d2
     | bop_sql_date_lt => rondboolsqldate2 SQL_DATE_lt d1 d2
     | bop_sql_date_le => rondboolsqldate2 SQL_DATE_le d1 d2
     | bop_sql_date_gt => rondboolsqldate2 SQL_DATE_gt d1 d2
     | bop_sql_date_ge => rondboolsqldate2 SQL_DATE_ge d1 d2
     | bop_sql_date_interval_between =>
       lift denhancedsqldateinterval (ondsqldate2 SQL_DATE_INTERVAL_between d1 d2)
     | bop_sql_date_set_component part =>
       lift denhancedsqldate (ondsqldatez2 (SQL_DATE_set_component part) d1 d2)
     end.

Definition enhanced_binary_op_interp
           (br:brand_relation_t)
           (op:enhanced_binary_op)
           (d1 d2:data) : option data
  := match op with
     | enhanced_binary_sql_date_op f => sql_date_binary_op_interp f d1 d2
     end.

Program Instance enhanced_foreign_operators : foreign_operators
  := { foreign_operators_unary := enhanced_unary_op
       ; foreign_operators_unary_interp := enhanced_unary_op_interp
       ; foreign_operators_unary_data_tostring := defaultDataToString
       ; foreign_operators_unary_data_totext := defaultDataToString
       ; foreign_operators_binary := enhanced_binary_op
       ; foreign_operators_binary_interp := enhanced_binary_op_interp }.
Next Obligation.
  red; unfold equiv; intros.
  change ({x = y} + {x <> y}).
  decide equality.
  - decide equality.
    decide equality.
Defined.
Next Obligation.
  constructor; intros op.
  destruct op.
  - exact (sql_date_unary_op_tostring s).
Defined.
Next Obligation.
  destruct op; simpl in H.
  - destruct s; simpl in H;
      unfold ondsqldate, denhancedsqldate, denhancedsqldateinterval, lift in H; simpl in H;
        destruct d; simpl in H; try discriminate.
    + destruct f; invcs H; repeat constructor.
    + invcs H; repeat constructor.
    + invcs H; repeat constructor.
Defined.
Next Obligation.
  red; unfold equiv; intros.
  change ({x = y} + {x <> y}).
  decide equality.
  - decide equality.
    decide equality.
Defined.
Next Obligation.
  constructor; intros op.
  destruct op.
  - exact (sql_date_binary_op_tostring s).
Defined.
Next Obligation.
  destruct op; simpl in H.
  - destruct s; simpl in H;
      unfold rondboolsqldate2, ondsqldate2, denhancedsqldate, lift in H
      ; destruct d1; simpl in H; try discriminate
      ; destruct f; simpl in H; try discriminate
      ; destruct d2; simpl in H; try discriminate
      ; try (destruct f; simpl in H; try discriminate)
      ; invcs H
      ; repeat constructor.
Qed.

Instance enhanced_foreign_runtime :
  foreign_runtime
  := mk_foreign_runtime
       enhanced_foreign_data
       enhanced_foreign_operators.

Inductive enhanced_foreign_ejson_runtime_op :=
| enhanced_EJsonRuntimeDateFromString
| enhanced_EJsonRuntimeDateGetYear
| enhanced_EJsonRuntimeDateGetMonth
| enhanced_EJsonRuntimeDateGetDay
| enhanced_EJsonRuntimeDateNe
| enhanced_EJsonRuntimeDateLt
| enhanced_EJsonRuntimeDateLe
| enhanced_EJsonRuntimeDateGt
| enhanced_EJsonRuntimeDateGe
| enhanced_EJsonRuntimeDateSetYear
| enhanced_EJsonRuntimeDateSetMonth
| enhanced_EJsonRuntimeDateSetDay
| enhanced_EJsonRuntimeDurationFromString
| enhanced_EJsonRuntimeDurationPlus
| enhanced_EJsonRuntimeDurationMinus
| enhanced_EJsonRuntimeDurationBetween.

Definition enhanced_foreign_ejson_runtime_op_tostring op : string :=
  match op with
  | enhanced_EJsonRuntimeDateFromString => "dateFromString"
  | enhanced_EJsonRuntimeDateGetYear => "dateGetYear"
  | enhanced_EJsonRuntimeDateGetMonth => "dateGetMonth"
  | enhanced_EJsonRuntimeDateGetDay => "dateGetDay"
  | enhanced_EJsonRuntimeDateNe => "dateNe"
  | enhanced_EJsonRuntimeDateLt => "dateLt"
  | enhanced_EJsonRuntimeDateLe => "dateLe"
  | enhanced_EJsonRuntimeDateGt => "dateGt"
  | enhanced_EJsonRuntimeDateGe => "dateGe"
  | enhanced_EJsonRuntimeDateSetYear => "dateSetYear"
  | enhanced_EJsonRuntimeDateSetMonth => "dateSetMonth"
  | enhanced_EJsonRuntimeDateSetDay => "dateSetDay"
  | enhanced_EJsonRuntimeDurationFromString => "durationFromString"
  | enhanced_EJsonRuntimeDurationPlus => "durationlus"
  | enhanced_EJsonRuntimeDurationMinus => "durationMinus"
  | enhanced_EJsonRuntimeDurationBetween => "durationBetween"
  end.

Definition enhanced_foreign_ejson_runtime_op_interp op (dl:list ejson) : option ejson :=
  match op with
  | enhanced_EJsonRuntimeDateFromString =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejstring s => Some (ejforeign (enhancedsqldate (SQL_DATE_from_string s)))
         | _ => None
         end) dl
  | enhanced_EJsonRuntimeDateGetYear =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhancedsqldate s) =>
           Some (ejbigint (SQL_DATE_get_component sql_date_YEAR s))
         | _ => None
         end) dl
  | enhanced_EJsonRuntimeDateGetMonth =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhancedsqldate fd) =>
           Some (ejbigint (SQL_DATE_get_component sql_date_MONTH fd))
         | _ => None
         end) dl
  | enhanced_EJsonRuntimeDateGetDay =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhancedsqldate fd) =>
           Some (ejbigint (SQL_DATE_get_component sql_date_DAY fd))
         | _ => None
         end) dl
  | enhanced_EJsonRuntimeDateNe =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejbool (SQL_DATE_ne fd1 fd2))
         | _, _ => None
         end) dl
  | enhanced_EJsonRuntimeDateLt =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejbool (SQL_DATE_lt fd1 fd2))
         | _, _ => None
         end) dl
  | enhanced_EJsonRuntimeDateLe =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejbool (SQL_DATE_le fd1 fd2))
         | _, _ => None
         end) dl
  | enhanced_EJsonRuntimeDateGt =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejbool (SQL_DATE_gt fd1 fd2))
         | _, _ => None
         end) dl
  | enhanced_EJsonRuntimeDateGe =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejbool (SQL_DATE_ge fd1 fd2))
         | _, _ => None
         end) dl
  | enhanced_EJsonRuntimeDateSetYear =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd), ejbigint n =>
           Some (ejforeign (enhancedsqldate (SQL_DATE_set_component sql_date_YEAR fd n)))
         | _, _ => None
         end) dl
  | enhanced_EJsonRuntimeDateSetMonth =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd), ejbigint n =>
           Some (ejforeign (enhancedsqldate (SQL_DATE_set_component sql_date_MONTH fd n)))
         | _, _ => None
         end) dl
  | enhanced_EJsonRuntimeDateSetDay =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd), ejbigint n =>
           Some (ejforeign (enhancedsqldate (SQL_DATE_set_component sql_date_DAY fd n)))
         | _, _ => None
         end) dl
  | enhanced_EJsonRuntimeDurationFromString =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejstring s => Some (ejforeign (enhancedsqldateinterval (SQL_DATE_INTERVAL_from_string s)))
         | _ => None
         end) dl
  | enhanced_EJsonRuntimeDurationPlus =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd), ejforeign (enhancedsqldateinterval id) =>
           Some (ejforeign (enhancedsqldate (SQL_DATE_plus fd id)))
         | _, _ => None
         end) dl
  | enhanced_EJsonRuntimeDurationMinus =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd), ejforeign (enhancedsqldateinterval id) =>
           Some (ejforeign (enhancedsqldate (SQL_DATE_minus fd id)))
         | _, _ => None
         end) dl
  | enhanced_EJsonRuntimeDurationBetween =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejforeign (enhancedsqldateinterval (SQL_DATE_INTERVAL_between fd1 fd2)))
         | _, _ => None
         end) dl
  end.

Program Instance enhanced_foreign_ejson_runtime : foreign_ejson_runtime :=
  mk_foreign_ejson_runtime enhanced_foreign_ejson enhanced_foreign_ejson_runtime_op _ _ _.
Next Obligation.
  red; unfold equiv; intros.
  change ({x = y} + {x <> y}).
  decide equality.
Defined.
Next Obligation.
  constructor; intros op.
  exact (enhanced_foreign_ejson_runtime_op_tostring op).
Defined.
Next Obligation.
  exact (enhanced_foreign_ejson_runtime_op_interp f dl).
Defined.

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

Definition enhanced_foreign_json_to_ejson (j:json) : option enhanced_ejson :=
  match j with
  | jobject (("$date"%string,jstring s)::nil) =>
    Some (enhancedsqldate (SQL_DATE_from_string s))
  | jobject (("$interval"%string,jstring s)::nil) =>
    Some (enhancedsqldateinterval (SQL_DATE_INTERVAL_from_string s))
  | _ => None
  end.

Definition enhanced_foreign_ejson_to_json (ej:enhanced_ejson) : json :=
  match ej with
  | enhancedsqldate fd =>
    jobject
      (("$date"%string,
        jstring (SQL_DATE_to_string fd))::nil)
  | enhancedsqldateinterval fd =>
    jobject
      (("$interval"%string,
        jstring (SQL_DATE_INTERVAL_to_string fd))::nil)
  end.

Lemma enhanced_foreign_json_to_ejson_correct (ej:enhanced_ejson) :
  enhanced_foreign_json_to_ejson (enhanced_foreign_ejson_to_json ej) = Some ej.
Proof.
  destruct ej; try reflexivity.
  - simpl. rewrite SQL_DATE_from_string_correct; reflexivity.
  - simpl. rewrite SQL_DATE_INTERVAL_from_string_correct; reflexivity.
Qed.

Program Instance enhanced_foreign_to_json : foreign_to_json
  := mk_foreign_to_json enhanced_foreign_ejson _ _ _.
Next Obligation.
  exact (enhanced_foreign_json_to_ejson fd).
Defined.
Next Obligation.
  exact (enhanced_foreign_ejson_to_json j).
Defined.
Next Obligation.
  apply enhanced_foreign_json_to_ejson_correct.
Defined.

(* XXX TODO: fix me *)
Local Open Scope nstring_scope.
Definition enhanced_to_java_data
           (quotel:nstring) (fd:enhanced_data) : java_json
  := match fd with
     | enhancedsqldate tp => mk_java_json (^@toString _ sql_date_foreign_data.(@foreign_data_tostring ) tp)
     | enhancedsqldateinterval tp => mk_java_json (^@toString _ sql_date_interval_foreign_data.(@foreign_data_tostring ) tp)
     end.

Definition enhanced_to_java_unary_op
           (indent:nat) (eol:nstring)
           (quotel:nstring) (fu:enhanced_unary_op)
           (d:java_json) : java_json
  := match fu with
     | enhanced_unary_sql_date_op op =>
       sql_date_to_java_unary_op indent eol quotel op d
     end.

Definition enhanced_to_java_binary_op
           (indent:nat) (eol:nstring)
           (quotel:nstring) (fb:enhanced_binary_op)
           (d1 d2:java_json) : java_json
  := match fb with
     | enhanced_binary_sql_date_op op =>
       sql_date_to_java_binary_op indent eol quotel op d1 d2
     end.

Instance enhanced_foreign_to_java :
  @foreign_to_java enhanced_foreign_runtime
  := mk_foreign_to_java
       enhanced_foreign_runtime
       enhanced_to_java_data
       enhanced_to_java_unary_op
       enhanced_to_java_binary_op.

Definition enhanced_ejson_to_ajavascript_expr (j:enhanced_ejson) : JsAst.JsSyntax.expr :=
  JsAst.JsSyntax.expr_literal (JsAst.JsSyntax.literal_null).

Instance enhanced_foreign_ejson_to_ajavascript :
  @foreign_ejson_to_ajavascript enhanced_foreign_ejson
  := mk_foreign_ejson_to_ajavascript
       enhanced_foreign_ejson
       enhanced_ejson_to_ajavascript_expr.

Definition enhanced_to_scala_unary_op (op: enhanced_unary_op) (d: nstring) : nstring :=
  match op with
  | enhanced_unary_sql_date_op op => ^"EnhancedModel: SQL date ops not supported for now."
  end.

Definition enhanced_to_scala_spark_datatype {ftype: foreign_type} (ft: foreign_type_type) : nstring :=
  (* AVI: This is obviously not correct. Where is the place I should put this? *)
  ^"FloatType".

Instance enhanced_foreign_to_scala {ftype: foreign_type}:
  @foreign_to_scala enhanced_foreign_runtime _
  := mk_foreign_to_scala
       enhanced_foreign_runtime _
       enhanced_to_scala_unary_op
       enhanced_to_scala_spark_datatype.

(* TODO: add general support for "tagged" stuff in JSON.
    Like our left/right encoding.  so that we can use it for
    timescale/timepoint.  just using a string may work for now.
 *)

Inductive enhanced_numeric_type :=
| enhanced_numeric_int
| enhanced_numeric_float.

Global Instance enhanced_numeric_type_eqdec : EqDec enhanced_numeric_type eq.
Proof.
  red. unfold equiv, complement.
  change (forall x y : enhanced_numeric_type, {x = y} + {x <> y}).
  decide equality.
Defined.

Inductive enhanced_reduce_op
  := RedOpCount : enhanced_reduce_op
   | RedOpSum (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpMin (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpMax (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpArithMean (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpStats (typ:enhanced_numeric_type) : enhanced_reduce_op.

Definition enhanced_numeric_type_prefix
           (typ:enhanced_numeric_type) : string
  := match typ with
     | enhanced_numeric_int => ""%string
     | enhanced_numeric_float => "F"%string
     end.

Definition enhanced_reduce_op_tostring (op:enhanced_reduce_op) : string
  := match op with
     | RedOpCount => "COUNT"%string
     | RedOpSum typ => append (enhanced_numeric_type_prefix typ) "FSUM"%string
     | RedOpMin typ  => append (enhanced_numeric_type_prefix typ) "FMIN"%string
     | RedOpMax typ => append (enhanced_numeric_type_prefix typ) "FMAX"%string
     | RedOpArithMean typ => append (enhanced_numeric_type_prefix typ) "FARITHMEAN"%string
     | RedOpStats typ => append (enhanced_numeric_type_prefix typ) "FSTATS"%string
     end.

Definition enhanced_numeric_sum (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatSum
     | enhanced_numeric_float
       => OpFloatSum
     end.

Definition enhanced_numeric_min (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatMin
     | enhanced_numeric_float
       => OpFloatBagMin
     end.

Definition enhanced_numeric_max (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatMax
     | enhanced_numeric_float
       => OpFloatBagMax
     end.

Definition enhanced_numeric_arith_mean (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatMean
     | enhanced_numeric_float
       => OpFloatMean
     end.

Definition enhanced_reduce_op_interp
           (br:brand_relation_t)
           (op:enhanced_reduce_op)
           (dl:list data) : option data
  := match op with
     | RedOpCount | RedOpSum _ | RedOpMin _ | RedOpMax _ | RedOpArithMean _ =>
                                                           let uop :=
                                                               match op with
                                                               | RedOpCount  => OpCount
                                                               | RedOpSum typ => enhanced_numeric_sum typ
                                                               | RedOpMin typ => enhanced_numeric_min typ
                                                               | RedOpMax typ => enhanced_numeric_max typ
                                                               | RedOpArithMean typ => enhanced_numeric_arith_mean typ
                                                               | RedOpStats _ => OpCount (* assert false *)
                                                               end
                                                           in
                                                           unary_op_eval br uop (dcoll dl) 
     | RedOpStats typ =>
       let coll := dcoll dl in
       let count := unary_op_eval br OpCount coll in
       let sum := unary_op_eval br (enhanced_numeric_sum typ) coll in
       let min := unary_op_eval br (enhanced_numeric_min typ) coll in
       let max := unary_op_eval br (enhanced_numeric_max typ) coll in
       let v :=
           match (count, sum, min, max) with
           | (Some count, Some sum, Some min, Some max) =>
             Some (drec (("count"%string, count)
                           ::("max"%string, max)
                           ::("min"%string, min)
                           ::("sum"%string, sum)
                           ::nil))
           | _ => None
           end
       in
       v
     end.

Program Instance enhanced_foreign_reduce_op : foreign_reduce_op
  := mk_foreign_reduce_op enhanced_foreign_data enhanced_reduce_op _ _ enhanced_reduce_op_interp _.
Next Obligation.
  red; unfold equiv, complement.
  change (forall x y:enhanced_reduce_op, {x = y} + {x <> y}).
  decide equality; decide equality.
Defined.
Next Obligation.
  constructor.
  apply enhanced_reduce_op_tostring.
Defined.
Next Obligation.
  destruct op; simpl in *; invcs H.
  - constructor.
  - destruct typ; simpl in *.
    + apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + unfold lifted_min in *.
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold lifted_fmin in *.
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + unfold lifted_max in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold lifted_fmax in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + unfold lifted_max in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold lifted_fmax in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + destruct (dsum dl); simpl in *; try discriminate.
      unfold lifted_min, lifted_max in *.
      destruct ((lift bnummin (lifted_zbag dl))); simpl in *; try discriminate.
      destruct ((lift bnummax (lifted_zbag dl))); simpl in *; try discriminate.
      invcs H2.
      constructor.
      * repeat constructor.
      * reflexivity.
    + case_eq (lifted_fsum dl); intros; simpl in *; rewrite H in *; try discriminate.
      unfold lifted_fmin, lifted_fmax in *.
      destruct ((lift float_list_min (lifted_fbag dl))); simpl in *; try discriminate.
      destruct ((lift float_list_max (lifted_fbag dl))); simpl in *; try discriminate.
      invcs H2.
      constructor.
      * repeat constructor.
        apply some_lift in H; destruct H as [? eqq ?]; subst.
        constructor.
      * reflexivity.
Qed.

Definition enhanced_to_reduce_op (uop:unary_op) : option NNRCMR.reduce_op
  := match uop with
     | OpCount => Some (NNRCMR.RedOpForeign RedOpCount)
     | OpNatSum =>
       Some (NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_int))
     | OpFloatSum =>
       Some (NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_float))
     | OpNatMin =>
       Some (NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_int))
     | OpFloatBagMin =>
       Some (NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_float))
     | OpNatMax =>
       Some (NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_int))
     | OpFloatBagMax =>
       Some (NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_float))
     | OpNatMean =>
       Some (NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_int))
     | OpFloatMean =>
       Some (NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_float))
     | _ => None
     end.

Definition enhanced_of_reduce_op (rop:NNRCMR.reduce_op) : option unary_op
  := match rop with
     | NNRCMR.RedOpForeign RedOpCount => Some OpCount
     | NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_int) =>
       Some (OpNatSum)
     | NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_float) =>
       Some (OpFloatSum)
     | NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_int) =>
       Some (OpNatMin)
     | NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_float) =>
       Some (OpFloatBagMin)
     | NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_int) =>
       Some (OpNatMax)
     | NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_float) =>
       Some (OpFloatBagMax)
     | NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_int) =>
       Some (OpNatMean)
     | NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_float) =>
       Some (OpFloatMean)
     | NNRCMR.RedOpForeign (RedOpStats _) =>
       None (* XXX TODO? XXX *)
     end.

Program Instance enhanced_foreign_to_reduce_op : foreign_to_reduce_op
  := mk_foreign_to_reduce_op enhanced_foreign_runtime enhanced_foreign_reduce_op enhanced_to_reduce_op _ enhanced_of_reduce_op _.
Next Obligation.
  unfold NNRCMR.reduce_op_eval.
  destruct uop; simpl in *; invcs H; try reflexivity.
Qed.
Next Obligation.
  unfold NNRCMR.reduce_op_eval.
  destruct rop; simpl in *; invcs H; try reflexivity.
  destruct f; invcs H1; simpl; try reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
Qed.

Local Open Scope string_scope.
Definition enhanced_to_spark_reduce_op
           (rop:enhanced_reduce_op)
           (scala_endl quotel:nstring) : nstring
  := match rop with
     | RedOpCount => ^".count().toString()"
     | RedOpSum enhanced_numeric_int => ^".aggregate(0)(_ + _.toInt, _ + _).toString()"
     | RedOpSum enhanced_numeric_float => ^".aggregate(0.0)(_ + _.toDouble, _ + _).toString()"
     | RedOpMin enhanced_numeric_int => ^".aggregate(Int.MaxValue)(((x, y) => Math.min(x, y.toInt)), Math.min).toString()"
     | RedOpMin enhanced_numeric_float => ^".aggregate(Double.MaxValue)(((x, y) => Math.min(x, y.toDouble)), Math.min).toString()"
     | RedOpMax enhanced_numeric_int =>
       ^".aggregate(Int.MinValue)(((x, y) => Math.max(x, y.toInt)), Math.max).toString()"
     | RedOpMax enhanced_numeric_float =>
       ^".aggregate(Double.MinValue)(((x, y) => Math.max(x, y.toDouble)), Math.max).toString()"
     | RedOpStats _ =>
       ^".aggregate("""")(statsReduce, statsRereduce).toString()" +++ scala_endl +++
                     ^"  sc.parallelize(Array(res))"
     | RedOpArithMean _ => (* assert false *)
       ^".arithmean /* ArithMean must be removed before code generation */"
     end.

(* NNRCMR rewrites *)
Require Import NNRCRuntime NNRCMRRuntime NNRCMRRewrite.

(* Java equivalent: MROptimizer.min_max_to_stats *)
Definition min_max_to_stats avoid (mr: mr) :=
  match mr.(mr_reduce) with
  | RedOp (RedOpForeign op) =>
    match op with
    | RedOpMin typ | RedOpMax typ =>
                     let stats_field :=
                         match op with
                         | RedOpMin _ => "min"%string
                         | RedOpMax _ => "max"%string
                         | _ => "ERROR"%string (* assert false *)
                         end
                     in
                     let (tmp, avoid) := fresh_mr_var "stats$" avoid in
                     let mr1 :=
                         mkMR
                           mr.(mr_input)
                                tmp
                                mr.(mr_map)
                                     (RedOp (RedOpForeign (RedOpStats typ)))
                     in
                     let x := "stats"%string in
                     let mr2 :=
                         mkMR
                           tmp
                           mr.(mr_output)
                                (MapScalar (x, NNRCUnop OpBag (NNRCUnop (OpDot stats_field) (NNRCVar x))))
                                RedSingleton
                     in
                     Some (mr1::mr2::nil)
    | _ => None
    end
  | _ => None
  end.

(* Java equivalent: MROptimizer.arithmean_to_stats *)
Definition arithmean_to_stats avoid (mr: mr) :=
  match mr.(mr_reduce) with
  | RedOp (RedOpForeign op) =>
    match op with
    | RedOpArithMean typ =>
      let (tmp, avoid) := fresh_mr_var "stats$" avoid in
      let mr1 :=
          mkMR
            mr.(mr_input)
                 tmp
                 mr.(mr_map)
                      (RedOp (RedOpForeign (RedOpStats typ)))
      in
      let map :=
          match typ with
          | enhanced_numeric_int =>
            let zero := NNRCConst (dnat 0) in
            let x := "stats"%string in
            MapScalar (x, NNRCUnop OpBag
                                   (NNRCIf (NNRCBinop OpEqual (NNRCUnop (OpDot "count"%string) (NNRCVar x)) zero)
                                           zero
                                           (NNRCBinop (OpNatBinary NatDiv)
                                                      (NNRCUnop (OpDot "sum"%string) (NNRCVar x))
                                                      (NNRCUnop (OpDot "count"%string) (NNRCVar x)))))
          | enhanced_numeric_float =>
            let zero := NNRCConst (dnat 0) in
            let zerof := NNRCConst (dfloat float_zero) in
            let x := "stats"%string in
            MapScalar (x, NNRCUnop OpBag
                                   (NNRCIf (NNRCBinop OpEqual (NNRCUnop (OpDot "count"%string) (NNRCVar x)) zero)
                                           zerof
                                           (NNRCBinop (OpFloatBinary FloatDiv)
                                                      (NNRCUnop (OpDot "sum"%string) (NNRCVar x))
                                                      (NNRCUnop (OpFloatOfNat)
                                                                (NNRCUnop (OpDot "count"%string) (NNRCVar x))))))
          end
      in
      let mr2 :=
          mkMR
            tmp
            mr.(mr_output)
                 map
                 RedSingleton
      in
      Some (mr1::mr2::nil)
    | _ => None
    end
  | _ => None
  end.

Definition min_max_free_reduce (src:reduce_fun)
  := match src with
     | RedOp (RedOpForeign (RedOpMin _|RedOpMax _)) => False
     | _ => True
     end.

Definition arithmean_free_reduce (src:reduce_fun)
  := match src with
     | RedOp (RedOpForeign (RedOpArithMean _)) => False
     | _ => True
     end.

Definition min_max_free_mr (src:mr)
  := min_max_free_reduce src.(mr_reduce).

Definition arithmean_free_mr (src:mr)
  := arithmean_free_reduce src.(mr_reduce).

Definition min_max_free_mr_chain (src:list mr)
  := Forall min_max_free_mr src.

Definition min_max_free_nnrcmr (src:nnrcmr)
  := min_max_free_mr_chain src.(mr_chain).

Definition arithmean_free_mr_chain (src:list mr)
  := Forall arithmean_free_mr src.

Definition arithmean_free_nnrcmr (src:nnrcmr)
  := arithmean_free_mr_chain src.(mr_chain).

Definition to_spark_nnrcmr (l: nnrcmr) :=
  let avoid := get_nnrcmr_vars l in
  let l := apply_rewrite (arithmean_to_stats avoid) l in
  l.

Definition to_spark_nnrcmr_prepared (src:nnrcmr)
  := arithmean_free_nnrcmr src.

Program Instance enhanced_foreign_to_spark : foreign_to_spark
  := mk_foreign_to_spark
       enhanced_foreign_runtime
       enhanced_foreign_reduce_op
       enhanced_to_spark_reduce_op
       to_spark_nnrcmr.

(* nra optimizer logger support *)
Axiom OPTIMIZER_LOGGER_nraenv_token_type : Set.
Extract Constant OPTIMIZER_LOGGER_nraenv_token_type => "Util.nra_logger_token_type".

Axiom OPTIMIZER_LOGGER_nraenv_startPass :
  String.string -> nraenv -> OPTIMIZER_LOGGER_nraenv_token_type.

Extract Constant OPTIMIZER_LOGGER_nraenv_startPass =>
"(fun name input -> Logger.nra_log_startPass (Util.string_of_char_list name) input)".

Axiom OPTIMIZER_LOGGER_nraenv_step :
  OPTIMIZER_LOGGER_nraenv_token_type -> String.string ->
  nraenv -> nraenv ->
  OPTIMIZER_LOGGER_nraenv_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nraenv_step =>
"(fun token name input output -> Logger.nra_log_step token (Util.string_of_char_list name) input output)".

Axiom OPTIMIZER_LOGGER_nraenv_endPass :
  OPTIMIZER_LOGGER_nraenv_token_type -> nraenv -> OPTIMIZER_LOGGER_nraenv_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nraenv_endPass =>
"(fun token output -> Logger.nra_log_endPass token output)".

Instance foreign_nraenv_optimizer_logger :
  optimizer_logger string nraenv
  :=
    {
      optimizer_logger_token_type := OPTIMIZER_LOGGER_nraenv_token_type
      ; logStartPass := OPTIMIZER_LOGGER_nraenv_startPass
      ; logStep :=  OPTIMIZER_LOGGER_nraenv_step
      ; logEndPass :=  OPTIMIZER_LOGGER_nraenv_endPass
    } .

(* nrc optimizer logger support *)
Axiom OPTIMIZER_LOGGER_nnrc_token_type : Set.
Extract Constant OPTIMIZER_LOGGER_nnrc_token_type => "Util.nrc_logger_token_type".

Axiom OPTIMIZER_LOGGER_nnrc_startPass :
  String.string -> nnrc -> OPTIMIZER_LOGGER_nnrc_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrc_startPass =>
"(fun name input -> Logger.nrc_log_startPass (Util.string_of_char_list name) input)".

Axiom OPTIMIZER_LOGGER_nnrc_step :
  OPTIMIZER_LOGGER_nnrc_token_type -> String.string ->
  nnrc -> nnrc ->
  OPTIMIZER_LOGGER_nnrc_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrc_step =>
"(fun token name input output -> Logger.nrc_log_step token (Util.string_of_char_list name) input output)".

Axiom OPTIMIZER_LOGGER_nnrc_endPass :
  OPTIMIZER_LOGGER_nnrc_token_type -> nnrc -> OPTIMIZER_LOGGER_nnrc_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrc_endPass =>
"(fun token output -> Logger.nrc_log_endPass token output)".

Instance foreign_nnrc_optimizer_logger :
  optimizer_logger string nnrc
  :=
    {
      optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrc_token_type
      ; logStartPass := OPTIMIZER_LOGGER_nnrc_startPass
      ; logStep :=  OPTIMIZER_LOGGER_nnrc_step
      ; logEndPass :=  OPTIMIZER_LOGGER_nnrc_endPass
    } .

(* nnrs_imp optimizer logger support *)
Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_token_type : Set.
Extract Constant OPTIMIZER_LOGGER_nnrs_imp_expr_token_type => "Util.nnrs_imp_expr_logger_token_type".

Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_startPass :
  String.string -> nnrs_imp_expr -> OPTIMIZER_LOGGER_nnrs_imp_expr_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_expr_startPass =>
"(fun name input -> Logger.nnrs_imp_expr_log_startPass (Util.string_of_char_list name) input)".

Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_step :
  OPTIMIZER_LOGGER_nnrs_imp_expr_token_type -> String.string ->
  nnrs_imp_expr -> nnrs_imp_expr ->
  OPTIMIZER_LOGGER_nnrs_imp_expr_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_expr_step =>
"(fun token name input output -> Logger.nnrs_imp_expr_log_step token (Util.string_of_char_list name) input output)".

Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_endPass :
  OPTIMIZER_LOGGER_nnrs_imp_expr_token_type -> nnrs_imp_expr -> OPTIMIZER_LOGGER_nnrs_imp_expr_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_expr_endPass =>
"(fun token output -> Logger.nnrs_imp_expr_log_endPass token output)".

Instance foreign_nnrs_imp_expr_optimizer_logger :
  optimizer_logger string nnrs_imp_expr
  :=
    {
      optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrs_imp_expr_token_type
      ; logStartPass := OPTIMIZER_LOGGER_nnrs_imp_expr_startPass
      ; logStep :=  OPTIMIZER_LOGGER_nnrs_imp_expr_step
      ; logEndPass :=  OPTIMIZER_LOGGER_nnrs_imp_expr_endPass
    } .

Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type : Set.
Extract Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type => "Util.nnrs_imp_stmt_logger_token_type".

Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_startPass :
  String.string -> nnrs_imp_stmt -> OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_startPass =>
"(fun name input -> Logger.nnrs_imp_stmt_log_startPass (Util.string_of_char_list name) input)".

Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_step :
  OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type -> String.string ->
  nnrs_imp_stmt -> nnrs_imp_stmt ->
  OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_step =>
"(fun token name input output -> Logger.nnrs_imp_stmt_log_step token (Util.string_of_char_list name) input output)".

Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_endPass :
  OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type -> nnrs_imp_stmt -> OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_endPass =>
"(fun token output -> Logger.nnrs_imp_stmt_log_endPass token output)".

Instance foreign_nnrs_imp_stmt_optimizer_logger :
  optimizer_logger string nnrs_imp_stmt
  :=
    {
      optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type
      ; logStartPass := OPTIMIZER_LOGGER_nnrs_imp_stmt_startPass
      ; logStep :=  OPTIMIZER_LOGGER_nnrs_imp_stmt_step
      ; logEndPass :=  OPTIMIZER_LOGGER_nnrs_imp_stmt_endPass
    } .

Axiom OPTIMIZER_LOGGER_nnrs_imp_token_type : Set.
Extract Constant OPTIMIZER_LOGGER_nnrs_imp_token_type => "Util.nnrs_imp_logger_token_type".

Axiom OPTIMIZER_LOGGER_nnrs_imp_startPass :
  String.string -> nnrs_imp -> OPTIMIZER_LOGGER_nnrs_imp_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_startPass =>
"(fun name input -> Logger.nnrs_imp_log_startPass (Util.string_of_char_list name) input)".

Axiom OPTIMIZER_LOGGER_nnrs_imp_step :
  OPTIMIZER_LOGGER_nnrs_imp_token_type -> String.string ->
  nnrs_imp -> nnrs_imp ->
  OPTIMIZER_LOGGER_nnrs_imp_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_step =>
"(fun token name input output -> Logger.nnrs_imp_log_step token (Util.string_of_char_list name) input output)".

Axiom OPTIMIZER_LOGGER_nnrs_imp_endPass :
  OPTIMIZER_LOGGER_nnrs_imp_token_type -> nnrs_imp -> OPTIMIZER_LOGGER_nnrs_imp_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_endPass =>
"(fun token output -> Logger.nnrs_imp_log_endPass token output)".

Instance foreign_nnrs_imp_optimizer_logger :
  optimizer_logger string nnrs_imp
  :=
    {
      optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrs_imp_token_type
      ; logStartPass := OPTIMIZER_LOGGER_nnrs_imp_startPass
      ; logStep :=  OPTIMIZER_LOGGER_nnrs_imp_step
      ; logEndPass :=  OPTIMIZER_LOGGER_nnrs_imp_endPass
    } .

(** Foreign typing, used to build the basic_model *)

Definition enhanced_type_join (t1 t2:enhanced_type)
  := match t1, t2 with
     | enhancedBottom, _ => t2
     | _, enhancedBottom => t1
     | enhancedSqlDate, enhancedSqlDate => enhancedSqlDate
     | enhancedSqlDateInterval, enhancedSqlDateInterval => enhancedSqlDateInterval
     | _, _ => enhancedTop
     end.

Definition enhanced_type_meet (t1 t2:enhanced_type)
  := match t1, t2 with
     | enhancedTop, _ => t2
     | _, enhancedTop => t1
     | enhancedSqlDate, enhancedSqlDate => enhancedSqlDate
     | enhancedSqlDateInterval, enhancedSqlDateInterval => enhancedSqlDateInterval
     | _, _ => enhancedBottom
     end.

Inductive enhanced_subtype : enhanced_type -> enhanced_type -> Prop :=
| enhanced_subtype_top t : enhanced_subtype t enhancedTop
| enhanced_subtype_bottom t : enhanced_subtype enhancedBottom t
| enhanced_subtype_refl t : enhanced_subtype t t.

Instance enhanced_subtype_pre : PreOrder enhanced_subtype.
Proof.
  constructor; red; intros.
  - destruct x; constructor.
  - inversion H; inversion H0; subst; try constructor; congruence.
Qed.

Instance enhanced_subtype_post : PartialOrder eq enhanced_subtype.
Proof.
  intros x y; split.
  - intros; subst.
    repeat red.
    split; constructor.
  - destruct 1.
    inversion H; inversion H0; congruence.
Qed.

Instance enhanced_type_lattice : Lattice enhanced_type eq
  := {
      join := enhanced_type_join
      ; meet := enhanced_type_meet
    }.
Proof.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
  - red; intros t1 t2 t3.
    destruct t1; destruct t2; destruct t3; simpl;
      reflexivity.
  - red; intros t1.
    simpl.
    destruct t1; simpl; try reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
  - red; intros t1 t2 t3.
    destruct t1; destruct t2; destruct t3; simpl;
      reflexivity.
  - red; intros t1.
    destruct t1; simpl;
      reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
Defined.

Instance enhanced_type_olattice : OLattice eq enhanced_subtype.
Proof.
  constructor.
  split.
  - destruct a; destruct b; inversion 1; simpl; reflexivity.
  - destruct a; destruct b; inversion 1; simpl;
      constructor.
Qed.

Program Instance enhanced_foreign_type : foreign_type
  := mk_foreign_type enhanced_type _ _ _ _ _ _ _.
Next Obligation.
  red.
  unfold equiv, complement.
  intros.
  change ({x = y} + {x <> y}).
  decide equality.
Defined.
Next Obligation.
  destruct a; destruct b; try solve [left; constructor | right; inversion 1].
Defined.

Program Instance enhanced_foreign_type_to_JSON : foreign_type_to_JSON
  := mk_foreign_type_to_JSON enhanced_foreign_type _ _.
Next Obligation.
  exact (string_to_enhanced_type s).
Defined.
Next Obligation.
  exact (enhanced_type_to_string fd).
Defined.

Inductive enhanced_has_type : enhanced_data -> enhanced_type -> Prop :=
| enhanced_has_type_top fd : enhanced_has_type fd enhancedTop
| enhanced_has_type_sqldate (tp:SQL_DATE) : enhanced_has_type (enhancedsqldate tp) enhancedSqlDate
| enhanced_has_type_sqldateinterval (tp:SQL_DATE_INTERVAL) : enhanced_has_type (enhancedsqldateinterval tp) enhancedSqlDateInterval
.

Definition enhanced_infer_type (d:enhanced_data) : option enhanced_type
  := match d with
     | enhancedsqldate _ => Some enhancedSqlDate
     | enhancedsqldateinterval _ => Some enhancedSqlDateInterval
     end.

Program Instance enhanced_foreign_data_typing :
  @foreign_data_typing enhanced_foreign_data enhanced_foreign_type
  := mk_foreign_data_typing
       enhanced_foreign_data
       enhanced_foreign_type
       enhanced_has_type _ _ _
       enhanced_infer_type _ _ _
.
Next Obligation.
  inversion H; subst;
    simpl; trivial.
  - destruct d; simpl; constructor.
  - constructor.
  - constructor.
Defined.
Next Obligation.
  inversion H0; subst; simpl.
  - constructor.
  - inversion H.
  - trivial.
Defined.
Next Obligation.
  inversion H; inversion H0; subst; simpl; try constructor; congruence.
Defined.
Next Obligation.
  destruct d; simpl; eexists; reflexivity.
Defined.
Next Obligation.
  destruct d; simpl in H; invcs H; constructor.
Defined.
Next Obligation.
  destruct d; simpl in H, H0
  ; invcs H; invcs H0; constructor.
Defined.

Definition dnnrc_for_log {br:brand_relation}
  := (@dnnrc_base enhanced_foreign_runtime (type_annotation unit) dataframe).

(* dnnrc optimizer logger support *)
Axiom OPTIMIZER_LOGGER_dnnrc_token_type : Set.
Extract Constant OPTIMIZER_LOGGER_dnnrc_token_type => "Util.dnrc_logger_token_type".

Axiom OPTIMIZER_LOGGER_dnnrc_startPass :
  forall {br:brand_relation}, String.string -> dnnrc_for_log -> OPTIMIZER_LOGGER_dnnrc_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_dnnrc_startPass =>
"(fun br name input -> Logger.dnrc_log_startPass (Util.string_of_char_list name) input)".

Axiom OPTIMIZER_LOGGER_dnnrc_step :
  forall  {br:brand_relation}, 
    OPTIMIZER_LOGGER_dnnrc_token_type -> String.string ->
    dnnrc_for_log -> dnnrc_for_log ->
    OPTIMIZER_LOGGER_dnnrc_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_dnnrc_step =>
"(fun br token name input output -> Logger.dnrc_log_step token (Util.string_of_char_list name) input output)".

Axiom OPTIMIZER_LOGGER_dnnrc_endPass :
  forall {br:brand_relation}, OPTIMIZER_LOGGER_dnnrc_token_type -> dnnrc_for_log -> OPTIMIZER_LOGGER_dnnrc_token_type.

Extract Inlined Constant OPTIMIZER_LOGGER_dnnrc_endPass =>
"(fun br token output -> Logger.dnrc_log_endPass token output)".

Instance foreign_dnnrc_optimizer_logger  {br:brand_relation} :
  optimizer_logger string dnnrc_for_log
  :=
    {
      optimizer_logger_token_type := OPTIMIZER_LOGGER_dnnrc_token_type
      ; logStartPass := OPTIMIZER_LOGGER_dnnrc_startPass
      ; logStep :=  OPTIMIZER_LOGGER_dnnrc_step
      ; logEndPass :=  OPTIMIZER_LOGGER_dnnrc_endPass
    } .

Module EnhancedRuntime <: CompilerRuntime.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
  Definition compiler_foreign_runtime : foreign_runtime
    := enhanced_foreign_runtime.
  Definition compiler_foreign_to_java : foreign_to_java
    := enhanced_foreign_to_java.
  Definition compiler_foreign_ejson : foreign_ejson
    := enhanced_foreign_ejson.
  Definition compiler_foreign_to_ejson : foreign_to_ejson
    := enhanced_foreign_to_ejson.
  Definition compiler_foreign_to_ejson_runtime : foreign_to_ejson_runtime
    := enhanced_foreign_to_ejson_runtime.
  Definition compiler_foreign_to_json : foreign_to_json
    := enhanced_foreign_to_json.
  Definition compiler_foreign_ejson_to_ajavascript : foreign_ejson_to_ajavascript
    := enhanced_foreign_ejson_to_ajavascript.
  Definition compiler_foreign_to_scala : foreign_to_scala
    := enhanced_foreign_to_scala.
  Definition compiler_foreign_type_to_JSON : foreign_type_to_JSON
    := enhanced_foreign_type_to_JSON.
  Definition compiler_foreign_reduce_op : foreign_reduce_op
    := enhanced_foreign_reduce_op.
  Definition compiler_foreign_to_reduce_op : foreign_to_reduce_op
    := enhanced_foreign_to_reduce_op.
  Definition compiler_foreign_to_spark : foreign_to_spark
    := enhanced_foreign_to_spark.
  Definition compiler_nraenv_optimizer_logger : optimizer_logger string nraenv
    := foreign_nraenv_optimizer_logger.
  Definition compiler_nnrc_optimizer_logger : optimizer_logger string nnrc
    := foreign_nnrc_optimizer_logger.
  Definition compiler_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr
    := foreign_nnrs_imp_expr_optimizer_logger.
  Definition compiler_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt
    := foreign_nnrs_imp_stmt_optimizer_logger.
  Definition compiler_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp
    := foreign_nnrs_imp_optimizer_logger.
  Definition compiler_dnnrc_optimizer_logger {br:brand_relation}: optimizer_logger string (@dnnrc_base _ (type_annotation unit) dataframe)
    := foreign_dnnrc_optimizer_logger.
  Definition compiler_foreign_data_typing : foreign_data_typing
    := enhanced_foreign_data_typing.
End EnhancedRuntime.

Definition SqlDate {br:brand_relation} : rtype := Foreign enhancedSqlDate.
Definition SqlDateInterval {br:brand_relation} : rtype := Foreign enhancedSqlDateInterval.

Definition isSqlDate {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedSqlDate => true
  | _ => false
  end.

Definition isSqlDateInterval {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedSqlDateInterval => true
  | _ => false
  end.

Definition isNat {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Nat₀ => true
  | _ => false
  end.

Definition isString {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | String₀ => true
  | _ => false
  end.

Definition tuncoll {model:brand_model} (τ:rtype) : option rtype.
Proof.
  destruct τ.
  destruct x.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact (Some (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e)). 
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
Defined.

Inductive sql_date_unary_op_has_type {model:brand_model} :
  sql_date_unary_op -> rtype -> rtype -> Prop
  :=
  | tuop_sql_date_get_component part : sql_date_unary_op_has_type (uop_sql_date_get_component part) SqlDate Nat
  | tuop_sql_date_from_string : sql_date_unary_op_has_type uop_sql_date_from_string RType.String SqlDate
  | tuop_sql_date_interval_from_string : sql_date_unary_op_has_type uop_sql_date_interval_from_string RType.String SqlDateInterval
.

Definition sql_date_unary_op_type_infer {model : brand_model} (op:sql_date_unary_op) (τ₁:rtype) : option rtype :=
  match op with
  | uop_sql_date_get_component part =>
    if isSqlDate τ₁ then Some Nat else None
  | uop_sql_date_from_string =>
    if isString τ₁ then Some SqlDate else None
  | uop_sql_date_interval_from_string =>
    if isString τ₁ then Some SqlDateInterval else None
  end.

Definition sql_date_unary_op_type_infer_sub {model : brand_model} (op:sql_date_unary_op) (τ₁:rtype) : option (rtype*rtype) :=
  match op with
  | uop_sql_date_get_component part =>
    enforce_unary_op_schema (τ₁,SqlDate) Nat
  | uop_sql_date_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) SqlDate
  | uop_sql_date_interval_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) SqlDateInterval
  end.

Lemma sql_date_unary_op_typing_sound {model : brand_model}
      (fu : sql_date_unary_op) (τin τout : rtype) :
  sql_date_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      sql_date_unary_op_interp fu din = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    try solve[inversion 1; subst;
              try invcs H0;
              try invcs H3;
              simpl; unfold denhancedsqldate, denhancedsqldateinterval; simpl;
              eexists; split; try reflexivity;
              repeat constructor].
Qed.

Inductive enhanced_unary_op_has_type {model:brand_model} : enhanced_unary_op -> rtype -> rtype -> Prop
  :=
  | tenhanced_unary_sql_date_op fu τin τout:
      sql_date_unary_op_has_type fu τin τout ->
      enhanced_unary_op_has_type (enhanced_unary_sql_date_op fu) τin τout.

Definition enhanced_unary_op_typing_infer {model:brand_model} (fu:enhanced_unary_op) (τ:rtype) : option rtype :=
  match fu with
  | enhanced_unary_sql_date_op op => sql_date_unary_op_type_infer op τ
  end.

Lemma enhanced_unary_op_typing_infer_correct
      {model:brand_model}
      (fu:foreign_operators_unary)
      {τ₁ τout} :
  enhanced_unary_op_typing_infer fu τ₁ = Some τout ->
  enhanced_unary_op_has_type fu τ₁ τout.
Proof.
  intros.
  destruct fu; simpl.
  - destruct s; simpl in *.
    + destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          destruct ft; simpl in *; try congruence;
            inversion H; subst; clear H; constructor;
              rewrite Foreign_canon; constructor.
    + destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          inversion H; subst; clear H; constructor;
            rewrite String_canon; constructor.
    + destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence.
      inversion H; subst; clear H; constructor.
      rewrite String_canon; constructor.
Qed.

Lemma enhanced_unary_op_typing_infer_least
      {model:brand_model}
      (fu:foreign_operators_unary)
      {τ₁ τout₁ τout₂} :
  enhanced_unary_op_typing_infer fu τ₁ = Some τout₁ ->
  enhanced_unary_op_has_type fu τ₁ τout₂ ->
  τout₁ ≤ τout₂.
Proof.
  intros.
  destruct fu; simpl in *.
  - destruct s; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence.
    + destruct ft; simpl in *; try congruence;
        inversion H; subst; clear H;
          rewrite Foreign_canon in H0;
          inversion H0; subst; clear H0;
            inversion H1; subst; clear H1;
              reflexivity.
    + inversion H; subst; clear H;
        rewrite String_canon in H0;
        inversion H0; subst; clear H0;
          inversion H1; subst; clear H1;
            reflexivity.
    + inversion H; subst; clear H;
        rewrite String_canon in H0;
        inversion H0; subst; clear H0;
          inversion H1; subst; clear H1;
            reflexivity.
Qed.

Lemma enhanced_unary_op_typing_infer_complete
      {model:brand_model}
      (fu:foreign_operators_unary)
      {τ₁ τout} : 
  enhanced_unary_op_typing_infer fu τ₁ = None ->
  ~ enhanced_unary_op_has_type fu τ₁ τout.
Proof.
  intros.
  destruct fu; simpl in *.
  - destruct s; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          unfold not; intros;
            inversion H0; subst; clear H0;
              inversion H2; subst; clear H2.
    + simpl in H; congruence.
Qed.

Definition enhanced_unary_op_typing_infer_sub {model:brand_model} (fu:enhanced_unary_op) (τ:rtype) : option (rtype*rtype) :=
  match fu with
  | enhanced_unary_sql_date_op op => sql_date_unary_op_type_infer_sub op τ
  end.

Lemma enhanced_unary_op_typing_sound {model : brand_model}
      (fu : foreign_operators_unary) (τin τout : rtype) :
  enhanced_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      enhanced_unary_op_interp brand_relation_brands fu din = Some dout /\ dout ▹ τout.
Proof.
  intros.
  destruct H.
  - eapply sql_date_unary_op_typing_sound; eauto.
Qed.

Inductive sql_date_binary_op_has_type {model:brand_model} :
  sql_date_binary_op -> rtype -> rtype -> rtype -> Prop
  :=
  | tbop_sql_date_plus :
      sql_date_binary_op_has_type bop_sql_date_plus SqlDate SqlDateInterval SqlDate 
  | tbop_sql_date_minus :
      sql_date_binary_op_has_type bop_sql_date_minus SqlDate SqlDateInterval SqlDate 
  | tbop_sql_date_ne :
      sql_date_binary_op_has_type bop_sql_date_ne SqlDate SqlDate Bool 
  | tbop_sql_date_lt :
      sql_date_binary_op_has_type bop_sql_date_lt SqlDate SqlDate Bool 
  | tbop_sql_date_le :
      sql_date_binary_op_has_type bop_sql_date_le SqlDate SqlDate Bool 
  | tbop_sql_date_gt :
      sql_date_binary_op_has_type bop_sql_date_gt SqlDate SqlDate Bool 
  | tbop_sql_date_ge :
      sql_date_binary_op_has_type bop_sql_date_ge SqlDate SqlDate Bool
  | tbop_sql_date_interval_between  :
      sql_date_binary_op_has_type bop_sql_date_interval_between SqlDate SqlDate SqlDateInterval
  | tbop_sql_date_set_component part : sql_date_binary_op_has_type (bop_sql_date_set_component part) SqlDate Nat SqlDate
.

Definition sql_date_binary_op_type_infer {model : brand_model} (op:sql_date_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | bop_sql_date_plus =>
    if isSqlDate τ₁ && isSqlDateInterval τ₂ then Some SqlDate else None
  | bop_sql_date_minus =>
    if isSqlDate τ₁ && isSqlDateInterval τ₂ then Some SqlDate else None
  | bop_sql_date_ne =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some Bool else None
  | bop_sql_date_lt =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some Bool else None
  | bop_sql_date_le =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some Bool else None
  | bop_sql_date_gt =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some Bool else None
  | bop_sql_date_ge =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some Bool else None
  | bop_sql_date_interval_between  =>
    if isSqlDate τ₁ && isSqlDate τ₂ then Some SqlDateInterval else None
  | bop_sql_date_set_component part =>
    if isSqlDate τ₁ && isNat τ₂ then Some SqlDate else None
  end.

Lemma sql_date_binary_op_typing_sound {model : brand_model}
      (fb : sql_date_binary_op) (τin₁ τin₂ τout : rtype) :
  sql_date_binary_op_has_type fb τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      sql_date_binary_op_interp fb din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    inversion 1; subst;
      inversion 1; subst;
        try invcs H0;
        try invcs H1;
        invcs H3;
        try invcs H4;
        simpl; 
        eexists; split; try reflexivity;
          repeat constructor.
Qed.

Definition sql_date_binary_op_type_infer_sub {model : brand_model} (op:sql_date_binary_op) (τ₁ τ₂:rtype) : option (rtype*rtype*rtype) :=
  match op with
  | bop_sql_date_plus => enforce_binary_op_schema (τ₁,SqlDate) (τ₂,SqlDateInterval) SqlDate
  | bop_sql_date_minus => enforce_binary_op_schema (τ₁,SqlDate) (τ₂,SqlDateInterval) SqlDate
  | bop_sql_date_ne
  | bop_sql_date_lt
  | bop_sql_date_le
  | bop_sql_date_gt
  | bop_sql_date_ge =>
    enforce_binary_op_schema (τ₁,SqlDate) (τ₂,SqlDate) Bool
  | bop_sql_date_interval_between  =>
    enforce_binary_op_schema (τ₁,SqlDate) (τ₂,SqlDate) SqlDateInterval
  | bop_sql_date_set_component part =>
    enforce_binary_op_schema (τ₁,SqlDate) (τ₂,Nat) SqlDate
  end.

Inductive enhanced_binary_op_has_type {model:brand_model} :
  enhanced_binary_op -> rtype -> rtype -> rtype -> Prop
  :=
  | tenhanced_binary_sql_date_op fb τin₁ τin₂ τout:
      sql_date_binary_op_has_type fb τin₁ τin₂ τout ->
      enhanced_binary_op_has_type (enhanced_binary_sql_date_op fb) τin₁ τin₂ τout.

Definition enhanced_binary_op_typing_infer {model:brand_model} (op:enhanced_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | enhanced_binary_sql_date_op fb => sql_date_binary_op_type_infer fb τ₁ τ₂
  end.

Lemma enhanced_binary_op_typing_infer_correct
      {model:brand_model}
      (fb:foreign_operators_binary)
      {τ₁ τ₂ τout} :
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = Some τout ->
  enhanced_binary_op_has_type fb τ₁ τ₂ τout.
Proof.
  intros.
  destruct fb; simpl.
  - destruct s; simpl in *;
      destruct τ₁; destruct τ₂; simpl in *; try discriminate;
        unfold isSqlDate, isSqlDateInterval, isNat in *
        ; destruct x; simpl in H; try discriminate
        ; destruct ft; simpl in H; try discriminate
        ; destruct x0; simpl in H; try discriminate
        ; try (destruct ft; simpl in H; try discriminate)
        ; invcs H
        ; constructor
        ; repeat rewrite Nat_canon
        ; repeat rewrite Foreign_canon
        ; constructor.
Qed.

Lemma enhanced_binary_op_typing_infer_least
      {model:brand_model}
      (fb:foreign_operators_binary)
      {τ₁ τ₂ τout₁ τout₂} : 
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = Some τout₁ ->
  enhanced_binary_op_has_type fb τ₁ τ₂ τout₂ ->
  τout₁ ≤ τout₂.
Proof.
  intros.
  destruct fb; simpl.
  - destruct s; simpl in *;
      destruct τ₁; destruct τ₂; simpl in *; try discriminate
      ; unfold isSqlDate, isSqlDateInterval, isNat in *
      ; destruct x; simpl in H; try discriminate
      ; destruct ft; simpl in H; try discriminate
      ; destruct x0; simpl in H; try discriminate
      ; try (destruct ft; simpl in H; try discriminate)
      ; invcs H
      ; repeat rewrite Foreign_canon in H0
      ; invcs H0
      ; invcs H1
      ; reflexivity.
Qed.

Lemma enhanced_binary_op_typing_infer_complete
      {model:brand_model}
      (fb:foreign_operators_binary)
      {τ₁ τ₂ τout} : 
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = None ->
  ~ enhanced_binary_op_has_type fb τ₁ τ₂ τout.
Proof.
  destruct fb; simpl; intros.
  - intro HH; invcs HH.
    destruct s; simpl in *; invcs H1; simpl in H; try discriminate.
Qed.

Definition enhanced_binary_op_typing_infer_sub {model:brand_model} (op:enhanced_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | enhanced_binary_sql_date_op fb => sql_date_binary_op_type_infer_sub fb τ₁ τ₂
  end.

Lemma enhanced_binary_op_typing_sound {model : brand_model}
      (fu : foreign_operators_binary) (τin₁ τin₂ τout : rtype) :
  enhanced_binary_op_has_type fu τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      enhanced_binary_op_interp brand_relation_brands fu din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
  intros.
  destruct H.
  - eapply sql_date_binary_op_typing_sound; eauto.
Qed.

Instance enhanced_foreign_operators_typing
         {model:brand_model} :
  @foreign_operators_typing
    enhanced_foreign_data
    enhanced_foreign_operators
    enhanced_foreign_type
    enhanced_foreign_data_typing
    model
  := { foreign_operators_typing_unary_has_type := enhanced_unary_op_has_type
       ; foreign_operators_typing_unary_sound := enhanced_unary_op_typing_sound
       ; foreign_operators_typing_unary_infer := enhanced_unary_op_typing_infer
       ; foreign_operators_typing_unary_infer_correct := enhanced_unary_op_typing_infer_correct
       ; foreign_operators_typing_unary_infer_least := enhanced_unary_op_typing_infer_least
       ; foreign_operators_typing_unary_infer_complete := enhanced_unary_op_typing_infer_complete
       ; foreign_operators_typing_unary_infer_sub := enhanced_unary_op_typing_infer_sub
       ; foreign_operators_typing_binary_has_type := enhanced_binary_op_has_type
       ; foreign_operators_typing_binary_sound := enhanced_binary_op_typing_sound
       ; foreign_operators_typing_binary_infer := enhanced_binary_op_typing_infer
       ; foreign_operators_typing_binary_infer_correct := enhanced_binary_op_typing_infer_correct
       ; foreign_operators_typing_binary_infer_least := enhanced_binary_op_typing_infer_least
       ; foreign_operators_typing_binary_infer_complete := enhanced_binary_op_typing_infer_complete
       ; foreign_operators_typing_binary_infer_sub := enhanced_binary_op_typing_infer_sub
     }.

Instance enhanced_foreign_typing {model:brand_model}:
  @foreign_typing
    enhanced_foreign_runtime
    enhanced_foreign_type
    model
  := mk_foreign_typing
       enhanced_foreign_runtime
       enhanced_foreign_type
       model
       enhanced_foreign_data_typing
       enhanced_foreign_operators_typing.

Instance enhanced_basic_model {model:brand_model} :
  basic_model
  := mk_basic_model
       enhanced_foreign_runtime
       enhanced_foreign_type
       model
       enhanced_foreign_typing.

Module EnhancedForeignType <: CompilerForeignType.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
End EnhancedForeignType.

Module EnhancedModel(bm:CompilerBrandModel(EnhancedForeignType)) <: CompilerModel.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
  Definition compiler_basic_model : @basic_model
    := @enhanced_basic_model bm.compiler_brand_model.
  Definition compiler_model_foreign_runtime : foreign_runtime
    := enhanced_foreign_runtime.
  Definition compiler_model_foreign_ejson : foreign_ejson
    := enhanced_foreign_ejson.
  Definition compiler_model_foreign_to_ejson : foreign_to_ejson
    := enhanced_foreign_to_ejson.
  Definition compiler_model_foreign_to_ejson_runtime : foreign_to_ejson_runtime
    := enhanced_foreign_to_ejson_runtime.
  Definition compiler_model_foreign_to_json : foreign_to_json
    := enhanced_foreign_to_json.
  Definition compiler_model_foreign_to_java : foreign_to_java
    := enhanced_foreign_to_java.
  Definition compiler_model_foreign_ejson_to_ajavascript : foreign_ejson_to_ajavascript
    := enhanced_foreign_ejson_to_ajavascript.
  Definition compiler_model_foreign_to_scala : foreign_to_scala
    := enhanced_foreign_to_scala.
  Definition compiler_model_foreign_type_to_JSON : foreign_type_to_JSON
    := enhanced_foreign_type_to_JSON.
  Definition compiler_model_foreign_reduce_op : foreign_reduce_op
    := enhanced_foreign_reduce_op.
  Definition compiler_model_foreign_to_reduce_op : foreign_to_reduce_op
    := enhanced_foreign_to_reduce_op.
  Definition compiler_model_foreign_to_spark : foreign_to_spark
    := enhanced_foreign_to_spark.
  Definition compiler_model_nraenv_optimizer_logger : optimizer_logger string nraenv
    := foreign_nraenv_optimizer_logger.
  Definition compiler_model_nnrc_optimizer_logger : optimizer_logger string nnrc
    := foreign_nnrc_optimizer_logger.
  Definition compiler_model_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr
    := foreign_nnrs_imp_expr_optimizer_logger.
  Definition compiler_model_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt
    := foreign_nnrs_imp_stmt_optimizer_logger.
  Definition compiler_model_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp
    := foreign_nnrs_imp_optimizer_logger.
  Definition compiler_model_dnnrc_optimizer_logger {br:brand_relation}: optimizer_logger string (@dnnrc_base _ (type_annotation unit) dataframe)
    := foreign_dnnrc_optimizer_logger.
  Definition compiler_model_foreign_data_typing : foreign_data_typing
    := enhanced_foreign_data_typing.
End EnhancedModel.

Module CompEnhanced.
  Module Enhanced.
    Module Model.
      Definition basic_model (bm:brand_model) : basic_model
        := @enhanced_basic_model bm.

      Definition foreign_type : foreign_type
        := enhanced_foreign_type.

      Definition foreign_typing (bm:brand_model) : foreign_typing
        := @enhanced_foreign_typing bm.

    End Model.

    Module Data.
      Definition sql_date_part := sql_date_component.
      Definition sql_date_day : sql_date_part := sql_date_DAY.
      Definition sql_date_month : sql_date_part := sql_date_MONTH.
      Definition sql_date_year : sql_date_part := sql_date_YEAR.

      Definition dsql_date (d:SQL_DATE) : data
        := dforeign (enhancedsqldate d).

      Definition dsql_date_interval (d:SQL_DATE_INTERVAL) : data
        := dforeign (enhancedsqldateinterval d).

    End Data.

    Module Ops.
      Module Unary.
        Definition sql_date_get_component (component:sql_date_component)
          := OpForeignUnary (enhanced_unary_sql_date_op (uop_sql_date_get_component component)).
        Definition sql_date_from_string
          := OpForeignUnary (enhanced_unary_sql_date_op uop_sql_date_from_string).
        Definition sql_date_interval_from_string
          := OpForeignUnary (enhanced_unary_sql_date_op uop_sql_date_interval_from_string).

        (* for coq style syntax *)
        Definition OpSqlGetDateComponent := sql_date_get_component.
        Definition OpSqlDateFromString := sql_date_from_string.
        Definition OpSqlDateIntervalFromString := sql_date_interval_from_string.

      End Unary.

      Module Binary.
        (* for ocaml *)
        Definition sql_date_plus
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_plus).
        Definition sql_date_minus
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_minus).
        Definition sql_date_ne 
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_ne).
        Definition sql_date_lt 
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_lt).
        Definition sql_date_le 
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_le).
        Definition sql_date_gt 
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_gt).
        Definition sql_date_ge 
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_ge).

        Definition sql_date_interval_between 
          := OpForeignBinary (enhanced_binary_sql_date_op (bop_sql_date_interval_between)).
        Definition sql_date_set_component (component:sql_date_component)
          := OpForeignBinary (enhanced_binary_sql_date_op (bop_sql_date_set_component component)).
        
        (* for coq style syntax *)
        Definition OpSqlDatePlus := sql_date_plus.
        Definition OpSqlDateMinus := sql_date_minus.
        Definition OpSqlDateNe := sql_date_ne.
        Definition OpSqlDateLt := sql_date_lt.
        Definition OpSqlDateLe := sql_date_le.
        Definition OpSqlDateGt := sql_date_gt.
        Definition OpSqlDateGe := sql_date_ge.

        Definition OpSqlDateIntervalBetween := sql_date_interval_between.

      End Binary.
    End Ops.
  End Enhanced.
End CompEnhanced.  
