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
Require Import JSONSystem.
Require Import EJsonSystem.
Require Import ForeignData.
Require Import ForeignEJson.
Require Import SqlDateComponent.

Require Import EnhancedData.

Import ListNotations.
Local Open Scope list_scope.

Definition enhanced_ejson : Set := enhanced_data.

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

