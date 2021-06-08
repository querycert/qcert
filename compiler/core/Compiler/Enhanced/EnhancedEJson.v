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
Require Import ForeignData.
Require Import ForeignEJson.
Require Import SqlDateComponent.
Require Import UriComponent.

Require Import EnhancedData.

Import ListNotations.
Local Open Scope list_scope.

Definition enhanced_ejson : Set := enhanced_data.

Program Instance enhanced_foreign_ejson : foreign_ejson enhanced_ejson
  := mk_foreign_ejson enhanced_ejson _ _ _ _ _ _.
Next Obligation.
  red.
  unfold equiv, complement.
  destruct x; destruct y; simpl; try solve [right; inversion 1].
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec sql_date_foreign_data) s s0).
    + left; congruence.
    + right; congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec sql_date_period_foreign_data) s s0).
    + left; congruence.
    + right; congruence.
Defined.
Next Obligation.
  (* normalized? *)
  destruct a.
  - exact (@foreign_data_normalized sql_date_foreign_data s).
  - exact (@foreign_data_normalized sql_date_period_foreign_data s).
Defined.
Next Obligation.
  destruct a.
  - exact (@foreign_data_normalize_normalizes sql_date_foreign_data s).
  - exact (@foreign_data_normalize_normalizes sql_date_period_foreign_data s).
Defined.
Next Obligation.
  constructor.
  destruct 1.
  - exact (@toString _ (@foreign_data_tostring sql_date_foreign_data) s).
  - exact (@toString _ (@foreign_data_tostring sql_date_period_foreign_data) s).
Defined.

Inductive enhanced_foreign_ejson_runtime_op :=
| enhanced_ejson_sql_date : ejson_sql_date_runtime_op -> enhanced_foreign_ejson_runtime_op
| enhanced_ejson_uri : ejson_uri_runtime_op -> enhanced_foreign_ejson_runtime_op
.

Definition enhanced_foreign_ejson_runtime_op_tostring op : string :=
  match op with
  | enhanced_ejson_sql_date sop => ejson_sql_date_runtime_op_tostring sop
  | enhanced_ejson_uri sop => ejson_uri_runtime_op_tostring sop
  end.

Definition enhanced_foreign_ejson_runtime_op_fromstring opname : option enhanced_foreign_ejson_runtime_op :=
  match ejson_sql_date_runtime_op_fromstring opname with
  | Some op =>  Some (enhanced_ejson_sql_date op)
  | None =>
    match ejson_uri_runtime_op_fromstring opname with
    | Some op => Some (enhanced_ejson_uri op)
    | None => None
    end
  end.

Definition enhanced_ejson_sql_date_runtime_op_interp op (dl:list ejson) : option ejson :=
  match op with
  | EJsonRuntimeDateFromString =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejstring s => Some (ejforeign (enhancedsqldate (SQL_DATE_from_string s)))
         | _ => None
         end) dl
  | EJsonRuntimeDateGetYear =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhancedsqldate s) =>
           Some (ejbigint (SQL_DATE_get_year s))
         | _ => None
         end) dl
  | EJsonRuntimeDateGetMonth =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhancedsqldate fd) =>
           Some (ejbigint (SQL_DATE_get_month fd))
         | _ => None
         end) dl
  | EJsonRuntimeDateGetDay =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhancedsqldate fd) =>
           Some (ejbigint (SQL_DATE_get_day fd))
         | _ => None
         end) dl
  | EJsonRuntimeDateNe =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejbool (SQL_DATE_ne fd1 fd2))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateLt =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejbool (SQL_DATE_lt fd1 fd2))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateLe =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejbool (SQL_DATE_le fd1 fd2))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateGt =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejbool (SQL_DATE_gt fd1 fd2))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateGe =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejbool (SQL_DATE_ge fd1 fd2))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateSetYear =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd), ejbigint n =>
           Some (ejforeign (enhancedsqldate (SQL_DATE_set_year fd n)))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateSetMonth =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd), ejbigint n =>
           Some (ejforeign (enhancedsqldate (SQL_DATE_set_month fd n)))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateSetDay =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd), ejbigint n =>
           Some (ejforeign (enhancedsqldate (SQL_DATE_set_day fd n)))
         | _, _ => None
         end) dl
  | EJsonRuntimePeriodFromString =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejstring s => Some (ejforeign (enhancedsqldateperiod (SQL_DATE_PERIOD_from_string s)))
         | _ => None
         end) dl
  | EJsonRuntimePeriodPlus =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd), ejforeign (enhancedsqldateperiod id) =>
           Some (ejforeign (enhancedsqldate (SQL_DATE_plus fd id)))
         | _, _ => None
         end) dl
  | EJsonRuntimePeriodMinus =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd), ejforeign (enhancedsqldateperiod id) =>
           Some (ejforeign (enhancedsqldate (SQL_DATE_minus fd id)))
         | _, _ => None
         end) dl
  | EJsonRuntimePeriodBetween =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhancedsqldate fd1), ejforeign (enhancedsqldate fd2) =>
           Some (ejforeign (enhancedsqldateperiod (SQL_DATE_PERIOD_between fd1 fd2)))
         | _, _ => None
         end) dl
  end.

Definition enhanced_ejson_uri_runtime_op_interp op (dl:list (@ejson enhanced_ejson)) : option ejson :=
  match op with
  | EJsonRuntimeUriEncode =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejstring s => Some (ejstring (URI_encode s))
         | _ => None
         end) dl
  | EJsonRuntimeUriDecode =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejstring s => Some (ejstring (URI_decode s))
         | _ => None
         end) dl
  end.

Definition enhanced_foreign_ejson_runtime_op_interp op :=
  match op with
  | enhanced_ejson_sql_date sop =>
    enhanced_ejson_sql_date_runtime_op_interp sop
  | enhanced_ejson_uri sop =>
    enhanced_ejson_uri_runtime_op_interp sop
  end.

Program Instance enhanced_foreign_ejson_runtime : foreign_ejson_runtime _ :=
  mk_foreign_ejson_runtime enhanced_foreign_ejson_runtime_op enhanced_ejson enhanced_foreign_ejson _ _ _ _ _ _.
Next Obligation.
  red; unfold equiv; intros.
  change ({x = y} + {x <> y}).
  decide equality.
  decide equality.
  decide equality.
Defined.
Next Obligation.
  constructor; intros op.
  exact (enhanced_foreign_ejson_runtime_op_tostring op).
Defined.
Next Obligation.
  exact (enhanced_foreign_ejson_runtime_op_interp f dl).
Defined.
Next Obligation.
  exact (defaultEJsonToString H).
Defined.
Next Obligation.
  exact (enhanced_foreign_ejson_runtime_op_fromstring H).
Defined.  
Next Obligation.
  exact (defaultEJsonToString H).
Defined.
