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

Require Import String.
Require Import List.
Require Import ZArith.
Require Import EquivDec.
Require Import Equivalence.
Require Import Utils.
Require Import DataSystem.
Require Import ForeignToJava.
Require Import ForeignOperators.
Require Import JavaRuntime.

Import ListNotations.

(*********  <WARNING>*********************)
(** Extraction to OCaml is currently a stub **)
(********* </WARNING> ********************)

(** Defines the foreign support for sql dates
     Posits axioms for the basic data/operators, and 
     defines how they are extracted to ocaml (using helper functions
     defined in qcert/ocaml/...../Util.ml)
     *)

(** Axioms Section *)
(* DATE_PERIOD *)
Axiom SQL_DATE_PERIOD : Set.
Extract Constant SQL_DATE_PERIOD => "Sql_date_component.period".

Axiom SQL_DATE_PERIOD_eq : SQL_DATE_PERIOD -> SQL_DATE_PERIOD -> bool.
Extract Inlined Constant SQL_DATE_PERIOD_eq => "(fun x y -> Sql_date_component.period_eq x y)".

Conjecture SQL_DATE_PERIOD_eq_correct :
  forall f1 f2, (SQL_DATE_PERIOD_eq f1 f2 = true <-> f1 = f2).

Axiom SQL_DATE_PERIOD_to_string : SQL_DATE_PERIOD -> String.string.
Extract Inlined Constant SQL_DATE_PERIOD_to_string => "(fun x -> Sql_date_component.period_to_string x)".

Axiom SQL_DATE_PERIOD_from_string : String.string -> SQL_DATE_PERIOD.
Extract Inlined Constant SQL_DATE_PERIOD_from_string => "(fun x -> Sql_date_component.period_from_string x)".

(* DATE *)
Axiom SQL_DATE : Set.
Extract Constant SQL_DATE => "Sql_date_component.date".

Axiom SQL_DATE_eq : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_eq => "(fun x y -> Sql_date_component.date_eq x y)".

Conjecture SQL_DATE_eq_correct :
  forall f1 f2, (SQL_DATE_eq f1 f2 = true <-> f1 = f2).

Axiom SQL_DATE_to_string : SQL_DATE -> String.string.
Extract Inlined Constant SQL_DATE_to_string => "(fun x -> Sql_date_component.date_to_string x)".

Axiom SQL_DATE_from_string : String.string -> SQL_DATE.
Extract Inlined Constant SQL_DATE_from_string => "(fun x -> Sql_date_component.date_from_string x)".

(* Operators *)
Axiom SQL_DATE_ne : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_ne => "(fun x y -> Sql_date_component.date_neq x y)".

Axiom SQL_DATE_lt : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_lt => "(fun x y -> Sql_date_component.date_lt x y)".

Axiom SQL_DATE_le : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_le => "(fun x y -> Sql_date_component.date_le x y)".

Axiom SQL_DATE_gt : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_gt => "(fun x y -> Sql_date_component.date_gt x y)".

Axiom SQL_DATE_ge : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_ge => "(fun x y -> Sql_date_component.date_ge x y)".

Axiom SQL_DATE_get_year : SQL_DATE -> Z.
Extract Inlined Constant SQL_DATE_get_year => "(fun x -> Sql_date_component.get_year x)".

Axiom SQL_DATE_get_month : SQL_DATE -> Z.
Extract Inlined Constant SQL_DATE_get_month => "(fun x -> Sql_date_component.get_month x)".

Axiom SQL_DATE_get_day : SQL_DATE -> Z.
Extract Inlined Constant SQL_DATE_get_day => "(fun x -> Sql_date_component.get_day x)".

Axiom SQL_DATE_set_year : SQL_DATE -> Z  -> SQL_DATE.
Extract Inlined Constant SQL_DATE_set_year => "(fun x y -> Sql_date_component.set_year x y)".

Axiom SQL_DATE_set_month : SQL_DATE -> Z  -> SQL_DATE.
Extract Inlined Constant SQL_DATE_set_month => "(fun x y -> Sql_date_component.set_month x y)".

Axiom SQL_DATE_set_day : SQL_DATE -> Z  -> SQL_DATE.
Extract Inlined Constant SQL_DATE_set_day => "(fun x y -> Sql_date_component.set_day x y)".

Axiom SQL_DATE_plus : SQL_DATE -> SQL_DATE_PERIOD -> SQL_DATE.
Extract Inlined Constant SQL_DATE_plus => "(fun x y -> Sql_date_component.plus x y)".

Axiom SQL_DATE_minus : SQL_DATE -> SQL_DATE_PERIOD -> SQL_DATE.
Extract Inlined Constant SQL_DATE_minus => "(fun x y -> Sql_date_component.minus x y)".

Axiom SQL_DATE_PERIOD_between : SQL_DATE -> SQL_DATE -> SQL_DATE_PERIOD.
Extract Inlined Constant SQL_DATE_PERIOD_between => "(fun x y -> Sql_date_component.between x y)".

(* For serialization *)
Axiom SQL_DATE_from_parts : Z -> Z -> Z -> SQL_DATE.
Extract Inlined Constant SQL_DATE_from_parts => "(fun x y z -> Sql_date_component.date_from_parts x y z)".

Section SqlDateModel.
  Inductive sql_date_component :=
  | sql_date_DAY
  | sql_date_MONTH
  | sql_date_YEAR.

  (** Equality *)
  Section Equality.
    Program Instance sql_date_period_foreign_data : foreign_data
      := {foreign_data_model := SQL_DATE_PERIOD}.
    Next Obligation.
      intros x y.
      case_eq (SQL_DATE_PERIOD_eq x y); intros eqq.
      + left.
        f_equal.
        apply SQL_DATE_PERIOD_eq_correct in eqq.
        trivial.
      + right; intros eqq2.
        red in eqq2.
        apply SQL_DATE_PERIOD_eq_correct in eqq2. 
        congruence.
    Defined.
    Next Obligation.
      exact True.
    Defined.
    Next Obligation.
      reflexivity.
    Qed.
    Next Obligation.
      constructor.
      intros f.
      exact (SQL_DATE_PERIOD_to_string f).
    Defined.

    Program Instance sql_date_foreign_data : foreign_data
      := {foreign_data_model := SQL_DATE}.
    Next Obligation.
      intros x y.
      case_eq (SQL_DATE_eq x y); intros eqq.
      + left.
        f_equal.
        apply SQL_DATE_eq_correct in eqq.
        trivial.
      + right; intros eqq2.
        red in eqq2.
        apply SQL_DATE_eq_correct in eqq2. 
        congruence.
    Defined.
    Next Obligation.
      exact True.
    Defined.
    Next Obligation.
      reflexivity.
    Qed.
    Next Obligation.
      constructor.
      intros f.
      exact (SQL_DATE_to_string f).
    Defined.
  End Equality.

  Section toString.
    Definition sql_date_component_tostring (part:sql_date_component) : String.string :=
      match part with
      | sql_date_DAY => "DAY"
      | sql_date_MONTH => "MONTH"
      | sql_date_YEAR => "YEAR"
      end.

    Global Instance sql_date_component_to_string : ToString sql_date_component
      := { toString := sql_date_component_tostring }.
  End toString.

End SqlDateModel.

Section SqlDateOperators.
  Local Open Scope string.
  Local Open Scope nstring_scope.

  Inductive sql_date_unary_op :=
  | uop_sql_date_get_component : sql_date_component -> sql_date_unary_op
  | uop_sql_date_from_string
  | uop_sql_date_period_from_string
  .

  Inductive sql_date_binary_op :=
  | bop_sql_date_plus
  | bop_sql_date_minus
  | bop_sql_date_ne
  | bop_sql_date_lt
  | bop_sql_date_le
  | bop_sql_date_gt
  | bop_sql_date_ge
  | bop_sql_date_period_between
  | bop_sql_date_set_component : sql_date_component -> sql_date_binary_op
  .

  Section toString.
    Definition sql_date_unary_op_tostring (f:sql_date_unary_op) : String.string :=
      match f with
      | uop_sql_date_get_component part => "(ASqlGetDateComponent" ++ (sql_date_component_tostring part) ++ ")"
      | uop_sql_date_from_string => "ASqlDateFromString"
      | uop_sql_date_period_from_string => "ASqlDatePeriodFromString"
      end.

    Definition sql_date_binary_op_tostring (f:sql_date_binary_op) : String.string :=
      match f with
      | bop_sql_date_plus => "ASqlDatePlus"
      | bop_sql_date_minus => "ASqlDateMinus"
      | bop_sql_date_ne => "ASqlDateNe"
      | bop_sql_date_lt => "ASqlDateLt"
      | bop_sql_date_le => "ASqlDateLe"
      | bop_sql_date_gt => "ASqlDateGt"
      | bop_sql_date_ge => "ASqlDateGe"
      | bop_sql_date_period_between => "ASqlDatePeriodBetween"
      | bop_sql_date_set_component part => "(ASqlSetDateComponent" ++ (sql_date_component_tostring part) ++ ")"
      end.
  End toString.

  Section toJava.
    Definition cname : nstring := ^"SqlDateComponent".

    Definition sql_date_component_to_java_string (part:sql_date_component): nstring :=
      cname +++ ^"." +++ (^sql_date_component_tostring part).

    Definition sql_date_to_java_unary_op
               (indent:nat) (eol:nstring)
               (quotel:nstring) (fu:sql_date_unary_op)
               (d:java_json) : java_json :=
      match fu with
      | uop_sql_date_get_component part =>
        mk_java_unary_op1_foreign cname (^"sql_date_get_component") (sql_date_component_to_java_string part) d
      | uop_sql_date_from_string => mk_java_unary_op0_foreign cname (^"sql_date_from_string") d
      | uop_sql_date_period_from_string => mk_java_unary_op0_foreign cname (^"sql_date_period_from_string") d
      end.

    Definition sql_date_to_java_binary_op
               (indent:nat) (eol:nstring)
               (quotel:nstring) (fb:sql_date_binary_op)
               (d1 d2:java_json) : java_json :=
      match fb with
      | bop_sql_date_plus => mk_java_binary_op0_foreign cname (^"sql_date_plus") d1 d2
      | bop_sql_date_minus => mk_java_binary_op0_foreign cname (^"sql_date_minus") d1 d2
      | bop_sql_date_ne =>  mk_java_binary_op0_foreign cname (^"sql_date_ne") d1 d2
      | bop_sql_date_lt =>  mk_java_binary_op0_foreign cname (^"sql_date_lt") d1 d2
      | bop_sql_date_le =>  mk_java_binary_op0_foreign cname (^"sql_date_le") d1 d2
      | bop_sql_date_gt =>  mk_java_binary_op0_foreign cname (^"sql_date_gt") d1 d2
      | bop_sql_date_ge => mk_java_binary_op0_foreign cname (^"sql_date_ge") d1 d2
      | bop_sql_date_period_between => mk_java_binary_op0_foreign cname (^"sql_date_period_between") d1 d2
      | bop_sql_date_set_component part => mk_java_binary_opn_foreign cname (^"sql_date_set_component") [sql_date_component_to_java_string part] d1 d2
      end.

  End toJava.

  Section toEJson.
    Inductive ejson_sql_date_runtime_op :=
    | EJsonRuntimeDateFromString
    | EJsonRuntimeDateGetYear
    | EJsonRuntimeDateGetMonth
    | EJsonRuntimeDateGetDay
    | EJsonRuntimeDateNe
    | EJsonRuntimeDateLt
    | EJsonRuntimeDateLe
    | EJsonRuntimeDateGt
    | EJsonRuntimeDateGe
    | EJsonRuntimeDateSetYear
    | EJsonRuntimeDateSetMonth
    | EJsonRuntimeDateSetDay
    | EJsonRuntimePeriodFromString
    | EJsonRuntimePeriodPlus
    | EJsonRuntimePeriodMinus
    | EJsonRuntimePeriodBetween
    .

    Definition ejson_sql_date_runtime_op_tostring op : string :=
      match op with
      | EJsonRuntimeDateFromString => "dateFromString"
      | EJsonRuntimeDateGetYear => "dateGetYear"
      | EJsonRuntimeDateGetMonth => "dateGetMonth"
      | EJsonRuntimeDateGetDay => "dateGetDay"
      | EJsonRuntimeDateNe => "dateNe"
      | EJsonRuntimeDateLt => "dateLt"
      | EJsonRuntimeDateLe => "dateLe"
      | EJsonRuntimeDateGt => "dateGt"
      | EJsonRuntimeDateGe => "dateGe"
      | EJsonRuntimeDateSetYear => "dateSetYear"
      | EJsonRuntimeDateSetMonth => "dateSetMonth"
      | EJsonRuntimeDateSetDay => "dateSetDay"
      | EJsonRuntimePeriodFromString => "periodFromString"
      | EJsonRuntimePeriodPlus => "periodPlus"
      | EJsonRuntimePeriodMinus => "periodMinus"
      | EJsonRuntimePeriodBetween => "periodBetween"
      end.

  End toEJson.
End SqlDateOperators.
