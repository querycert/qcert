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
Require Import ForeignData.
Require Import ForeignToJava.
Require Import NNRCtoJava.
Require Import ForeignOperators.
Require Import JavaScriptAstRuntime.

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
(* DATE_INTERVAL *)
Axiom SQL_DATE_INTERVAL : Set.
Extract Constant SQL_DATE_INTERVAL => "string".

Axiom SQL_DATE_INTERVAL_eq : SQL_DATE_INTERVAL -> SQL_DATE_INTERVAL -> bool.
Extract Inlined Constant SQL_DATE_INTERVAL_eq => "(fun x y -> x = y)".

Conjecture SQL_DATE_INTERVAL_eq_correct :
  forall f1 f2, (SQL_DATE_INTERVAL_eq f1 f2 = true <-> f1 = f2).

Axiom SQL_DATE_INTERVAL_to_string : SQL_DATE_INTERVAL -> String.string.
Extract Inlined Constant SQL_DATE_INTERVAL_to_string => "(fun x -> Util.char_list_of_string x)".

Axiom SQL_DATE_INTERVAL_from_string : String.string -> SQL_DATE_INTERVAL.
Extract Inlined Constant SQL_DATE_INTERVAL_from_string => "(fun x -> Util.string_of_char_list x)".

Axiom SQL_DATE_INTERVAL_from_string_correct :
  forall s, SQL_DATE_INTERVAL_from_string (SQL_DATE_INTERVAL_to_string s) = s.

(* DATE *)
Axiom SQL_DATE : Set.
Extract Constant SQL_DATE => "string".

Axiom SQL_DATE_eq : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_eq => "(fun x y -> x = y)".

Conjecture SQL_DATE_eq_correct :
  forall f1 f2, (SQL_DATE_eq f1 f2 = true <-> f1 = f2).

Axiom SQL_DATE_to_string : SQL_DATE -> String.string.
Extract Inlined Constant SQL_DATE_to_string => "(fun x -> Util.char_list_of_string x)".

Axiom SQL_DATE_from_string : String.string -> SQL_DATE.
Extract Inlined Constant SQL_DATE_from_string => "(fun x -> Util.string_of_char_list x)".

Axiom SQL_DATE_from_string_correct :
  forall s, SQL_DATE_from_string (SQL_DATE_to_string s) = s.

(* Operators *)
Inductive sql_date_component :=
| sql_date_DAY
| sql_date_MONTH
| sql_date_YEAR.

Axiom SQL_DATE_get_component : sql_date_component -> SQL_DATE -> Z.
Extract Inlined Constant SQL_DATE_get_component => "(fun x y -> 0)".

Axiom SQL_DATE_set_component : sql_date_component -> SQL_DATE -> Z -> SQL_DATE.
Extract Inlined Constant SQL_DATE_set_component => "(fun x y z -> y)".
  
Axiom SQL_DATE_plus : SQL_DATE -> SQL_DATE_INTERVAL -> SQL_DATE.
Extract Inlined Constant SQL_DATE_plus => "(fun x y -> x)".

Axiom SQL_DATE_minus : SQL_DATE -> SQL_DATE_INTERVAL -> SQL_DATE.
Extract Inlined Constant SQL_DATE_minus => "(fun x y -> x)".

Axiom SQL_DATE_ne : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_ne => "(fun x y -> x <> y)".

Axiom SQL_DATE_lt : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_lt => "(fun x y -> x < y)".

Axiom SQL_DATE_le : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_le => "(fun x y -> x <= y)".

Axiom SQL_DATE_gt : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_gt => "(fun x y -> x > y)".

Axiom SQL_DATE_ge : SQL_DATE -> SQL_DATE -> bool.
Extract Inlined Constant SQL_DATE_ge => "(fun x y -> x >= y)".

Axiom SQL_DATE_INTERVAL_between : SQL_DATE -> SQL_DATE -> SQL_DATE_INTERVAL.
Extract Inlined Constant SQL_DATE_INTERVAL_between => "(fun x y -> """")".

Section SqlDateModel.
  (** Equality *)
  Section Equality.
    Program Instance sql_date_interval_foreign_data : foreign_data
      := {foreign_data_model := SQL_DATE_INTERVAL}.
    Next Obligation.
      intros x y.
      case_eq (SQL_DATE_INTERVAL_eq x y); intros eqq.
      + left.
        f_equal.
        apply SQL_DATE_INTERVAL_eq_correct in eqq.
        trivial.
      + right; intros eqq2.
        red in eqq2.
        apply SQL_DATE_INTERVAL_eq_correct in eqq2. 
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
      exact (SQL_DATE_INTERVAL_to_string f).
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
  | uop_sql_date_interval_from_string
  .

  Inductive sql_date_binary_op :=
  | bop_sql_date_plus
  | bop_sql_date_minus
  | bop_sql_date_ne
  | bop_sql_date_lt
  | bop_sql_date_le
  | bop_sql_date_gt
  | bop_sql_date_ge
  | bop_sql_date_interval_between
  | bop_sql_date_set_component : sql_date_component -> sql_date_binary_op
  .
    
  Section toString.
    Definition sql_date_unary_op_tostring (f:sql_date_unary_op) : String.string :=
      match f with
      | uop_sql_date_get_component part => "(ASqlGetDateComponent" ++ (sql_date_component_tostring part) ++ ")"
      | uop_sql_date_from_string => "ASqlDateFromString"
      | uop_sql_date_interval_from_string => "ASqlDateDurationFromString"
      end.
  End toString.

  Section toJava.
    Definition sql_date_component_to_java_string (part:sql_date_component): string :=
      match part with
      | sql_date_DAY => "UnaryOperators.DAY"
      | sql_date_MONTH => "UnaryOperators.MONTH"
      | sql_date_YEAR => "UnaryOperators.YEAR"
      end.

    Definition sql_date_to_java_unary_op
               (indent:nat) (eol:nstring)
               (quotel:nstring) (fu:sql_date_unary_op)
               (d:java_json) : java_json :=
      match fu with
      | uop_sql_date_get_component part =>
        mk_java_unary_op1 (^"sql_date_get_component") (^sql_date_component_to_java_string part) d
      | uop_sql_date_from_string => mk_java_unary_op0 (^"sql_date_from_string") d
      | uop_sql_date_interval_from_string => mk_java_unary_op0 (^"sql_date_interval_from_string") d
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
      | bop_sql_date_interval_between => "ASqlDateDurationBetween"
      | bop_sql_date_set_component part => "(ASqlSetDateComponent" ++ (sql_date_component_tostring part) ++ ")"
      end.

    Definition sql_date_to_java_binary_op
               (indent:nat) (eol:nstring)
               (quotel:nstring) (fb:sql_date_binary_op)
               (d1 d2:java_json) : java_json :=
      match fb with
      | bop_sql_date_plus => mk_java_binary_op0 (^"sql_date_plus") d1 d2
      | bop_sql_date_minus => mk_java_binary_op0 (^"sql_date_minus") d1 d2
      | bop_sql_date_ne =>  mk_java_binary_op0 (^"sql_date_ne") d1 d2
      | bop_sql_date_lt =>  mk_java_binary_op0 (^"sql_date_lt") d1 d2
      | bop_sql_date_le =>  mk_java_binary_op0 (^"sql_date_le") d1 d2
      | bop_sql_date_gt =>  mk_java_binary_op0 (^"sql_date_gt") d1 d2
      | bop_sql_date_ge => mk_java_binary_op0 (^"sql_date_ge") d1 d2
      | bop_sql_date_interval_between => mk_java_binary_op0 (^"sql_date_interval_between") d1 d2
      | bop_sql_date_set_component part => mk_java_binary_op0 (^"sql_date_set_component") d1 d2
      end.

  End toJava.

End SqlDateOperators.
