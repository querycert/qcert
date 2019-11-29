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

Require Import String.
Require Import List.
Require Import ZArith.
Require Import EquivDec.
Require Import Equivalence.
Require Import Utils.
Require Import ForeignData.
Require Import ForeignOperators.
Require Import JavaScriptAstRuntime.

Import ListNotations.

(*********  <WARNING>*********************)
(** Extraction to OCaml is currently a stub **)
(********* </WARNING> ********************)


(** Defines the foreign support for date/time numbers
     Posits axioms for the basic data/operators, and 
     defines how they are extracted to ocaml (using helper functions
     defined in qcert/ocaml/...../Util.ml)
     *)

(** Defines the notion of a time scale *)
Inductive time_scale
  := ts_second
   | ts_minute
   | ts_hour
   | ts_day
   | ts_week
   | ts_month
   | ts_year.

Instance time_scale_eqdec : EqDec time_scale eq.
Proof.
  red; unfold equiv, complement.
  change (forall x y : time_scale, {x = y} + {x <> y}).
  decide equality.
Defined.


Definition time_scale_to_string
           (ts:time_scale) : string
  := match ts with
     | ts_second => "SECOND"%string
     | ts_minute => "MINUTE"%string
     | ts_hour => "HOUR"%string
     | ts_day => "DAY"%string
     | ts_week => "WEEK"%string
     | ts_month => "MONTH"%string
     | ts_year => "YEAR"%string
     end.

Instance time_scale_tostring : ToString time_scale
  := { toString := time_scale_to_string }.

Definition time_scale_to_java_string
           (ts:time_scale) : string
  := "TimeScale." ++ time_scale_to_string ts.
    
Program Instance time_scale_foreign_data : foreign_data
  := {foreign_data_type := time_scale
      ; foreign_data_dec := time_scale_eqdec
      ; foreign_data_tostring := time_scale_tostring
      ; foreign_data_normalized ts := True
      ; foreign_data_normalize ts := ts
     }.

(* Now we define a DurationValue.  Unlike time_scale, this is done via axioms *)

Axiom TIME_DURATION : Set.
Extract Constant TIME_DURATION => "string".

Axiom TIME_DURATION_eq : TIME_DURATION -> TIME_DURATION -> bool.
Extract Inlined Constant TIME_DURATION_eq => "(fun x y -> x = y)".

Conjecture TIME_DURATION_eq_correct :
  forall f1 f2, (TIME_DURATION_eq f1 f2 = true <-> f1 = f2).

Axiom TIME_DURATION_tostring : TIME_DURATION -> String.string.
Extract Inlined Constant TIME_DURATION_tostring => "(fun x -> Util.char_list_of_string x)".

Program Instance time_duration_foreign_data : foreign_data
  := {foreign_data_type := TIME_DURATION}.
Next Obligation.
  intros x y.
  case_eq (TIME_DURATION_eq x y); intros eqq.
  + left.
    f_equal.
    apply TIME_DURATION_eq_correct in eqq.
    trivial.
  + right; intros eqq2.
    red in eqq2.
    apply TIME_DURATION_eq_correct in eqq2. 
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
  exact (TIME_DURATION_tostring f).
Defined.

(* Now we define a TimePoint.  Unlike time_scale, this is done via axioms *)

Axiom TIME_POINT : Set.
Extract Constant TIME_POINT => "string".

Axiom TIME_POINT_eq : TIME_POINT -> TIME_POINT -> bool.
Extract Inlined Constant TIME_POINT_eq => "(fun x y -> x = y)".

Conjecture TIME_POINT_eq_correct :
  forall f1 f2, (TIME_POINT_eq f1 f2 = true <-> f1 = f2).

Axiom TIME_POINT_tostring : TIME_POINT -> String.string.
Extract Inlined Constant TIME_POINT_tostring => "(fun x -> Util.char_list_of_string x)".

Program Instance time_point_foreign_data : foreign_data
  := {foreign_data_type := TIME_POINT}.
Next Obligation.
  intros x y.
  case_eq (TIME_POINT_eq x y); intros eqq.
  + left.
    f_equal.
    apply TIME_POINT_eq_correct in eqq.
    trivial.
  + right; intros eqq2.
    red in eqq2.
    apply TIME_POINT_eq_correct in eqq2. 
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
  exact (TIME_POINT_tostring f).
Defined.

Axiom TIME_POINT_from_string : String.string -> TIME_POINT.
Extract Inlined Constant TIME_POINT_from_string => "(fun x -> Util.string_of_char_list x)".

Axiom TIME_DURATION_from_string : String.string -> TIME_DURATION.
Extract Inlined Constant TIME_DURATION_from_string => "(fun x -> Util.string_of_char_list x)".

Axiom TIME_POINT_to_scale : TIME_POINT -> time_scale.
Extract Inlined Constant TIME_POINT_to_scale => "(fun x -> Ts_second)".

Inductive time_unary_op
  :=
  | uop_time_to_scale
  | uop_time_from_string
  | uop_time_duration_from_string
.

Local Open Scope string.

Definition time_unary_op_tostring (f:time_unary_op) : String.string
  := match f with
     | uop_time_to_scale => "ATimeToScale"
     | uop_time_from_string => "ATimeFromString"
     | uop_time_duration_from_string => "ATimeDurationFromString"
     end.


Require Import ForeignToJava NNRCtoJava.

Definition time_to_java_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:time_unary_op)
             (d:java_json) : java_json
  := match fu with
     | uop_time_to_scale => mk_java_unary_op0 "time_to_scale" d
     | uop_time_from_string => mk_java_unary_op0 "time_from_string" d
     | uop_time_duration_from_string => mk_java_unary_op0 "time_duration_from_string" d
     end.

(* XXX THOSE ARE MISSING IN THE RUNTIME? *)
Definition time_to_javascript_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:time_unary_op)
             (d:String.string) : String.string
  := match fu with
     | uop_time_to_scale => "timePointToScale(" ++ d ++ ")"
     | uop_time_from_string => "timeFromString(" ++ d ++ ")"
     | uop_time_duration_from_string => "timeDurationFromString(" ++ d ++ ")"
     end.

Definition time_to_ajavascript_unary_op
             (fu:time_unary_op)
             (e:JsSyntax.expr) : JsSyntax.expr
  := match fu with
     | uop_time_to_scale => call_runtime "timePointToScale" [ e ]
     | uop_time_from_string => call_runtime "timeFromString" [ e ]
     | uop_time_duration_from_string => call_runtime "timeDurationFromString" [ e ]
     end.

Axiom TIME_POINT_as : TIME_POINT -> time_scale -> TIME_POINT.
Extract Inlined Constant TIME_POINT_as => "(fun x y -> x)".

Axiom TIME_POINT_shift : TIME_POINT -> TIME_DURATION -> TIME_POINT.
Extract Inlined Constant TIME_POINT_shift => "(fun x y -> x)".

Axiom TIME_POINT_ne : TIME_POINT -> TIME_POINT -> bool.
Extract Inlined Constant TIME_POINT_ne => "(fun x y -> x <> y)".

Axiom TIME_POINT_lt : TIME_POINT -> TIME_POINT -> bool.
Extract Inlined Constant TIME_POINT_lt => "(fun x y -> x < y)".

Axiom TIME_POINT_le : TIME_POINT -> TIME_POINT -> bool.
Extract Inlined Constant TIME_POINT_le => "(fun x y -> x <= y)".

Axiom TIME_POINT_gt : TIME_POINT -> TIME_POINT -> bool.
Extract Inlined Constant TIME_POINT_gt => "(fun x y -> x > y)".

Axiom TIME_POINT_ge : TIME_POINT -> TIME_POINT -> bool.
Extract Inlined Constant TIME_POINT_ge => "(fun x y -> x >= y)".

Axiom TIME_DURATION_from_scale : time_scale -> Z -> TIME_DURATION.
Extract Inlined Constant TIME_DURATION_from_scale => "(fun x y -> """")".

Axiom TIME_DURATION_between : TIME_POINT -> TIME_POINT -> TIME_DURATION.
Extract Inlined Constant TIME_DURATION_between => "(fun x y -> """")".

Inductive time_binary_op
  :=
  | bop_time_as 
  | bop_time_shift
  | bop_time_ne
  | bop_time_lt
  | bop_time_le
  | bop_time_gt
  | bop_time_ge
  | bop_time_duration_from_scale
  | bop_time_duration_between
.

Definition time_binary_op_tostring (f:time_binary_op) : String.string
  := match f with
     | bop_time_as => "ATimeAs"
     | bop_time_shift => "ATimeShift"
     | bop_time_ne => "ATimeNe"
     | bop_time_lt => "ATimeLt"
     | bop_time_le => "ATimeLe"
     | bop_time_gt => "ATimeGt"
     | bop_time_ge => "ATimeGe"
     | bop_time_duration_from_scale => "ATimeDurationFromScale"
     | bop_time_duration_between => "ATimeDurationBetween"
     end.

(* Java equivalent: JavaScriptBackend.jsFunc *)
Definition jsFunc (name d1 d2:string)
  := name ++ "(" ++ d1 ++ ", " ++ d2 ++ ")".

Definition time_to_java_binary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fb:time_binary_op)
             (d1 d2:java_json) : java_json
  := match fb with
     | bop_time_as => mk_java_binary_op0 "time_point_as" d1 d2
     | bop_time_shift => mk_java_binary_op0 "time_point_shift" d1 d2
     | bop_time_ne =>  mk_java_binary_op0 "time_point_ne" d1 d2
     | bop_time_lt =>  mk_java_binary_op0 "time_point_lt" d1 d2
     | bop_time_le =>  mk_java_binary_op0 "time_point_le" d1 d2
     | bop_time_gt =>  mk_java_binary_op0 "time_point_gt" d1 d2
     | bop_time_ge => mk_java_binary_op0 "time_point_ge" d1 d2
     | bop_time_duration_from_scale => mk_java_binary_op0 "time_duration_from_scale" d1 d2
     | bop_time_duration_between => mk_java_binary_op0 "time_duration_between" d1 d2

     end.

Definition time_to_javascript_binary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fb:time_binary_op)
             (d1 d2:String.string) : String.string
  := match fb with
     | bop_time_as => jsFunc "timePointAs" d1 d2
     | bop_time_shift => jsFunc "timePointShift" d1 d2
     | bop_time_ne =>  jsFunc "timePointNe" d1 d2
     | bop_time_lt =>  jsFunc "timePointLt" d1 d2
     | bop_time_le =>  jsFunc "timePointLe" d1 d2
     | bop_time_gt =>  jsFunc "timePointGt" d1 d2
     | bop_time_ge => jsFunc "timePointGe" d1 d2
     | bop_time_duration_from_scale =>  jsFunc "timeDurationFromScale" d1 d2
     | bop_time_duration_between => jsFunc "timeDurationBetween" d1 d2
     end.  

Definition time_to_ajavascript_binary_op
             (fb:time_binary_op)
             (e1 e2:JsSyntax.expr) : JsSyntax.expr
  := match fb with
     | bop_time_as => call_runtime "timePointAs" [ e1; e2 ]
     | bop_time_shift => call_runtime "timePointShift" [ e1; e2 ]
     | bop_time_ne =>  call_runtime "timePointNe" [ e1; e2 ]
     | bop_time_lt =>  call_runtime "timePointLt" [ e1; e2 ]
     | bop_time_le =>  call_runtime "timePointLe" [ e1; e2 ]
     | bop_time_gt =>  call_runtime "timePointGt" [ e1; e2 ]
     | bop_time_ge => call_runtime "timePointGe" [ e1; e2 ]
     | bop_time_duration_from_scale =>  call_runtime "timeDurationFromScale" [ e1; e2 ]
     | bop_time_duration_between => call_runtime "timeDurationBetween" [ e1; e2 ]
     end.  

