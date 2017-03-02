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
Require Import ZArith.
Require Import ForeignData ForeignOps.
Require Import EquivDec Equivalence.

(** Defines the foreign support for Floating point numbers.  
     Posits axioms for the basic data/operators, and 
     defines how they are extracted to ocaml (using helper functions
     defined in qcert/ocaml/...../Util.ml)
     *)

(** Defines the data model *)
Axiom FLOAT : Set.
Extract Constant FLOAT => "float".

Axiom FLOAT_eq : FLOAT -> FLOAT -> bool.
Extract Inlined Constant FLOAT_eq => "(fun x y -> x = y)".

Conjecture FLOAT_eq_correct :
  forall f1 f2, (FLOAT_eq f1 f2 = true <-> f1 = f2).

Axiom FLOAT_tostring : FLOAT -> String.string.
Extract Inlined Constant FLOAT_tostring => "(fun x -> Util.char_list_of_string (Util.qcert_string_of_float x))".

Program Instance float_foreign_data : foreign_data
  := {foreign_data_type := FLOAT}.
Next Obligation.
  intros x y.
  case_eq (FLOAT_eq x y); intros eqq.
  + left.
    f_equal.
    apply FLOAT_eq_correct in eqq.
    trivial.
  + right; intros eqq2.
    red in eqq2.
    apply FLOAT_eq_correct in eqq2. 
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
  exact (FLOAT_tostring f).
Defined.

(* Some constant floats *)
Axiom FLOAT_CONST0 : FLOAT.
Extract Inlined Constant FLOAT_CONST0 => "0.".

(** Defines additional operations on FLOATs *)
(** Unary operations *)

Axiom FLOAT_neg : FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_neg => "(fun x -> ~-. x)".

Axiom FLOAT_sqrt : FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_sqrt => "(fun x -> sqrt x)".

Axiom FLOAT_exp : FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_exp => "(fun x -> exp x)".

Axiom FLOAT_log : FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_log => "(fun x -> log x)".

Axiom FLOAT_log10 : FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_log10 => "(fun x -> log10 x)".

Axiom FLOAT_of_int : Z -> FLOAT.
Extract Inlined Constant FLOAT_of_int => "(fun x -> float_of_int x)".

Axiom FLOAT_ceil : FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_ceil => "(fun x -> ceil x)".

Axiom FLOAT_floor : FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_floor => "(fun x -> floor x)".

Axiom FLOAT_truncate : FLOAT -> Z.
Extract Inlined Constant FLOAT_truncate=> "(fun x -> truncate x)".

Axiom FLOAT_abs : FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_abs => "(fun x -> abs_float x)".

Axiom FLOAT_sum : list FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_sum => "(fun x -> Util.float_sum x)".

Axiom FLOAT_arithmean : list FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_arithmean => "(fun x -> Util.float_arithmean x)".

Axiom FLOAT_listmin : list FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_listmin => "(fun x -> Util.float_listmin x)".

Axiom FLOAT_listmax : list FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_listmax => "(fun x -> Util.float_listmax x)".

Inductive float_unary_op
  :=
  | uop_float_neg
  | uop_float_sqrt
  | uop_float_exp
  | uop_float_log
  | uop_float_log10
  | uop_float_of_int
  | uop_float_ceil
  | uop_float_floor
  | uop_float_truncate
  | uop_float_abs
  | uop_float_sum
  | uop_float_arithmean
  | uop_float_listmin
  | uop_float_listmax
.

Local Open Scope string_scope.

Definition float_unary_op_tostring (f:float_unary_op) : String.string
  := match f with
         | uop_float_neg => "AFloatNeg"
         | uop_float_sqrt => "AFloatSqrt"
         | uop_float_exp => "AFloatExp"
         | uop_float_log => "AFloatLog"
         | uop_float_log10 => "AFloatLog10"
         | uop_float_of_int => "AFloatOfInt"
         | uop_float_ceil => "AFloatCeil"
         | uop_float_floor => "AFloatFloor"
         | uop_float_truncate => "AFloatTruncate"
         | uop_float_abs => "AFloatAbs"
         | uop_float_sum => "AFloatSum"
         | uop_float_arithmean => "AFloatArithMean"
         | uop_float_listmin => "AFloatListMin"
         | uop_float_listmax => "AFloatListMax"
     end.

Definition float_to_javascript_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:float_unary_op)
             (d:String.string) : String.string
  := match fu with
     | uop_float_neg => "-" ++ "(" ++ d ++ ")"
     | uop_float_sqrt =>"Math.sqrt(" ++ "-" ++ d ++ ")"
     | uop_float_exp => "Math.exp(" ++ d ++ ")" 
     | uop_float_log => "Math.log2(" ++ d ++ ")"
     | uop_float_log10 => "Math.log10(" ++ d ++ ")"
     | uop_float_of_int => d
     | uop_float_ceil => "Math.ceil(" ++ d ++ ")" 
     | uop_float_floor => "Math.floor(" ++ d ++ ")" 
     | uop_float_truncate => "Math.trunc(" ++ d ++ ")" 
     | uop_float_abs => "Math.abs(" ++ d ++ ")"
     | uop_float_sum => "sum(" ++ d ++ ")"
     | uop_float_arithmean => "arithMean(" ++ d ++ ")"
     | uop_float_listmin => "Math.min.apply(Math," ++ d ++ ")"
     | uop_float_listmax => "Math.max.apply(Math," ++ d ++ ")"
     end.

Definition float_to_scala_unary_op
           (op: float_unary_op) (d: string) : string :=
  match op with
    | uop_float_sum => d ++ ".sum"
    | _ => "Unsupported float unary op in FloatModelPart.float_to_scala_unary_op"
  end.

Require Import ForeignToJava NNRCtoJava.

Definition float_to_java_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:float_unary_op)
             (d:java_json) : java_json
  := match fu with
     | uop_float_neg => mk_java_unary_op0 "float_neg" d
     | uop_float_sqrt =>mk_java_unary_op0 "float_sqrt" d
     | uop_float_exp => mk_java_unary_op0 "float_exp" d
     | uop_float_log => mk_java_unary_op0 "float_log" d
     | uop_float_log10 => mk_java_unary_op0 "float_log10" d
     | uop_float_of_int =>mk_java_unary_op0 "float_of_int" d
     | uop_float_ceil => mk_java_unary_op0 "float_ceil" d
     | uop_float_floor => mk_java_unary_op0 "float_floor" d
     | uop_float_truncate =>mk_java_unary_op0 "float_truncate" d
     | uop_float_abs => mk_java_unary_op0 "float_abs" d
     | uop_float_sum =>mk_java_unary_op0 "float_sum" d
     | uop_float_arithmean => mk_java_unary_op0 "float_list_mean" d
     | uop_float_listmin => mk_java_unary_op0 "float_list_min" d
     | uop_float_listmax => mk_java_unary_op0 "float_list_max" d
     end.

  
(** Binary operations *)
Axiom FLOAT_plus : FLOAT -> FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_plus => "(fun x y -> x +. y)".

Axiom FLOAT_minus : FLOAT -> FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_minus => "(fun x y -> x -. y)".

Axiom FLOAT_mult : FLOAT -> FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_mult => "(fun x y -> x *. y)".

Axiom FLOAT_div : FLOAT -> FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_div => "(fun x y -> x /. y)".

Axiom FLOAT_pow : FLOAT -> FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_pow => "(fun x y -> x ** y)".

Axiom FLOAT_min : FLOAT -> FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_min => "(fun x y -> min x y)".

Axiom FLOAT_max : FLOAT -> FLOAT -> FLOAT.
Extract Inlined Constant FLOAT_max => "(fun x y -> max x y)".

Axiom FLOAT_ne : FLOAT -> FLOAT -> bool.
Extract Inlined Constant FLOAT_ne => "(fun x y -> x <> y)".

Axiom FLOAT_lt : FLOAT -> FLOAT -> bool.
Extract Inlined Constant FLOAT_lt => "(fun x y -> x < y)".

Axiom FLOAT_le : FLOAT -> FLOAT -> bool.
Extract Inlined Constant FLOAT_le => "(fun x y -> x <= y)".

Axiom FLOAT_gt : FLOAT -> FLOAT -> bool.
Extract Inlined Constant FLOAT_gt => "(fun x y -> x > y)".

Axiom FLOAT_ge : FLOAT -> FLOAT -> bool.
Extract Inlined Constant FLOAT_ge => "(fun x y -> x >= y)".

Inductive float_binary_op
  := 
  | bop_float_plus
  | bop_float_minus
  | bop_float_mult
  | bop_float_div
  | bop_float_pow
  | bop_float_min
  | bop_float_max
  | bop_float_ne
  | bop_float_lt
  | bop_float_le
  | bop_float_gt
  | bop_float_ge
.

Definition float_binary_op_tostring (f:float_binary_op) : String.string
  := match f with
     | bop_float_plus => "AFloatPlus"
     | bop_float_minus => "AFloatMinus"
     | bop_float_mult => "AFloatMult"
     | bop_float_div => "AFloatDiv"
     | bop_float_pow => "AFloatPow"
     | bop_float_min => "AFloatMin"
     | bop_float_max => "AFloatMax"
     | bop_float_ne => "AFloatNe"
     | bop_float_lt => "AFloatLt"
     | bop_float_le => "AFloatLe"
     | bop_float_gt => "AFloatGt"
     | bop_float_ge => "AFloatGe"
     end.

Definition float_to_javascript_binary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fb:float_binary_op)
             (d1 d2:String.string) : String.string
  := match fb with
     | bop_float_plus => "(" ++ d1 ++ ") + (" ++ d2 ++ ")"
     | bop_float_minus =>  "(" ++ d1 ++ ") - (" ++ d2 ++ ")"
     | bop_float_mult =>  "(" ++ d1 ++ ") * (" ++ d2 ++ ")"
     | bop_float_div =>  "(" ++ d1 ++ ") / (" ++ d2 ++ ")"
     | bop_float_pow => "Math.pow(" ++ d1 ++ ", " ++ d2 ++ ")"
     | bop_float_min => "Math.min(" ++ d1 ++ ", " ++ d2 ++ ")"
     | bop_float_max => "Math.max(" ++ d1 ++ ", " ++ d2 ++ ")"
     | bop_float_ne => "(" ++ d1 ++ ") != (" ++ d2 ++ ")"
     | bop_float_lt =>"(" ++ d1 ++ ") < (" ++ d2 ++ ")"
     | bop_float_le =>"(" ++ d1 ++ ") <= (" ++ d2 ++ ")"
     | bop_float_gt =>"(" ++ d1 ++ ") > (" ++ d2 ++ ")"
     | bop_float_ge => "(" ++ d1 ++ ") >= (" ++ d2 ++ ")"
     end.

Definition float_to_java_binary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fb:float_binary_op)
             (d1 d2:java_json) : java_json
  := match fb with
     | bop_float_plus => mk_java_binary_op0 "float_plus" d1 d2
     | bop_float_minus => mk_java_binary_op0 "float_minus" d1 d2
     | bop_float_mult =>  mk_java_binary_op0 "float_mult" d1 d2
     | bop_float_div => mk_java_binary_op0 "float_divide" d1 d2
     | bop_float_pow => mk_java_binary_op0 "float_pow" d1 d2
     | bop_float_min => mk_java_binary_op0 "float_min" d1 d2
     | bop_float_max => mk_java_binary_op0 "float_max" d1 d2
     | bop_float_ne => mk_java_binary_op0 "float_ne" d1 d2
     | bop_float_lt => mk_java_binary_op0 "float_lt" d1 d2
     | bop_float_le => mk_java_binary_op0 "float_le" d1 d2
     | bop_float_gt => mk_java_binary_op0 "float_gt" d1 d2
     | bop_float_ge => mk_java_binary_op0 "float_ge" d1 d2
     end.
  
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
