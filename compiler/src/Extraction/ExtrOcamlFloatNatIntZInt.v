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

(** This module contains extraction code for definitions and
operations on floating point numbers. *)

(** This module assumes Nat is extracted to int and Z is extracted to
int *)

Require Import JsAst.JsNumber.
Require Import Float.
Require Import EquivDec.
Require Import Extraction.

(** BUG !!! B755_zero false = +0 ; B755_zero true = -0 *)
(** BUG !!! SAME FOR INFINITY *)
Extract Inductive Fappli_IEEE.binary_float => float [
  "(fun s -> if s then (-0.) else (0.))"
  "(fun s -> if s then neg_infinity else infinity)"
  "nan"
  "(fun (s, m, e) -> if s then -. (ldexp (float_of_int m) e) else (ldexp (float_of_int m) e))"
].
Extract Inlined Constant nan => "nan".
Extract Inlined Constant zero => "0.".
Extract Inlined Constant neg_zero => "(-0.)".
Extract Inlined Constant one => "1.".
Extract Inlined Constant neg_one => "(-1.)".
Extract Inlined Constant infinity => "infinity".
Extract Inlined Constant neg_infinity => "neg_infinity".
Extract Inlined Constant max_value => "max_float".
Extract Inlined Constant min_value => "(Int64.float_of_bits Int64.one)". (** XXX Why not min_float in OCaml? *)

Extract Inlined Constant float_floor => "(fun x -> floor x)".
Extract Inlined Constant float_absolute => "(fun x -> abs_float x)".
Extract Inlined Constant float_neg => "(fun x -> ~-. x)".

(** Defines additional operations on FLOATs *)
(** Unary operations *)

Extract Inlined Constant float_sqrt => "(fun x -> sqrt x)".
Extract Inlined Constant float_exp => "(fun x -> exp x)".
Extract Inlined Constant float_log => "(fun x -> log x)".
Extract Inlined Constant float_log10 => "(fun x -> log10 x)".
Extract Inlined Constant float_ceil => "(fun x -> ceil x)".

Extract Inlined Constant float_eq => "(fun x y -> x = y)".

Conjecture float_eq_correct :
  forall f1 f2, (float_eq f1 f2 = true <-> f1 = f2).
Lemma float_eq_dec : EqDec float eq.
Proof.
  unfold EqDec.
  intros x y.
  case_eq (float_eq x y); intros eqq.
  + left.
    f_equal.
    apply float_eq_correct in eqq.
    trivial.
  + right; intros eqq2.
    red in eqq2.
    apply float_eq_correct in eqq2.
    congruence.
Defined.
  
Extract Constant float_eq_dec => "(fun n1 n2 -> 0 = compare n1 n2)".

(** Binary operations *)
Extract Inlined Constant float_add => "(fun x y -> x +. y)".
Extract Inlined Constant float_sub => "(fun x y -> x -. y)".
Extract Inlined Constant float_mult => "(fun x y -> x *. y)".
Extract Inlined Constant float_div => "(fun x y -> x /. y)".

Extract Inlined Constant float_pow => "(fun x y -> x ** y)".
Extract Inlined Constant float_min => "(fun x y -> min x y)".
Extract Inlined Constant float_max => "(fun x y -> max x y)".
Extract Inlined Constant float_ne => "(fun x y -> x <> y)".
Extract Inlined Constant float_lt => "(fun x y -> x < y)".
Extract Inlined Constant float_le => "(fun x y -> x <= y)".
Extract Inlined Constant float_gt => "(fun x y -> x > y)".
Extract Inlined Constant float_ge => "(fun x y -> x >= y)".

Require Import ZArith.
Extract Inlined Constant float_of_int => "(fun x -> float_of_int x)".

Extract Inlined Constant float_truncate => "(fun x -> truncate x)".

Extract Inlined Constant from_string => "(fun x -> float_of_string (QcertUtils.Util.string_of_char_list x))".
Extract Inlined Constant to_string => "(fun x -> QcertUtils.Util.char_list_of_string (QcertUtils.Util.qcert_string_of_float x))".

