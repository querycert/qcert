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

Require Import JsAst.JsNumber.
Require Import EquivDec.
Require Import Extraction.

(** BUG !!! B755_zero false = +0 ; B755_zero true = -0 *)
(** BUG !!! SAME FOR INFINITY *)
Extract Inductive Fappli_IEEE.binary_float => float [
  "(fun s -> if s then (0.) else (-0.))"
  "(fun s -> if s then infinity else neg_infinity)"
  "nan"
  "(fun (s, m, e) -> failwith ""FIXME: No extraction from binary float allowed yet."")"
]. 
Extract Inlined Constant nan => "nan".
Extract Inlined Constant zero => "0.".
Extract Inlined Constant neg_zero => "(-0.)".
Extract Inlined Constant one => "1.".
Extract Inlined Constant infinity => "infinity".
Extract Inlined Constant neg_infinity => "neg_infinity".
Extract Inlined Constant max_value => "max_float".
Extract Inlined Constant min_value => "(Int64.float_of_bits Int64.one)".
Extract Inlined Constant floor => "(fun x -> floor x)".
Extract Inlined Constant absolute => "(fun x -> abs_float x)".
Extract Inlined Constant neg => "(fun x -> ~-. x)".

(*
Extract Inlined Constant fmod => "mod_float".
Extract Inlined Constant sign => "(fun f -> float_of_int (compare f 0.))".
*)

(** Defines additional operations on FLOATs *)
(** Unary operations *)

Axiom sqrt : number -> number. (** In Flocq *)
Extract Inlined Constant sqrt => "(fun x -> sqrt x)".

Axiom exp : number -> number.
Extract Inlined Constant exp => "(fun x -> exp x)".

Axiom log : number -> number.
Extract Inlined Constant log => "(fun x -> log x)".

Axiom log10 : number -> number.
Extract Inlined Constant log10 => "(fun x -> log10 x)".

Axiom ceil : number -> number.
Extract Inlined Constant ceil => "(fun x -> ceil x)".

Axiom sum : list number -> number. (** Note: + is NOT associative, so check the specification for the evaluation order *)
Extract Inlined Constant sum => "(fun x -> Util.float_sum x)".

Axiom arithmean : list number -> number. (** Note: + is NOT associative, so check the specification for the evaluation order *)
Extract Inlined Constant arithmean => "(fun x -> Util.float_arithmean x)".

Axiom number_eq : number -> number -> bool. (* TODO by Jerome pattern matching on B754 *)
Extract Inlined Constant number_eq => "(fun x y -> x = y)".

Conjecture number_eq_correct :
  forall f1 f2, (number_eq f1 f2 = true <-> f1 = f2).
Lemma number_eq_dec : EqDec number eq.
Proof.
  unfold EqDec.
  intros x y.
  case_eq (number_eq x y); intros eqq.
  + left.
    f_equal.
    apply number_eq_correct in eqq.
    trivial.
  + right; intros eqq2.
    red in eqq2.
    apply number_eq_correct in eqq2.
    congruence.
Defined.
  
Extract Constant number_eq_dec => "(fun n1 n2 -> 0 = compare n1 n2)".
Extract Constant lt_bool => "(<)". (* First compare exponent, if same, check mantissa *)

(** Binary operations *)
Extract Inlined Constant add => "(fun x y -> x +. y)".
Extract Inlined Constant sub => "(fun x y -> x -. y)".
Extract Inlined Constant mult => "(fun x y -> x *. y)".
Extract Inlined Constant div => "(fun x y -> x /. y)".

Axiom number_pow : number -> number -> number.
Extract Inlined Constant number_pow => "(fun x y -> x ** y)".
Axiom number_min : number -> number -> number. (** Check in JS spec what happens for min/max *)
Extract Inlined Constant number_min => "(fun x y -> min x y)".
Axiom number_max : number -> number -> number.
Extract Inlined Constant number_max => "(fun x y -> max x y)".
Axiom number_ne : number -> number -> bool.
Extract Inlined Constant number_ne => "(fun x y -> x <> y)".
Axiom number_lt : number -> number -> bool.
Extract Inlined Constant number_lt => "(fun x y -> x < y)".
Axiom number_le : number -> number -> bool.
Extract Inlined Constant number_le => "(fun x y -> x <= y)".
Axiom number_gt : number -> number -> bool.
Extract Inlined Constant number_gt => "(fun x y -> x > y)".
Axiom number_ge : number -> number -> bool.
Extract Inlined Constant number_ge => "(fun x y -> x >= y)".

Section Additional.
  Require Import List.
  Definition listmin (l:list number) :=
    match l with
    | nil => zero
    | x0 :: l' =>
      fold_right (fun x y => number_min x y) x0 l'
    end.

  Definition listmax (l:list number) :=
    match l with
    | nil => zero
    | x0 :: l' =>
      fold_right (fun x y => number_max x y) x0 l'
    end.
End Additional.

Require Import ZArith.
Axiom number_of_int : Z -> number. (** Binary normalize *)
Extract Inlined Constant number_of_int => "(fun x -> float_of_int x)".

Axiom truncate : number -> Z. (** Do like parsing ... *)
Extract Inlined Constant truncate=> "(fun x -> truncate x)".

(*** NOTE: For floor/ceiling, could be *)

Require Flocq.Appli.Fappli_IEEE Flocq.Appli.Fappli_IEEE_bits.
Require Import BinPos.
Require Import ZArith.

