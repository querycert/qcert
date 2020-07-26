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
Require Import BinPos Zpower ZArith.
Require Floats PrimFloat.
Require JsAst.JsNumber.

(** Floating point numbers use Flocq binary 64 representation (double precision IEEE 754) *)

Definition float : Set := PrimFloat.float.

(** The following definitions already exist in JsAst.JsNumber *)

Definition float_nan : float := PrimFloat.nan.
Definition float_zero : float := PrimFloat.zero.
Definition float_neg_zero : float := PrimFloat.neg_zero.
Definition float_one : float := PrimFloat.one.
Definition float_neg_one : float := Eval compute in (PrimFloat.opp PrimFloat.one).
Definition float_infinity : float := PrimFloat.infinity.
Definition float_neg_infinity : float := PrimFloat.neg_infinity.

Parameter float_min_value : float.
Parameter float_max_value : float.

(* from JsAst *)
Definition float_from_string : string -> float := JsNumber.from_string.
Definition float_to_string : float -> string := JsNumber.to_string.

Definition float_neg : float -> float := PrimFloat.opp.
Definition float_floor : float -> float := JsNumber.floor.
Definition float_absolute : float -> float := PrimFloat.abs.

Definition float_sign : float -> float := (* Note: This sign function is consistent with Math.sign in JavaScript *)
  fun x => match PrimFloat.classify x with
        | FloatClass.PNormal => float_one
        | FloatClass.NNormal => float_neg_one
        | _ => x
        end.


Definition float_add : float -> float -> float := PrimFloat.add.
Definition float_sub : float -> float -> float := PrimFloat.sub.
Definition float_mult : float -> float -> float := PrimFloat.mul.
Definition float_div : float -> float -> float := PrimFloat.div.

(** The following are additional floating point operations used in Q*cert *)

(** Unary operations *)

Parameter float_sqrt : float -> float. (** TODO exists in Flocq *)
Parameter float_exp : float -> float.
Parameter float_log : float -> float.
Parameter float_log10 : float -> float.
Parameter float_ceil : float -> float.

Definition float_eq : float -> float -> bool := PrimFloat.eqb.

Conjecture float_eq_correct :
  forall f1 f2, (float_eq f1 f2 = true <-> f1 = f2).

Require Import EquivDec.
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

Parameter float_pow : float -> float -> float.
Parameter float_min : float -> float -> float. (** TODO: Check in JavaScript spec what happens for min/max *)
Parameter float_max : float -> float -> float.
Parameter float_ne : float -> float -> bool.
Definition float_lt (n1 n2 : float) := PrimFloat.ltb n1 n2.
Definition float_le : float -> float -> bool := PrimFloat.leb.
Definition float_gt (n1 n2: float) : bool := float_lt n2 n1.
Definition float_ge (n1 n2: float) : bool := float_le n2 n1.

Parameter float_of_int : Z -> float. (** Binary normalize *)
Parameter float_truncate : float -> Z. (** Do like parsing ... *)

Definition float_list_min (l:list float) : float :=
  fold_right (fun x y => float_min x y) float_infinity l.

Definition float_list_max (l:list float) : float :=
  fold_right (fun x y => float_max x y) float_neg_infinity l.

Definition float_list_sum (l:list float) : float :=
  fold_right (fun x y => float_add x y) float_zero l.

Definition float_list_arithmean (l:list float) : float :=
  let ll := List.length l in
  match ll with
  | O => float_zero
  | _ => float_div (float_list_sum l) (float_of_int (Z_of_nat ll))
  end.

