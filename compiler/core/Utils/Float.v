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
Require Flocq.Appli.Fappli_IEEE.
Require Flocq.Appli.Fappli_IEEE_bits.
Require Import JsAst.JsNumber.

(** Floating point numbers use Flocq binary 64 representation (double precision IEEE 754) *)

Definition float : Set := Fappli_IEEE_bits.binary64.


(** The following definitions already exist in JsAst.JsNumber *)

Definition float_nan : float := nan.
Definition float_zero : float := zero.
Definition float_neg_zero : float := neg_zero.
Definition float_one : float := one.
Definition float_neg_one : float := neg_one.
Definition float_infinity : float := infinity.
Definition float_neg_infinity : float := neg_infinity.

Definition float_max_value : float := max_value.
Definition float_min_value : float := min_value.

(** Initial idea for converting external sign+mantisse+exponent into Flocq binary64. Possibly this could be tied to a parser from strings. *)
Definition float_triple : Set := (bool * positive * Z).
Definition float_triple_to_b64 (ft:float_triple) : float :=
  let '(sign, m, e) := ft in
  match e with
  | Z0 => Fappli_IEEE.B754_zero _ _ false
  | Zneg e =>
    let my :=
        match Zpower_pos 10 e with
        | Zpos p => p
        | _ => xH
        end
    in
    Fappli_IEEE.FF2B
      53 1024 _
      (proj1
         (Fappli_IEEE.Bdiv_correct_aux
            53 1024
            (eq_refl Lt) (eq_refl Lt)
            Fappli_IEEE.mode_NE
            sign m 0
            false my 0))
  | Zpos e =>
    Fappli_IEEE.B754_zero _ _ false
  end.

Definition float_from_string : string -> float := from_string.
Definition float_to_string : float -> string := to_string.

Definition float_neg : float -> float := neg.
Definition float_floor : float -> float := floor. (* Note: this is an axiom in JsAst.JsNumber *)
Definition float_absolute : float -> float := absolute.
Definition float_sign : float -> float := sign.

Definition float_add : float -> float -> float := add.
Definition float_sub : float -> float -> float := sub.
Definition float_mod : float -> float -> float := fmod. (* Note: this is an axiom in JsAst.JsNumber *)

Definition float_mult : float -> float -> float := mult.
Definition float_div : float -> float -> float := div.

(** The following are additional floating point operations used in Q*cert *)

(** Unary operations *)

Parameter float_sqrt : float -> float. (** TODO exists in Flocq *)
Parameter float_exp : float -> float.
Parameter float_log : float -> float.
Parameter float_log10 : float -> float.
Parameter float_ceil : float -> float.
Parameter float_eq : float -> float -> bool. (* TODO by pattern matching on B754 *)

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
Definition float_lt (n1 n2 : float) := lt_bool n1 n2.
Parameter float_le : float -> float -> bool.
Parameter float_gt : float -> float -> bool.
Parameter float_ge : float -> float -> bool.

Parameter float_of_int : Z -> float. (** Binary normalize *)
Parameter float_truncate : float -> Z. (** Do like parsing ... *)

Definition float_list_min (l:list float) : float :=
  fold_right (fun x y => float_min x y) infinity l.

Definition float_list_max (l:list float) : float :=
  fold_right (fun x y => float_max x y) neg_infinity l.

Definition float_list_sum (l:list float) : float :=
  fold_right (fun x y => float_add x y) zero l.

Definition float_list_arithmean (l:list float) : float :=
  let ll := List.length l in
  match ll with
  | O => zero
  | _ => float_div (float_list_sum l) (float_of_int (Z_of_nat ll))
  end.

