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
Require Import Ascii.
Require Import String.
Require Import CoqLibAdd.
Require Import StringAdd.

Section Encode.
  Definition key_encode (s:string) : string
    := match s with
       | String "$"%char s => String "$"%char (String "$"%char s)
       | _ => s
       end.

  Definition key_decode (s:string) : string
    := match s with
       | EmptyString => EmptyString
       | String "$"%char (String "$"%char s) =>  String "$"%char s
         | _ => s
       end.

  Lemma key_encode_decode (s:string) : key_decode (key_encode s) = s.
    do 2 (destruct s; simpl; trivial)
    ; repeat match_destr.
  Qed.

  Lemma key_encode_not_data s : (key_encode s) <> "$data"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
  Qed.

  Lemma key_encode_not_class s : (key_encode s) <> "$class"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
  Qed.

  Lemma key_encode_not_foreign s : (key_encode s) <> "$foreign"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
  Qed.

  Lemma key_encode_not_nat s : (key_encode s) <> "$nat"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
  Qed.

  Lemma key_encode_not_left s : (key_encode s) <> "$left"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
  Qed.

  Lemma key_encode_not_right s : (key_encode s) <> "$right"%string.
  Proof.
    destruct s; simpl; try discriminate.
    repeat match_destr.
  Qed.

  Lemma match_not_dollar a s :
    a <> "$"%char ->
    match a with
    | "$"%char => String "$" (String "$" s)
    | _ => String a s
    end = String a s.
  Proof.
    intros.
    destruct a; simpl; try congruence.
    destruct b; simpl; try congruence.
    destruct b0; simpl; try congruence.
    destruct b1; simpl; try congruence.
    destruct b2; simpl; try congruence.
    destruct b3; simpl; try congruence.
    destruct b4; simpl; try congruence.
    destruct b5; simpl; try congruence.
    destruct b6; simpl; congruence.
  Qed.

  Lemma key_encode_inv s s0:
    (key_encode s) = (key_encode s0) ->
    s = s0.
  Proof.
    intros.
    unfold key_encode in H.
    destruct s; destruct s0; simpl in *.
    - reflexivity.
    - destruct a; simpl.
      destruct b; try congruence.
      destruct b0; try congruence.
      destruct b1; try congruence.
      destruct b2; try congruence.
      destruct b3; try congruence.
      destruct b4; try congruence.
      destruct b5; try congruence.
      destruct b6; try congruence.
    - destruct a; simpl.
      destruct b; try congruence.
      destruct b0; try congruence.
      destruct b1; try congruence.
      destruct b2; try congruence.
      destruct b3; try congruence.
      destruct b4; try congruence.
      destruct b5; try congruence.
      destruct b6; try congruence.
    - specialize (ascii_dec a "$"%char);
        specialize (ascii_dec a0 "$"%char);
        intros.
      elim H0 ; elim H1; intros; clear H0 H1.
      + rewrite a1 in H; simpl.
        rewrite a2 in H; simpl.
        rewrite a1; rewrite a2.
        inversion H; reflexivity.
      + rewrite a1 in H.
        rewrite (match_not_dollar a s b) in H.
        inversion H; subst. congruence.
      + rewrite a1 in H.
        rewrite (match_not_dollar a0 s0 b) in H.
        inversion H; subst. congruence.
      + rewrite (match_not_dollar a s b) in H.
        rewrite (match_not_dollar a0 s0 b0) in H.
        assumption.
  Qed.

  Lemma key_encode_diff s s0:
    s <> s0
    -> (key_encode s) <> (key_encode s0).
  Proof.
    intros.
    unfold not in *.
    intros.
    apply H; clear H.
    apply key_encode_inv; assumption.
  Qed.

  Lemma key_encode_eq s s0:
    (key_encode s) = (key_encode s0) <-> s = s0.
  Proof.
    split.
    - apply key_encode_inv.
    - intros; subst; reflexivity.
  Qed.

  Lemma in_map_key_encode s pl:
    In s pl -> In (key_encode s) (map key_encode pl).
  Proof.
    apply in_map.
  Qed.

  Lemma in_map_key_encode_inv s pl:
    In (key_encode s) (map key_encode pl) -> In s pl.
  Proof.
    intros.
    induction pl; simpl in *; trivial.
    simpl in *.
    elim H; intros; clear H.
    - left; apply key_encode_inv; assumption.
    - auto.
  Qed.

  Lemma match_one_dollar_character a s0:
    exists b s,
      match a with
      | "$"%char => String "$" (String "$" s0)
      | _ => String a s0
      end = String b s.
  Proof.
    specialize (ascii_dec a "$"%char); intros.
    elim H; intros.
    rewrite a0.
    - exists "$"%char.  exists (String "$" s0); reflexivity.
    - exists a. exists s0.
      rewrite (match_not_dollar a s0 b).
      reflexivity.
  Qed.

  Lemma key_encode_lt s s0:
    StringOrder.lt s s0 -> StringOrder.lt (key_encode s) (key_encode s0).
  Proof.
    revert s0.
    induction s; destruct s0; intros; simpl.
    - auto.
    - unfold StringOrder.lt, StringOrder.compare in *.
      elim (match_one_dollar_character a s0); intros.
      elim H0; clear H0; intros.
      rewrite H0.
      reflexivity.
    - inversion H.
    - inversion H; clear H.
      specialize (ascii_dec a "$"%char); specialize (ascii_dec a0 "$"%char); intros.
      elim H; clear H; elim H0; clear H0; intros.
      + rewrite a1 in *; rewrite a2 in *.
        inversion H1.
        auto.
      + rewrite a1 in *.
        rewrite (match_not_dollar a s b).
        case_eq (AsciiOrder.compare a "$"); intros; rewrite H in H1.
        * rewrite AsciiOrder.compare_eq_iff in H; congruence.
        * unfold StringOrder.lt; simpl. rewrite H. assumption.
        * congruence.
      + rewrite a1 in *.
        rewrite (match_not_dollar a0 s0 b).
        case_eq (AsciiOrder.compare "$" a0); intros; rewrite H in H1.
        * rewrite AsciiOrder.compare_eq_iff in H; congruence.
        * unfold StringOrder.lt; simpl; rewrite H; assumption.
        * congruence.
      + rewrite (match_not_dollar a s b).
        rewrite (match_not_dollar a0 s0 b0).
        case_eq (AsciiOrder.compare a a0); intros; rewrite H in H1.
        unfold StringOrder.lt; simpl. rewrite H. assumption.
        unfold StringOrder.lt; simpl. rewrite H. assumption.
        congruence.
  Qed.

  Lemma key_encode_lt_inv s s0:
    StringOrder.lt (key_encode s) (key_encode s0) -> StringOrder.lt s s0.
  Proof.
    revert s0.
    induction s; destruct s0; intros; simpl.
    - auto.
    - unfold StringOrder.lt, StringOrder.compare in *.
      reflexivity.
    - inversion H.
      specialize (ascii_dec a "$"%char); intros.
      elim H0; clear H0; intros.
      + rewrite a0 in H1; simpl in H1; congruence.
      + rewrite (match_not_dollar a s b) in H1; assumption.
    - inversion H; clear H.
      specialize (ascii_dec a "$"%char); specialize (ascii_dec a0 "$"%char); intros.
      elim H; clear H; elim H0; clear H0; intros.
      + rewrite a1 in *; rewrite a2 in *.
        inversion H1.
        unfold StringOrder.lt; simpl; assumption.
      + rewrite a1 in *.
        rewrite (match_not_dollar a s b) in H1.
        inversion H1.
        case_eq (AsciiOrder.compare a "$"); intros; rewrite H in H0.
        * rewrite AsciiOrder.compare_eq_iff in H; congruence.
        * unfold StringOrder.lt; simpl; rewrite H; assumption.
        * congruence.
      + rewrite a1 in *.
        rewrite (match_not_dollar a0 s0 b) in H1.
        inversion H1.
        case_eq (AsciiOrder.compare "$" a0); intros; rewrite H in H0.
        * rewrite AsciiOrder.compare_eq_iff in H; congruence.
        * unfold StringOrder.lt; simpl; rewrite H; assumption.
        * congruence.
      + rewrite (match_not_dollar a s b) in H1.
        rewrite (match_not_dollar a0 s0 b0) in H1.
        unfold StringOrder.lt.
        assumption.
  Qed.

  Lemma key_encode_lt_idem s s0:
    StringOrder.lt s s0 <-> StringOrder.lt (key_encode s) (key_encode s0).
  Proof.
    split.
    - apply key_encode_lt.
    - apply key_encode_lt_inv.
  Qed.

  Lemma match_not_left {A} s (x y:A):
    s <> "$left"%string ->
    match s with
    | "$left"%string => Some y
    | _ => None
    end = None.
  Proof.
    intros.
    repeat (destruct s; simpl; try congruence;
    destruct a; simpl; try congruence;
    destruct b; simpl; try congruence;
    destruct b0; simpl; try congruence;
    destruct b1; simpl; try congruence;
    destruct b2; simpl; try congruence;
    destruct b3; simpl; try congruence;
    destruct b4; simpl; try congruence;
    destruct b5; simpl; try congruence;
    destruct b6; simpl; try congruence).
  Qed.

  Lemma match_not_right {A} s (x y:A):
    s <> "$right"%string ->
    match s with
    | "$right"%string => Some y
    | _ => None
    end = None.
  Proof.
    intros.
    repeat (destruct s; simpl; try congruence;
    destruct a; simpl; try congruence;
    destruct b; simpl; try congruence;
    destruct b0; simpl; try congruence;
    destruct b1; simpl; try congruence;
    destruct b2; simpl; try congruence;
    destruct b3; simpl; try congruence;
    destruct b4; simpl; try congruence;
    destruct b5; simpl; try congruence;
    destruct b6; simpl; try congruence).
  Qed.

  Lemma match_neither_left_nor_right {A} s (x y:A):
    s <> "$right"%string -> s <> "$left"%string ->
    match s with
    | "$right"%string => Some x
    | "$left"%string => Some y
    | _ => None
    end = None.
  Proof.
    intros.
    repeat (destruct s; simpl; try congruence;
    destruct a; simpl; try congruence;
    destruct b; simpl; try congruence;
    destruct b0; simpl; try congruence;
    destruct b1; simpl; try congruence;
    destruct b2; simpl; try congruence;
    destruct b3; simpl; try congruence;
    destruct b4; simpl; try congruence;
    destruct b5; simpl; try congruence;
    destruct b6; simpl; try congruence).
  Qed.

End Encode.

