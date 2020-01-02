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

Require Import List.
Require Import Ascii.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import JsAst.JsNumber.
Require Import Float.
Require Import ToString.
Require Import CoqLibAdd.
Require Import StringAdd.
Require Import Digits.
Require Import EquivDec.

Section JSON.
  Unset Elimination Schemes.

  Inductive json : Set :=
  | jnull : json
  | jnumber : float -> json
  | jbool : bool -> json
  | jstring : string -> json
  | jarray : list json -> json
  | jobject : list (string * json) -> json
  .

  Set Elimination Schemes.

  (** Induction principles used as backbone for inductive proofs on json *)
  Definition json_rect (P : json -> Type)
             (fnull : P jnull)
             (fnumber : forall n : number, P (jnumber n))
             (fbool : forall b : bool, P (jbool b))
             (fstring : forall s : string, P (jstring s))
             (farray : forall c : list json, Forallt P c -> P (jarray c))
             (fobject : forall r : list (string * json), Forallt (fun ab => P (snd ab)) r -> P (jobject r))
    :=
      fix F (j : json) : P j :=
    match j as j0 return (P j0) with
      | jnull => fnull
      | jnumber x => fnumber x
      | jbool x => fbool x
      | jstring x => fstring x
      | jarray x => farray x ((fix F2 (c : list json) : Forallt P c :=
                            match c as c0 with
                              | nil => Forallt_nil _
                              | cons j c0 => @Forallt_cons _ P j c0 (F j) (F2 c0)
                            end) x)
      | jobject x => fobject x ((fix F3 (r : list (string*json)) : Forallt (fun ab => P (snd ab)) r :=
                           match r as c0 with
                             | nil => Forallt_nil _
                             | cons sj c0 => @Forallt_cons _ (fun ab => P (snd ab)) sj c0 (F (snd sj)) (F3 c0)
                           end) x)
    end.

  Definition json_ind (P : json -> Prop)
             (fnull : P jnull)
             (fnumber : forall n : number, P (jnumber n))
             (fbool : forall b : bool, P (jbool b))
             (fstring : forall s : string, P (jstring s))
             (farray : forall c : list json, Forall P c -> P (jarray c))
             (fobject : forall r : list (string * json), Forall (fun ab => P (snd ab)) r -> P (jobject r))
    :=
      fix F (j : json) : P j :=
    match j as j0 return (P j0) with
      | jnull => fnull
      | jnumber x => fnumber x
      | jbool x => fbool x
      | jstring x => fstring x
      | jarray x => farray x ((fix F2 (c : list json) : Forall P c :=
                            match c with
                              | nil => Forall_nil _
                              | cons j c0 => @Forall_cons _ P j c0 (F j) (F2 c0)
                            end) x)
      | jobject x => fobject x ((fix F3 (r : list (string*json)) : Forall (fun ab => P (snd ab)) r :=
                           match r with
                             | nil => Forall_nil _
                             | cons sj c0 => @Forall_cons _ (fun ab => P (snd ab)) sj c0 (F (snd sj)) (F3 c0)
                           end) x)
    end.

  Definition json_rec (P:json->Set) := json_rect P.

  Lemma jsonInd2 (P : json -> Prop)
        (f : P jnull)
        (f0 : forall n : number, P (jnumber n))
        (f1 : forall b : bool, P (jbool b))
        (f2 : forall s : string, P (jstring s))
        (f3 : forall c : list json, (forall x, In x c -> P x) -> P (jarray c))
        (f4 : forall r : list (string * json), (forall x y, In (x,y) r -> P y) -> P (jobject r)):
    forall d, P d.
  Proof.
    intros.
    apply json_ind; trivial.
    - intros. rewrite Forall_forall in H.
      auto.
    - intros. rewrite Forall_forall in H.
      apply f4.
      intros. apply (H (x,y)). trivial.
  Qed.

  (** Equality is decidable for json *)
  Lemma json_eq_dec : forall x y:json, {x=y}+{x<>y}.
  Proof.
    induction x; destruct y; try solve[right; inversion 1].
    - left; trivial.
    - destruct (float_eq_dec n f).
      + left; f_equal; trivial.
      + right;intro;apply c;inversion H; reflexivity.
    - destruct (bool_dec b b0).
      + left; f_equal; trivial.
      + right;intro;apply n;inversion H; trivial. 
    - destruct (string_dec s s0).
      + left; f_equal; trivial.
      + right;intro;apply n;inversion H; trivial.
    - destruct (list_Forallt_eq_dec c l H). subst. auto.
      right; inversion 1. auto.
    - destruct (list_Forallt_eq_dec r l); subst; auto.
      + apply (forallt_impl H).
        apply forallt_weaken; clear; intros.
        destruct x; destruct y; simpl in *.
        apply pair_eq_dec; auto.
        apply string_dec.
      + right; inversion 1; auto.
  Defined.

  (* begin hide *)
  Global Instance json_eqdec : EqDec json eq := json_eq_dec.
  (* begin hide *)

  Section toString.

    Local Open Scope string.

    Fixpoint jsonStringify (quotel:string) (j : json) : string
      := match j with
         | jnull => "null"
         | jnumber n => toString n
         | jbool b => toString b
         | jstring s => stringToStringQuote quotel s
         | jarray ls =>
           let ss := map (jsonStringify quotel) ls in
           "[" ++ (concat ", " ss) ++ "]"
         | jobject ls =>
           let ss := (map (fun kv =>
                             let '(k,v) := kv in
                             "" ++ quotel ++ "" ++ k ++ ""
                                ++ quotel ++ ": " ++ (jsonStringify quotel v)) ls)
           in "{" ++ (concat ", " ss) ++ "}"
         end.

  End toString.

  Section Encode.
    Definition json_key_encode (s:string) : string
      := match s with
         | String "$"%char s => String "$"%char (String "$"%char s)
         | _ => s
         end.

    Definition json_key_decode (s:string) : string
      := match s with
         | EmptyString => EmptyString
         | String "$"%char (String "$"%char s) =>  String "$"%char s
         | _ => s
         end.

    Lemma json_key_encode_decode (s:string) : json_key_decode (json_key_encode s) = s.
      do 2 (destruct s; simpl; trivial)
      ; repeat match_destr.
    Qed.

    Lemma json_key_encode_not_data s : (json_key_encode s) <> "$data"%string.
    Proof.
      destruct s; simpl; try discriminate.
      repeat match_destr.
    Qed.

    Lemma json_key_encode_not_class s : (json_key_encode s) <> "$class"%string.
    Proof.
      destruct s; simpl; try discriminate.
      repeat match_destr.
    Qed.

    Lemma json_key_encode_not_foreign s : (json_key_encode s) <> "$foreign"%string.
    Proof.
      destruct s; simpl; try discriminate.
      repeat match_destr.
    Qed.

    Lemma json_key_encode_not_nat s : (json_key_encode s) <> "$nat"%string.
    Proof.
      destruct s; simpl; try discriminate.
      repeat match_destr.
    Qed.

    Lemma json_key_encode_not_left s : (json_key_encode s) <> "$left"%string.
    Proof.
      destruct s; simpl; try discriminate.
      repeat match_destr.
    Qed.

    Lemma json_key_encode_not_right s : (json_key_encode s) <> "$right"%string.
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
      
    Lemma json_key_encode_inv s s0:
      (json_key_encode s) = (json_key_encode s0) ->
      s = s0.
    Proof.
      intros.
      unfold json_key_encode in H.
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
      
    Lemma json_key_encode_diff s s0:
      s <> s0
      -> (json_key_encode s) <> (json_key_encode s0).
    Proof.
      intros.
      unfold not in *.
      intros.
      apply H; clear H.
      apply json_key_encode_inv; assumption.
    Qed.

    Lemma json_key_encode_eq s s0:
      (json_key_encode s) = (json_key_encode s0) <-> s = s0.
    Proof.
      split.
      - apply json_key_encode_inv.
      - intros; subst; reflexivity.
    Qed.
    
    Lemma in_map_json_key_encode s pl:
      In s pl -> In (json_key_encode s) (map json_key_encode pl).
    Proof.
      apply in_map.
    Qed.

    Lemma in_map_json_key_encode_inv s pl:
      In (json_key_encode s) (map json_key_encode pl) -> In s pl.
    Proof.
      intros.
      induction pl; simpl in *; trivial.
      simpl in *.
      elim H; intros; clear H.
      - left; apply json_key_encode_inv; assumption.
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
        
    Lemma json_key_encode_lt s s0:
      StringOrder.lt s s0 -> StringOrder.lt (json_key_encode s) (json_key_encode s0).
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

    Lemma json_key_encode_lt_inv s s0:
      StringOrder.lt (json_key_encode s) (json_key_encode s0) -> StringOrder.lt s s0.
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

    Lemma json_key_encode_lt_idem s s0:
      StringOrder.lt s s0 <-> StringOrder.lt (json_key_encode s) (json_key_encode s0).
    Proof.
      split.
      - apply json_key_encode_lt.
      - apply json_key_encode_lt_inv.
    Qed.

  End Encode.

End JSON.
