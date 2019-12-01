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
Require Import Sumbool.
Require Import Arith.
Require Import Bool.
Require Import EquivDec.
Require Import Assoc.
Require Import Bindings.
Require Import SortingAdd.
Require Import CoqLibAdd.
Require Import JSON.

Section JSONNorm.
  Fixpoint normalize_json (d:json) : json :=
    match d with
    | jobject rl => jobject (rec_sort (map (fun x => (fst x, normalize_json (snd x))) rl))
    | jarray l => jarray (map normalize_json l)
    | _ => d
    end.

  Inductive json_normalized : json -> Prop :=
  | jnnull :
      json_normalized jnull
  | jnnumber n :
      json_normalized (jnumber n)
  | jnbigint n :
      json_normalized (jbigint n)
  | jnbool b :
      json_normalized (jbool b)
  | jnstring s :
      json_normalized (jstring s)
  | jnarray dl :
      Forall (fun x => json_normalized x) dl -> json_normalized (jarray dl)
  | jnobject dl :
      Forall (fun d => json_normalized (snd d)) dl ->
      (is_list_sorted ODT_lt_dec (domain dl) = true) ->
      json_normalized (jobject dl).

  Theorem normalize_normalizes :
    forall (d:json), json_normalized (normalize_json d).
  Proof.
    induction d using jsonInd2; simpl.
    - apply jnnull.
    - apply jnnumber.
    - apply jnbigint.
    - apply jnbool.
    - apply jnstring.
    - apply jnarray.
      apply Forall_forall; intros.
      induction c; elim H0; intros.
      rewrite <- H1.
      apply (H a); left; reflexivity.
      assert (forall x:json, In x c -> json_normalized (normalize_json x))
        by (intros; apply (H x0); right; assumption).
      specialize (IHc H2 H1).
      assumption.
    - apply jnobject.
      + apply Forall_sorted.
        apply Forall_forall; intros.
        induction r.
        contradiction.
        simpl in *.
        elim H0; intros; clear H0.
        rewrite <- H1.
        simpl.
        apply (H (fst a) (snd a)).
        left; destruct a; reflexivity.
        assert (forall (x : string) (y : json),
                   In (x, y) r -> json_normalized (normalize_json y)); intros.
        apply (H x0 y); right; assumption.
        apply (IHr H0).
        assumption.
      + apply (@rec_sort_sorted string ODT_string) with (l1 := (map (fun x : string * json => (fst x, normalize_json (snd x))) r)).
        reflexivity.
  Qed.

  Theorem normalize_normalized_eq {d}:
    json_normalized d ->
    normalize_json d = d.
  Proof.
    induction d using jsonInd2; simpl; trivial.
    - intros.
      rewrite (@map_eq _ _ normalize_json id).
      + rewrite map_id; trivial.
      + inversion H0; simpl; subst.
        revert H2. apply Forall_impl_in.
        auto.
    - intros.
      inversion H0; subst.
      rewrite (@map_eq _ _ (fun x : string * json => (fst x, normalize_json (snd x))) id).
      + rewrite map_id.
        rewrite rec_sorted_id; trivial.
      + revert H2. apply Forall_impl_in.
        destruct a; unfold id; simpl; intros.
        f_equal; eauto.
  Qed.

  Lemma map_normalize_normalized_eq c :
    Forall (fun x => json_normalized (snd x)) c ->
    (map
       (fun x0 : string * json => (fst x0, normalize_json (snd x0)))
       c) = c.
  Proof.
    induction c; simpl; trivial.
    destruct a; inversion 1; simpl in *; subst.
    rewrite normalize_normalized_eq; trivial.
    rewrite IHc; trivial.
  Qed.


  Corollary normalize_idem d :
    normalize_json (normalize_json d) = normalize_json d.
  Proof.
    apply normalize_normalized_eq.
    apply normalize_normalizes.
  Qed.

  Corollary normalize_json_eq_normalized {d} :
    normalize_json d = d -> json_normalized d.
  Proof.
    intros.
    generalize (normalize_normalizes d).
    congruence.
  Qed.
  
  Theorem normalized_json_dec d : {json_normalized d} + {~ json_normalized d}.
  Proof.
    destruct (normalize_json d == d); unfold equiv, complement in *.
    - left. apply normalize_json_eq_normalized; trivial.
    - right. intro dn; elim c. apply normalize_normalized_eq; trivial.
  Defined.

  Lemma json_normalized_jarray a l :
    (json_normalized a /\ json_normalized (jarray l)) <->
    json_normalized (jarray (a :: l)).
  Proof.
    split.
    - destruct 1 as [d1 d2]. inversion d2; subst.
      constructor; auto.
    - inversion 1; subst. inversion H1; subst.
      split; trivial.
      constructor; auto.
  Qed.
  
  Lemma json_normalized_rec_sort_app l1 l2 :
    json_normalized (jobject l1) ->
    json_normalized (jobject l2) ->
    json_normalized (jobject (rec_sort (l1 ++ l2))).
  Proof.
    inversion 1; inversion 1; subst.
    constructor; eauto 1.
    apply Forall_sorted.
    apply Forall_app; trivial.
  Qed.

  Lemma json_normalized_rec_concat_sort l1 l2 :
    json_normalized (jobject l1) ->
    json_normalized (jobject l2) ->
    json_normalized (jobject (rec_concat_sort l1 l2)).
  Proof.
    apply json_normalized_rec_sort_app.
  Qed.

  Lemma json_normalized_jarray_in x l :
    In x l ->
    json_normalized (jarray l) ->
    json_normalized x.
  Proof.
    inversion 2; subst.
    rewrite Forall_forall in H2.
    eauto.
  Qed.

  Lemma jnobject_nil : json_normalized (jobject nil).
  Proof.
    econstructor; trivial.
  Qed.

  Lemma jnobject_sort_content c :
    Forall (fun d : string * json => json_normalized (snd d)) c ->
    Forall (fun d : string * json => json_normalized (snd d)) (rec_sort c).
  Proof.
    intros F.
    apply Forall_sorted; trivial.
  Qed.

  Lemma jnobject_sort c :
    Forall (fun d : string * json => json_normalized (snd d)) c ->
    json_normalized (jobject (rec_sort c)).
  Proof.
    intros F; econstructor; trivial.
    apply Forall_sorted; trivial.
  Qed.

  Lemma json_normalized_jarray_Forall l :
    json_normalized (jarray l) <-> Forall json_normalized l.
  Proof.
    split; intros H.
    - invcs H; trivial.
    - constructor; trivial.
  Qed.
  
End JSONNorm.

