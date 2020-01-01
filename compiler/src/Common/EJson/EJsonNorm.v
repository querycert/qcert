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
Require Import ForeignEJson.
Require Import EJson.

Section EJsonNorm.
  Context {fejson:foreign_ejson}.

  Fixpoint normalize_ejson (d:ejson) : ejson :=
    match d with
    | ejobject rl => ejobject (rec_sort (map (fun x => (fst x, normalize_ejson (snd x))) rl))
    | ejarray l => ejarray (map normalize_ejson l)
    | ejforeign fd => ejforeign (foreign_ejson_normalize fd)
    | _ => d
    end.

  Inductive ejson_normalized : ejson -> Prop :=
  | ejnnull :
      ejson_normalized ejnull
  | ejnnumber n :
      ejson_normalized (ejnumber n)
  | ejnbigint n :
      ejson_normalized (ejbigint n)
  | ejnbool b :
      ejson_normalized (ejbool b)
  | ejnstring s :
      ejson_normalized (ejstring s)
  | ejnarray dl :
      Forall (fun x => ejson_normalized x) dl -> ejson_normalized (ejarray dl)
  | ejnobject dl :
      Forall (fun d => ejson_normalized (snd d)) dl ->
      (is_list_sorted ODT_lt_dec (domain dl) = true) ->
      ejson_normalized (ejobject dl)
  | ejnforeign fd :
      foreign_ejson_normalized fd ->
      ejson_normalized (ejforeign fd).

  Theorem ejson_normalize_normalizes :
    forall (d:ejson), ejson_normalized (normalize_ejson d).
  Proof.
    induction d using ejsonInd2; simpl.
    - apply ejnnull.
    - apply ejnnumber.
    - apply ejnbigint.
    - apply ejnbool.
    - apply ejnstring.
    - apply ejnarray.
      apply Forall_forall; intros.
      induction c; elim H0; intros.
      rewrite <- H1.
      apply (H a); left; reflexivity.
      assert (forall x:ejson, In x c -> ejson_normalized (normalize_ejson x))
        by (intros; apply (H x0); right; assumption).
      specialize (IHc H2 H1).
      assumption.
    - apply ejnobject.
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
        assert (forall (x : string) (y : ejson),
                   In (x, y) r -> ejson_normalized (normalize_ejson y)); intros.
        apply (H x0 y); right; assumption.
        apply (IHr H0).
        assumption.
      + apply (@rec_sort_sorted string ODT_string) with (l1 := (map (fun x : string * ejson => (fst x, normalize_ejson (snd x))) r)).
        reflexivity.
    - constructor.
      apply foreign_ejson_normalize_normalizes.
  Qed.

  Theorem ejson_normalize_normalized_eq {d}:
    ejson_normalized d ->
    normalize_ejson d = d.
  Proof.
    induction d using ejsonInd2; simpl; trivial.
    - intros.
      rewrite (@map_eq _ _ normalize_ejson id).
      + rewrite map_id; trivial.
      + inversion H0; simpl; subst.
        revert H2. apply Forall_impl_in.
        auto.
    - intros.
      inversion H0; subst.
      rewrite (@map_eq _ _ (fun x : string * ejson => (fst x, normalize_ejson (snd x))) id).
      + rewrite map_id.
        rewrite rec_sorted_id; trivial.
      + revert H2. apply Forall_impl_in.
        destruct a; unfold id; simpl; intros.
        f_equal; eauto.
    - inversion 1; subst.
      f_equal.
      apply foreign_ejson_normalize_idempotent.
      trivial.
  Qed.

  Lemma ejson_map_normalize_normalized_eq c :
    Forall (fun x => ejson_normalized (snd x)) c ->
    (map
       (fun x0 : string * ejson => (fst x0, normalize_ejson (snd x0)))
       c) = c.
  Proof.
    induction c; simpl; trivial.
    destruct a; inversion 1; simpl in *; subst.
    rewrite ejson_normalize_normalized_eq; trivial.
    rewrite IHc; trivial.
  Qed.

  Corollary ejson_normalize_idem d :
    normalize_ejson (normalize_ejson d) = normalize_ejson d.
  Proof.
    apply ejson_normalize_normalized_eq.
    apply ejson_normalize_normalizes.
  Qed.

  Corollary normalize_ejson_eq_normalized {d} :
    normalize_ejson d = d -> ejson_normalized d.
  Proof.
    intros.
    generalize (ejson_normalize_normalizes d).
    congruence.
  Qed.

  Theorem normalized_ejson_dec d : {ejson_normalized d} + {~ ejson_normalized d}.
  Proof.
    destruct (normalize_ejson d == d); unfold equiv, complement in *.
    - left. apply normalize_ejson_eq_normalized; trivial.
    - right. intro dn; elim c. apply ejson_normalize_normalized_eq; trivial.
  Defined.

  Lemma ejson_normalized_jarray a l :
    (ejson_normalized a /\ ejson_normalized (ejarray l)) <->
    ejson_normalized (ejarray (a :: l)).
  Proof.
    split.
    - destruct 1 as [d1 d2]. inversion d2; subst.
      constructor; auto.
    - inversion 1; subst. inversion H1; subst.
      split; trivial.
      constructor; auto.
  Qed.
  
  Lemma ejson_normalized_rec_sort_app l1 l2 :
    ejson_normalized (ejobject l1) ->
    ejson_normalized (ejobject l2) ->
    ejson_normalized (ejobject (rec_sort (l1 ++ l2))).
  Proof.
    inversion 1; inversion 1; subst.
    constructor; eauto 1.
    apply Forall_sorted.
    apply Forall_app; trivial.
  Qed.

  Lemma ejson_normalized_rec_concat_sort l1 l2 :
    ejson_normalized (ejobject l1) ->
    ejson_normalized (ejobject l2) ->
    ejson_normalized (ejobject (rec_concat_sort l1 l2)).
  Proof.
    apply ejson_normalized_rec_sort_app.
  Qed.

  Lemma ejson_normalized_jarray_in x l :
    In x l ->
    ejson_normalized (ejarray l) ->
    ejson_normalized x.
  Proof.
    inversion 2; subst.
    rewrite Forall_forall in H2.
    eauto.
  Qed.

  Lemma ejnobject_nil : ejson_normalized (ejobject nil).
  Proof.
    econstructor; trivial.
  Qed.

  Lemma ejnobject_sort_content c :
    Forall (fun d : string * ejson => ejson_normalized (snd d)) c ->
    Forall (fun d : string * ejson => ejson_normalized (snd d)) (rec_sort c).
  Proof.
    intros F.
    apply Forall_sorted; trivial.
  Qed.

  Lemma ejnobject_sort c :
    Forall (fun d : string * ejson => ejson_normalized (snd d)) c ->
    ejson_normalized (ejobject (rec_sort c)).
  Proof.
    intros F; econstructor; trivial.
    apply Forall_sorted; trivial.
  Qed.

  Lemma ejson_normalized_jarray_Forall l :
    ejson_normalized (ejarray l) <-> Forall ejson_normalized l.
  Proof.
    split; intros H.
    - invcs H; trivial.
    - constructor; trivial.
  Qed.
  
End EJsonNorm.

