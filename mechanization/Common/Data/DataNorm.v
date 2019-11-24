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
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignData.
Require Import Data.

Section DataNorm.
  Context {fdata:foreign_data}.
  Context (h:brand_relation_t).
  Fixpoint normalize_data (d:data) : data :=
    match d with
    | drec rl =>
      drec (rec_sort (map (fun x => (fst x, normalize_data (snd x))) rl))
    | dcoll l => dcoll (map normalize_data l)
    | dleft l => dleft (normalize_data l)
    | dright l  => dright (normalize_data l)
    | dbrand b d => dbrand (canon_brands h b) (normalize_data d)
    | dforeign fd => dforeign (foreign_data_normalize fd)
    | _ => d
    end.

  Inductive data_normalized : data -> Prop :=
  | dnunit :
      data_normalized dunit
  | dnnat n :
      data_normalized (dnat n)
  | dnfloat n :
      data_normalized (dfloat n)
  | dnbool b :
      data_normalized (dbool b)
  | dnstring s :
      data_normalized (dstring s)
  | dncoll dl :
      Forall (fun x => data_normalized x) dl -> data_normalized (dcoll dl)
  | dnrec dl :
      Forall (fun d => data_normalized (snd d)) dl ->
      (is_list_sorted ODT_lt_dec (domain dl) = true) ->
      data_normalized (drec dl)
  | dnleft l :
      data_normalized l ->
      data_normalized (dleft l)
  | dnright r :
      data_normalized r ->
      data_normalized (dright r)
  | dnbrand b d :
      is_canon_brands h b ->
      data_normalized d ->
      data_normalized (dbrand b d)
  | dnforeign fd :
      foreign_data_normalized fd ->
      data_normalized (dforeign fd).

  Theorem normalize_normalizes :
    forall (d:data), data_normalized (normalize_data d).
  Proof.
    induction d using dataInd2; simpl.
    - apply dnunit.
    - apply dnnat.
    - apply dnfloat.
    - apply dnbool.
    - apply dnstring.
    - apply dncoll.
      apply Forall_forall; intros.
      induction c; elim H0; intros.
      rewrite <- H1.
      apply (H a); left; reflexivity.
      assert (forall x:data, In x c -> data_normalized (normalize_data x))
        by (intros; apply (H x0); right; assumption).
      specialize (IHc H2 H1).
      assumption.
    - apply dnrec.
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
        assert (forall (x : string) (y : data),
                   In (x, y) r -> data_normalized (normalize_data y)); intros.
        apply (H x0 y); right; assumption.
        apply (IHr H0).
        assumption.
      + apply (@rec_sort_sorted string ODT_string) with (l1 := (map (fun x : string * data => (fst x, normalize_data (snd x))) r)).
        reflexivity.
    - constructor; trivial.
    - constructor; trivial.
    - constructor; trivial.
    - constructor.
      apply foreign_data_normalize_normalizes.
  Qed.

  Theorem normalize_normalized_eq {d}:
    data_normalized d ->
    normalize_data d = d.
  Proof.
    induction d using dataInd2; simpl; trivial.
    - intros. 
      rewrite (@map_eq _ _ normalize_data id).
      + rewrite map_id; trivial.
      + inversion H0; simpl; subst.
        revert H2. apply Forall_impl_in.
        auto.
    - intros.
      inversion H0; subst.
      rewrite (@map_eq _ _ (fun x : string * data => (fst x, normalize_data (snd x))) id).
      + rewrite map_id.
        rewrite rec_sorted_id; trivial.
      + revert H2. apply Forall_impl_in.
        destruct a; unfold id; simpl; intros.
        f_equal; eauto.
    - inversion 1; subst. rewrite (IHd H1); trivial.
    - inversion 1; subst. rewrite (IHd H1); trivial.
    - inversion 1; subst.
      rewrite IHd; trivial.
      rewrite is_canon_brands_canon_brands; trivial.
    - inversion 1; subst.
      f_equal.
      apply foreign_data_normalize_idempotent.
      trivial.
  Qed.

  Lemma map_normalize_normalized_eq c :
    Forall (fun x => data_normalized (snd x)) c ->
    (map
       (fun x0 : string * data => (fst x0, normalize_data (snd x0)))
       c) = c.
  Proof.
    induction c; simpl; trivial.
    destruct a; inversion 1; simpl in *; subst.
    rewrite normalize_normalized_eq; trivial.
    rewrite IHc; trivial.
  Qed.


  Corollary normalize_idem d :
    normalize_data (normalize_data d) = normalize_data d.
  Proof.
    apply normalize_normalized_eq.
    apply normalize_normalizes.
  Qed.

  Corollary normalize_data_eq_normalized {d} :
    normalize_data d = d -> data_normalized d.
  Proof.
    intros.
    generalize (normalize_normalizes d).
    congruence.
  Qed.
  
  Theorem normalized_data_dec d : {data_normalized d} + {~ data_normalized d}.
  Proof.
    destruct (normalize_data d == d); unfold equiv, complement in *.
    - left. apply normalize_data_eq_normalized; trivial.
    - right. intro dn; elim c. apply normalize_normalized_eq; trivial.
  Defined.

  Lemma data_normalized_dcoll a l :
    (data_normalized a /\ data_normalized (dcoll l)) <->
    data_normalized (dcoll (a :: l)).
  Proof.
    split.
    - destruct 1 as [d1 d2]. inversion d2; subst.
      constructor; auto.
    - inversion 1; subst. inversion H1; subst.
      split; trivial.
      constructor; auto.
  Qed.
  
  Lemma data_normalized_rec_sort_app l1 l2 :
    data_normalized (drec l1) ->
    data_normalized (drec l2) ->
    data_normalized (drec (rec_sort (l1 ++ l2))).
  Proof.
    inversion 1; inversion 1; subst.
    constructor; eauto 1.
    apply Forall_sorted.
    apply Forall_app; trivial.
  Qed.

  Lemma data_normalized_rec_concat_sort l1 l2 :
    data_normalized (drec l1) ->
    data_normalized (drec l2) ->
    data_normalized (drec (rec_concat_sort l1 l2)).
  Proof.
    apply data_normalized_rec_sort_app.
  Qed.

  Lemma data_normalized_dcoll_in x l :
    In x l ->
    data_normalized (dcoll l) ->
    data_normalized x.
  Proof.
    inversion 2; subst.
    rewrite Forall_forall in H2.
    eauto.
  Qed.

  Lemma dnrec_nil : data_normalized (drec nil).
  Proof.
    econstructor; trivial.
  Qed.

  Lemma dnrec_sort_content c :
    Forall (fun d : string * data => data_normalized (snd d)) c ->
    Forall (fun d : string * data => data_normalized (snd d)) (rec_sort c).
  Proof.
    intros F.
    apply Forall_sorted; trivial.
  Qed.

  Lemma dnrec_sort c :
    Forall (fun d : string * data => data_normalized (snd d)) c ->
    data_normalized (drec (rec_sort c)).
  Proof.
    intros F; econstructor; trivial.
    apply Forall_sorted; trivial.
  Qed.

  Lemma data_normalized_dcoll_Forall l :
    data_normalized (dcoll l) <-> Forall data_normalized l.
  Proof.
    split; intros H.
    - invcs H; trivial.
    - constructor; trivial.
  Qed.
  
End DataNorm.

