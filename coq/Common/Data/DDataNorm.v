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
Require Import ZArith.
Require Import Bool.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignData.
Require Import Data.
Require Import DataNorm.
Require Import DData.

Section DDataNorm.

  Context {fdata:foreign_data}.
  Context (h:brand_relation_t).

  Definition normalize_ddata (d:ddata) : ddata :=
    match d with
    | Dlocal d => Dlocal (normalize_data h d)
    | Ddistr l => Ddistr (map (normalize_data h) l)
    end.

  Inductive ddata_normalized : ddata -> Prop :=
  | dnlocal d :
      data_normalized h d -> ddata_normalized (Dlocal d)
  | dndistr l :
      Forall (fun x => data_normalized h x) l -> ddata_normalized (Ddistr l).

  Theorem dnormalize_normalizes :
    forall (d:ddata), ddata_normalized (normalize_ddata d).
  Proof.
    intros.
    destruct d.
    - constructor.
      apply normalize_normalizes.
    - constructor.
      apply Forall_forall.
      intros.
      induction l; simpl in *.
      + contradiction.
      + elim H; intros; clear H.
        subst.
        apply normalize_normalizes.
        auto.
  Qed.

  Theorem dnormalize_normalized_eq {d} :
    ddata_normalized d ->
    normalize_ddata d = d.
  Proof.
    intros.
    destruct d; simpl.
    - rewrite normalize_normalized_eq.
      reflexivity.
      inversion H.
      auto.
    - inversion H; subst; clear H.
      induction l; simpl in *.
      + reflexivity.
      + rewrite Forall_forall in *.
        simpl in *.
        f_equal.
        assert (normalize_data h a = a).
        specialize (H1 a).
        rewrite normalize_normalized_eq.
        reflexivity.
        apply H1; left; reflexivity.
        rewrite H; clear H.
        f_equal.
        assert (forall x : data, In x l -> data_normalized h x).
        intros.
        apply H1.
        auto.
        specialize (IHl H).
        inversion IHl.
        rewrite H2.
        assumption.
  Qed.

  Corollary dnormalize_idem d :
    normalize_ddata (normalize_ddata d) = normalize_ddata d.
  Proof.
    rewrite dnormalize_normalized_eq.
    reflexivity.
    apply dnormalize_normalizes.
  Qed.

  Corollary dnormalize_normalizes_local :
    forall (d:data), ddata_normalized (Dlocal (normalize_data h d)).
  Proof.
    intros.
    constructor.
    apply normalize_normalizes.
  Qed.
    
End DDataNorm.

