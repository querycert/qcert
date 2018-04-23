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
Require Import Morphisms.
Require Import Basics.
Require Import BrandRelation.
Require Import Utils.
Require Import Types.
Require Import ForeignData.
Require Import CommonData.
Require Import ForeignDataTyping.
Require Import TData.

Section TDData.
  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Inductive ddata_type : ddata -> drtype -> Prop :=
  | dtlocal d τ : data_type d τ -> ddata_type (Dlocal d) (Tlocal τ)
  | dtdistr dl τ : Forall (fun d => data_type d τ) dl -> ddata_type (Ddistr dl) (Tdistr τ).
  
  Lemma ddata_dtype_normalized d dτ :
    ddata_type d dτ -> ddata_normalized brand_relation_brands d.
  Proof.
    intros.
    destruct d; simpl in *.
    - inversion H. subst.
      constructor.
      apply (data_type_normalized d τ H1).
    - inversion H. subst.
      constructor.
      rewrite Forall_forall in *; intros.
      specialize (H1 x H0).
      apply (data_type_normalized x τ H1).
  Qed.

  Definition drtype_sub (dτ₁ dτ₂:drtype) : Prop
    := match dτ₁, dτ₂ with
       | Tlocal τ₁, Tlocal τ₂ => τ₁ ≤ τ₂
       | Tdistr τ₁, Tdistr τ₂ => τ₁ ≤ τ₂
       | _, _ => False
       end.

  Global Instance drtype_sub_pre : PreOrder drtype_sub.
  Proof.
    constructor; red; intros.
    - destruct x; constructor.
    - destruct x; destruct y
      ; simpl in * ; try tauto
      ; destruct z
      ; simpl in * ; try tauto
      ; etransitivity; eauto.
  Qed.

  Global Instance drtype_sub_part : PartialOrder eq drtype_sub.
  Proof.
    intros dτ₁ dτ₂.
    split; intros H.
    - repeat red; subst; intuition.
    - repeat red in H; intuition.
      unfold flip in H1.
      destruct dτ₁; destruct dτ₂
      ; simpl in * ; try tauto
      ; f_equal
      ; apply antisymmetry; auto.
  Qed.

  Global Instance ddata_type_sub :
    Proper (eq ==> drtype_sub ==> impl) ddata_type.
  Proof.
    unfold Proper, respectful, impl
    ; intros d d' ? dτ₁ dτ₂ sub typ
    ; subst d'.
    destruct d; destruct dτ₁
    ; simpl in *; invcs typ
    ; destruct dτ₂; try tauto
    ; constructor.
    - rewrite sub in H1; trivial.
    - rewrite Forall_forall in *.
      intros d ind.
      specialize (H1 _ ind).
      rewrite sub in H1.
      trivial.
  Qed.

  Lemma drtype_sub_dec (dτ₁ dτ₂:drtype) :
    {drtype_sub dτ₁ dτ₂} + {~ drtype_sub dτ₁ dτ₂}.
  Proof.
    destruct dτ₁; destruct dτ₂
    ; simpl.
    - apply subtype_dec.
    - right; tauto.
    - right; tauto.
    - apply subtype_dec.
  Defined.
  
End TDData.

