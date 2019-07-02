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

(*******************************
 * Operators typed equivalence *
 *******************************)

Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import List.
Require Import String.
Require Import Utils.
Require Import Types.
Require Import CommonData.
Require Import ForeignData.
Require Import ForeignDataToJSON.
Require Import ForeignOperators.
Require Import ForeignDataTyping.
Require Import ForeignOperatorsTyping.
Require Import Operators.
Require Import TData.
Require Import TUnaryOperators.
Require Import TBinaryOperators.

Section TOperatorsEq.
  (* Two well-typed operators are type equivalent iff they return the
     same value for every well-typed input.
   *)
  Context {fdata:foreign_data}.
  Context {ftojson:foreign_to_JSON}.
  Context {fuop:foreign_unary_op}.
  Context {fbop:foreign_binary_op}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.
  Context {fuoptyping:foreign_unary_op_typing}.
  Context {fboptyping:foreign_binary_op_typing}.

  Definition typed_unary_op τin τout := {u:unary_op|unary_op_type u τin τout}.

  Definition tunary_op_eq {τin τout} (uop1 uop2:typed_unary_op τin τout) : Prop :=
    forall (x:data),
      data_type x τin ->
      (unary_op_eval brand_relation_brands (`uop1)) x
      = (unary_op_eval brand_relation_brands (`uop2)) x.
  
  Global Instance tunary_op_equiv {τin τout} : Equivalence (@tunary_op_eq τin τout).
  Proof.
    constructor.
    - unfold Reflexive, tunary_op_eq.
      intros; reflexivity.
    - unfold Symmetric, tunary_op_eq.
      intros; rewrite (H x0); [reflexivity|assumption].
    - unfold Transitive, tunary_op_eq.
      intros;
        rewrite (H x0); try assumption;
        rewrite (H0 x0); [reflexivity|assumption].
  Qed.

  Definition tunary_op_rewrites_to (u1 u2:unary_op) :=
    forall τ₁ τ₂,
    unary_op_type u1 τ₁ τ₂ ->
    unary_op_type u2 τ₁ τ₂ /\
    (forall (x:data),
        data_type x τ₁ ->
        (unary_op_eval brand_relation_brands u1) x
        = (unary_op_eval brand_relation_brands u2) x).

  Global Instance tunary_op_rewrites_to_pre : PreOrder tunary_op_rewrites_to.
  Proof.
    unfold tunary_op_rewrites_to.
    constructor; red.
    - intuition.
    - intros x y z Hx Hy; intros ? ? typx.
      specialize (Hx _ _ typx).
      destruct Hx as [typy Hx].
      specialize (Hy _ _ typy).
      destruct Hy as [typz Hy].
      split; trivial; intros.
      rewrite Hx, Hy; trivial.
  Qed.
  
  Definition typed_binary_op τ₁ τ₂ τout := {b:binary_op|binary_op_type b τ₁ τ₂ τout}.

  Definition tbinary_op_eq {τ₁ τ₂ τout} (bop1 bop2:typed_binary_op τ₁ τ₂ τout) : Prop :=
    forall (x1 x2:data),
      data_type x1 τ₁ -> data_type x2 τ₂ -> 
      (binary_op_eval brand_relation_brands (`bop1)) x1 x2
      = (binary_op_eval brand_relation_brands (`bop2)) x1 x2.

  Global Instance tbinary_op_equiv {τ₁ τ₂ τout} : Equivalence (@tbinary_op_eq τ₁ τ₂ τout).
  Proof.
    constructor.
    - unfold Reflexive, tbinary_op_eq.
      intros; reflexivity.
    - unfold Symmetric, tbinary_op_eq.
      intros; rewrite (H x1 x2); try assumption; reflexivity.
    - unfold Transitive, tbinary_op_eq.
      intros;
        rewrite (H x1 x2); try assumption;
          rewrite (H0 x1 x2); try assumption; reflexivity.
  Qed.

  Definition tbinary_op_rewrites_to (b1 b2:binary_op) :=
    forall τ₁ τ₂ τ₃,
    binary_op_type b1 τ₁ τ₂ τ₃ ->
    binary_op_type b2 τ₁ τ₂ τ₃ /\
    (forall (x1 x2:data),
        data_type x1 τ₁ ->
        data_type x2 τ₂ ->
        (binary_op_eval brand_relation_brands b1) x1 x2
        = (binary_op_eval brand_relation_brands b2) x1 x2).

  Global Instance tbinary_op_rewrites_to_pre : PreOrder tbinary_op_rewrites_to.
  Proof.
    unfold tbinary_op_rewrites_to.
    constructor; red.
    - intuition.
    - intros x y z Hx Hy; intros ? ? ? typx.
      specialize (Hx _ _ _ typx).
      destruct Hx as [typy Hx].
      specialize (Hy _ _ _ typy).
      destruct Hy as [typz Hy].
      split; trivial; intros.
      rewrite Hx, Hy; trivial.
  Qed.
  
End TOperatorsEq.

