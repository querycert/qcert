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

Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import List.
Require Import String.
Require Import CommonSystem.
Require Import NRA.
Require Import NRAEq.
Require Import TNRA.

Section TNRAEq.
  Local Open Scope nra_scope.

  (* Equivalence relation between *typed* algebraic plans.  Two
     well-typed plans are equivalent iff they return the same value
     for every well-typed input.  *)

  Context {m:basic_model}.
  Definition typed_nra τc τin τout := {op:nra|op ▷ τin >=> τout ⊣ τc}.

  Definition tnra_eq {τc} {τin τout} (op1 op2:typed_nra τc τin τout) : Prop :=
    forall (x:data) c
           (dt_x:x ▹ τin)
           (dt_c:bindings_type c τc),
      brand_relation_brands ⊢ (proj1_sig op1) @ₐ x ⊣ c
                 = brand_relation_brands ⊢ (proj1_sig op2) @ₐ x ⊣ c.

  Global Instance tnra_equiv {τc} {τin τout:rtype} : Equivalence (@tnra_eq τc τin τout).
  Proof.
    constructor.
    - unfold Reflexive, tnra_eq.
      intros; reflexivity.
    - unfold Symmetric, tnra_eq.
      intros; rewrite (H x0 c dt_x dt_c); reflexivity.
    - unfold Transitive, tnra_eq.
      intros; rewrite (H x0 c dt_x dt_c); rewrite (H0 x0 c dt_x dt_c); reflexivity.
  Qed.

  Notation "t1 ⇝ t2 ⊣ τc" := (typed_nra τc t1 t2) (at level 80).                        (* ≡ = \equiv *)
  Notation "X ≡τ Y" := (tnra_eq X Y) (at level 80).                             (* ≡ = \equiv *)

  Hint Resolve data_type_normalized.
  Hint Resolve bindings_type_Forall_normalized.

  Lemma nra_eq_impl_tnra_eq {τc} {τin τout} (op1 op2: τin ⇝ τout ⊣ τc) :
    `op1 ≡ₐ `op2 -> op1 ≡τ op2.
  Proof.
    unfold tnra_eq, nra_eq; intros.
    eapply H; eauto.
  Qed.

  Lemma nra_eq_pf_irrel {op} {τc} {τin τout} (pf1 pf2: op ▷ τin >=> τout ⊣ τc) :
    tnra_eq (exist _ _ pf1) (exist _ _ pf2).
  Proof.
    red; intros; simpl.
    reflexivity.
  Qed.

  (* A different kind of type-based rewrite *)

  Definition tnra_rewrites_to {τc} {τin τout} (op1 op2:nra) : Prop :=
    op1 ▷ τin >=> τout ⊣ τc ->
    (op2 ▷ τin >=> τout ⊣ τc) /\ (forall (x:data) c
                                         (dt_x:x ▹ τin)
                                         (dt_c:bindings_type c τc),
                                     brand_relation_brands ⊢ op1 @ₐ x ⊣ c = brand_relation_brands ⊢ op2 @ₐ x ⊣ c).
  
  Notation "A ↦ₐ B ⊣ C ⊧ op1 ⇒ op2" := (@tnra_rewrites_to C A B op1 op2) (at level 80).

  Lemma rewrites_typed_and_untyped {τc} {τin τout} (op1 op2:nra):
    (op1 ▷ τin >=> τout ⊣ τc -> op2 ▷ τin >=> τout ⊣ τc) -> op1 ≡ₐ op2 -> τin ↦ₐ τout ⊣ τc ⊧ op1 ⇒ op2.
  Proof.
    intros.
    unfold tnra_rewrites_to; simpl; intros.
    split; eauto.
  Qed.

  Lemma tnra_rewrites_eq_is_typed_eq {τc} {τin τout:rtype} (op1 op2:typed_nra τc τin τout):
    (τin ↦ₐ τout ⊣ τc ⊧ `op1 ⇒ `op2) -> op1 ≡τ op2.
  Proof.
    unfold tnra_rewrites_to, tnra_eq; intros.
    elim H; clear H; intros.
    apply (H0 x c dt_x dt_c).
    dependent induction op1; simpl.
    assumption.
  Qed.

  Lemma tnra_typed_eq_and_type_propag {τc} {τin τout:rtype} (op1 op2:typed_nra τc τin τout):
    op1 ≡τ op2 ->
    ((`op1) ▷ τin >=> τout ⊣ τc -> (`op2) ▷ τin >=> τout ⊣ τc) -> τin ↦ₐ τout ⊣ τc ⊧ (`op1) ⇒ (`op2).
  Proof.
    unfold tnra_rewrites_to, tnra_eq; intros.
    split.
    apply H0; assumption.
    assumption.
  Qed.

End TNRAEq.

Notation "m ⊢ₐ A ↦ B ⊣ C ⊧ op1 ⇒ op2" := (@tnra_rewrites_to m C A B op1 op2) (at level 80).

Notation "t1 ⇝ t2 ⊣ tc" := (typed_nra tc t1 t2) (at level 80).
Notation "X ≡τ Y" := (tnra_eq X Y) (at level 80).                             (* ≡ = \equiv *)
Notation "X ≡τ' Y" := (tnra_eq (exist _ _ X) (exist _ _ Y)) (at level 80).    (* ≡ = \equiv *)

