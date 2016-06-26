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

Section TAlgEq.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.

  Require Import List.
  Require Import String.

  Require Import Utils BasicSystem.

  Require Import RAlg RAlgEq.
  Require Import TAlg.

  Local Open Scope alg_scope.

  (* Equivalence relation between *typed* algebraic plans.  Two
     well-typed plans are equivalent iff they return the same value
     for every well-typed input.  *)

  Context {m:basic_model}.
  Definition typed_alg τin τout := {op:alg|op ▷ τin >=> τout}.

  Definition talg_eq {τin τout} (op1 op2:typed_alg τin τout) : Prop :=
    forall x:data, x ▹ τin -> brand_relation_brands ⊢ (proj1_sig op1) @ₐ x = brand_relation_brands ⊢ (proj1_sig op2) @ₐ x.

  Global Instance talg_equiv {τin τout:rtype} : Equivalence (@talg_eq τin τout).
  Proof.
    constructor.
    - unfold Reflexive, talg_eq.
      intros; reflexivity.
    - unfold Symmetric, talg_eq.
      intros; rewrite (H x0 H0); reflexivity.
    - unfold Transitive, talg_eq.
      intros; rewrite (H x0 H1); rewrite (H0 x0 H1); reflexivity.
  Qed.

  Notation "t1 ⇝ t2" := (typed_alg t1 t2) (at level 80).                        (* ≡ = \equiv *)
  Notation "X ≡τ Y" := (talg_eq X Y) (at level 80).                             (* ≡ = \equiv *)

  Lemma alg_eq_impl_talg_eq {τin τout} (op1 op2: τin ⇝ τout) :
    `op1 ≡ₐ `op2 -> op1 ≡τ op2.
  Proof.
    unfold talg_eq, alg_eq; intros.
    apply (H brand_relation_brands x).
    eauto.
  Qed.

  Lemma alg_eq_pf_irrel {op} {τin τout} (pf1 pf2: op ▷ τin >=> τout) :
    talg_eq (exist _ _ pf1) (exist _ _ pf2).
  Proof.
    red; intros; simpl.
    reflexivity.
  Qed.

  (* A different kind of type-based rewrite *)

  Definition talg_rewrites_to {τin τout} (op1 op2:alg) : Prop :=
    op1 ▷ τin >=> τout ->
    (op2 ▷ τin >=> τout) /\ (forall x:data, x ▹ τin -> brand_relation_brands ⊢ op1 @ₐ x = brand_relation_brands ⊢ op2 @ₐ x).
  
  Notation "A ↦ₐ B ⊧ op1 ⇒ op2" := (@talg_rewrites_to A B op1 op2) (at level 80).

  Lemma rewrites_typed_and_untyped {τin τout} (op1 op2:alg):
    (op1 ▷ τin >=> τout -> op2 ▷ τin >=> τout) -> op1 ≡ₐ op2 -> τin ↦ₐ τout ⊧ op1 ⇒ op2.
  Proof.
    intros.
    unfold talg_rewrites_to; simpl; intros.
    split; eauto.
  Qed.

  Lemma talg_rewrites_eq_is_typed_eq {τin τout:rtype} (op1 op2:typed_alg τin τout):
    (τin ↦ₐ τout ⊧ `op1 ⇒ `op2) -> op1 ≡τ op2.
  Proof.
    unfold talg_rewrites_to, talg_eq; intros.
    elim H; clear H; intros.
    apply (H1 x H0).
    dependent induction op1; simpl.
    assumption.
  Qed.

  Lemma talg_typed_eq_and_type_propag {τin τout:rtype} (op1 op2:typed_alg τin τout):
    op1 ≡τ op2 ->
    ((`op1) ▷ τin >=> τout -> (`op2) ▷ τin >=> τout) -> τin ↦ₐ τout ⊧ (`op1) ⇒ (`op2).
  Proof.
    unfold talg_rewrites_to, talg_eq; intros.
    split.
    apply H0; assumption.
    assumption.
  Qed.

End TAlgEq.

Notation "m ⊢ₐ A ↦ B ⊧ op1 ⇒ op2" := (@talg_rewrites_to m A B op1 op2) (at level 80).

Notation "t1 ⇝ t2" := (typed_alg t1 t2) (at level 80).
Notation "X ≡τ Y" := (talg_eq X Y) (at level 80).                             (* ≡ = \equiv *)
Notation "X ≡τ' Y" := (talg_eq (exist _ _ X) (exist _ _ Y)) (at level 80).    (* ≡ = \equiv *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
