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
Require Import Compare_dec.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRSimp.
Require Import NNRSimpNorm.
Require Import NNRSimpEval.


Section NNRSimpEq.
  (* Equivalence for nnrs_imp *)

  Local Open Scope nnrs_imp_scope.

  Context {fruntime:foreign_runtime}.

  Definition nnrs_imp_expr_eq (e₁ e₂:nnrs_imp_expr) : Prop :=
    forall (h:list(string*string))
           (σc:list (string*data))
           (dn_σc: Forall (data_normalized h) (map snd σc))
           (σ:pd_bindings)
           (dn_σ: forall d, In (Some d) (map snd σ) -> data_normalized h d),
      nnrs_imp_expr_eval h σc σ e₁ = nnrs_imp_expr_eval h σc σ e₂.

  Definition nnrs_imp_stmt_eq (s₁ s₂:nnrs_imp_stmt) : Prop :=
    forall (h:list(string*string))
           (σc:list (string*data))
           (dn_σc: Forall (data_normalized h) (map snd σc))
           (σ:pd_bindings)
           (dn_σ: forall d, In (Some d) (map snd σ) -> data_normalized h d),
      nnrs_imp_stmt_eval h σc s₁ σ = nnrs_imp_stmt_eval h σc s₂ σ.
  
  Definition nnrs_imp_eq (si₁ si₂:nnrs_imp) : Prop :=
    forall (h:list(string*string))
           (σc:list (string*data))
           (dn_σc: Forall (data_normalized h) (map snd σc)),
      nnrs_imp_eval h σc si₁ = nnrs_imp_eval h σc si₂.

  Global Instance nnrs_imp_expr_equiv : Equivalence nnrs_imp_expr_eq.
  Proof.
    unfold nnrs_imp_expr_eq. 
    constructor; red; intros.
    - reflexivity.
    - symmetry; eauto.
    - rewrite H; eauto. 
  Qed.

  Global Instance nnrs_imp_stmt_equiv : Equivalence nnrs_imp_stmt_eq.
  Proof.
    unfold nnrs_imp_stmt_eq. 
    constructor; red; intros.
    - reflexivity.
    - symmetry; eauto.
    - rewrite H; eauto. 
  Qed.

  Global Instance nnrs_imp_equiv : Equivalence nnrs_imp_eq.
  Proof.
    unfold nnrs_imp_eq. 
    constructor; red; intros.
    - reflexivity.
    - symmetry; eauto.
    - rewrite H; eauto. 
  Qed.

  Section proper.

    Global Instance NNRSimpGetConstant_proper v :
      Proper nnrs_imp_expr_eq (NNRSimpGetConstant v).
    Proof.
      unfold Proper, respectful, nnrs_imp_expr_eq; trivial.
    Qed.

    Global Instance NNRSimpVar_proper v :
      Proper nnrs_imp_expr_eq (NNRSimpVar v).
    Proof.
      unfold Proper, respectful, nnrs_imp_expr_eq; trivial.
    Qed.

    Global Instance NNRSimpConst_proper d :
      Proper nnrs_imp_expr_eq (NNRSimpConst d).
    Proof.
      unfold Proper, respectful, nnrs_imp_expr_eq; trivial.
    Qed.

    Global Instance NNRSimpBinop_proper :
      Proper (binary_op_eq ==> nnrs_imp_expr_eq ==> nnrs_imp_expr_eq ==> nnrs_imp_expr_eq) NNRSimpBinop.
    Proof.
      unfold Proper, respectful, nnrs_imp_expr_eq; intros; simpl.
      rewrite H0, H1 by trivial.
      apply olift2_ext; intros.
      apply H
      ; eapply nnrs_imp_expr_eval_normalized; eauto.
    Qed.

    Global Instance NNRSimpUnop_proper :
      Proper (unary_op_eq ==> nnrs_imp_expr_eq ==> nnrs_imp_expr_eq) NNRSimpUnop.
    Proof.
      unfold Proper, respectful, nnrs_imp_expr_eq; intros; simpl.
      rewrite H0 by trivial.
      apply olift_ext; intros.
      apply H
      ; eapply nnrs_imp_expr_eval_normalized; eauto.
    Qed.

    Global Instance NNRSimpGroupBy_proper s ls :
      Proper (nnrs_imp_expr_eq ==> nnrs_imp_expr_eq) (NNRSimpGroupBy s ls).
    Proof.
      unfold Proper, respectful, nnrs_imp_expr_eq; intros; simpl.
      rewrite H; trivial.
    Qed.

    Global Instance NNRSimpSeq_proper :
      Proper (nnrs_imp_stmt_eq ==> nnrs_imp_stmt_eq ==> nnrs_imp_stmt_eq) NNRSimpSeq.
    Proof.
      unfold Proper, respectful, nnrs_imp_stmt_eq; intros; simpl.
      rewrite H by trivial.
      apply olift_ext; intros.
      apply H0; trivial.
      eapply nnrs_imp_stmt_eval_normalized; eauto.
    Qed.

    Global Instance NNRSimpAssign_proper v :
      Proper (nnrs_imp_expr_eq ==> nnrs_imp_stmt_eq) (NNRSimpAssign v).
    Proof.
      unfold Proper, respectful, nnrs_imp_stmt_eq; intros; simpl.
      rewrite H; trivial.
    Qed.

    Global Instance NNRSimpLet_proper v :
      Proper (lift2P nnrs_imp_expr_eq ==> nnrs_imp_stmt_eq ==> nnrs_imp_stmt_eq) (NNRSimpLet v).
    Proof.
      unfold Proper, respectful, nnrs_imp_stmt_eq; intros; simpl.
      unfold lift2P in H.
      destruct x; destruct y; try contradiction; trivial.
      - rewrite H; eauto 2.
        apply olift_ext; simpl; intros ? eqq.
        rewrite H0; trivial; simpl.
        apply some_lift in eqq.
        destruct eqq as [???]; subst.
        intuition.
        invcs H2; eauto.
      - rewrite H0; trivial; simpl.
        intuition; try discriminate.
    Qed.

    Global Instance NNRSimpLet_none_proper v :
      Proper (nnrs_imp_stmt_eq ==> nnrs_imp_stmt_eq) (NNRSimpLet v None).
    Proof.
      apply NNRSimpLet_proper.
      simpl; trivial.
    Qed.

    Global Instance NNRSimpFor_proper v :
      Proper (nnrs_imp_expr_eq ==> nnrs_imp_stmt_eq ==> nnrs_imp_stmt_eq) (NNRSimpFor v).
    Proof.
      unfold Proper, respectful, nnrs_imp_stmt_eq; intros; simpl.
      rewrite H; eauto 2.
      apply olift_ext; simpl; intros ? eqq.
      destruct a; trivial.
      eapply nnrs_imp_expr_eval_normalized in eqq; eauto.
      invcs eqq.
      revert σ dn_σ.
      induction l; simpl; trivial; intros σ dn_σ.
      invcs H2.
      rewrite H0; simpl; trivial.
      - repeat (match_case; intros); subst.
        apply IHl; trivial; intros.
        eapply nnrs_imp_stmt_eval_normalized; eauto; simpl
        ; intuition.
        invcs H7; trivial.
      - intuition.
        invcs H3; trivial.
    Qed.

    Global Instance NNRSimpIf_proper :
      Proper (nnrs_imp_expr_eq ==> nnrs_imp_stmt_eq ==> nnrs_imp_stmt_eq ==> nnrs_imp_stmt_eq) NNRSimpIf.
    Proof.
      unfold Proper, respectful, nnrs_imp_stmt_eq; intros; simpl.
      rewrite H; eauto 2.
      match_case; intros ? eqq.
      destruct d; trivial.
      destruct b; eauto.
    Qed.

    Global Instance NNRSimpEither_proper :
      Proper (nnrs_imp_expr_eq ==> eq ==> nnrs_imp_stmt_eq ==> eq ==> nnrs_imp_stmt_eq ==> nnrs_imp_stmt_eq) NNRSimpEither.
    Proof.
      unfold Proper, respectful, nnrs_imp_stmt_eq; intros; simpl.
      subst.
      rewrite H; eauto 2.
      match_case; intros ? eqq.
      eapply nnrs_imp_expr_eval_normalized in eqq; eauto.
      destruct d; trivial
      ; invcs eqq.
      - rewrite H1; eauto; simpl; intuition
        ; invcs H4; eauto.
      - rewrite H3; eauto; simpl; intuition
        ; invcs H4; eauto.
    Qed.      

    Lemma NNRSImp_proper {s₁ s₂} : nnrs_imp_stmt_eq s₁ s₂ ->
                                   forall v, nnrs_imp_eq (s₁, v) (s₂, v).
    Proof.
      unfold nnrs_imp_eq; intros eqq v; intros; simpl.
      rewrite eqq; trivial.
      simpl; intuition congruence.
    Qed.
    
  End proper.
  
End NNRSimpEq.

Notation "X ≡ᵉ Y" := (nnrs_imp_expr_eq X Y) (at level 90) : nnrs_imp. (* ≡ = \equiv *)

Notation "X ≡ˢ Y" := (nnrs_imp_stmt_eq X Y) (at level 90) : nnrs_imp. (* ≡ = \equiv *)

Notation "X ≡ˢⁱ Y" := (nnrs_imp_eq X Y) (at level 90) : nnrs_imp. (* ≡ = \equiv *)

