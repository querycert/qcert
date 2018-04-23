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

(** NNRCimpish is a variant of the named nested relational calculus
     (NNRC) that is meant to be more imperative in feel.  It is used
     as an intermediate language between NNRC and more imperative /
     statement oriented backends *)

Require Import String.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Arith.
Require Import Max.
Require Import Bool.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRCimpish.
Require Import NNRCimpishSem.
Require Import NNRCimpishEval.

Section NNRCimpishSemEval.
  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  Local Open Scope nnrc_impish.
  Local Open Scope string.

  Lemma nnrc_impish_expr_sem_eval σc σ e d :
    [ h , σc ; σ ⊢ e ⇓ d ] <-> nnrc_impish_expr_eval h σc σ e = Some d.
  Proof.
    split; revert σ d.
    - {
        nnrc_impish_expr_cases (induction e) Case; intros σ d₀ sem; invcs sem; simpl; trivial.
        - Case "NNRCimpishVar".
          rewrite H1; simpl; reflexivity.
        - Case "NNRCimpishBinop".
          erewrite IHe1 by eauto.
          erewrite IHe2 by eauto.
          simpl; trivial.
        - Case "NNRCimpishUnop".
          erewrite IHe by eauto.
          simpl; trivial.
        - Case "NNRCimpishGroupBy".
          erewrite IHe by eauto.
          simpl; rewrite H5; simpl; trivial.
      }
    - {
        Hint Constructors nnrc_impish_expr_sem.
        nnrc_impish_expr_cases (induction e) Case; intros σ d₀ sem; invcs sem; simpl; trivial; eauto 3.
        - Case "NNRCimpishVar".
          apply some_olift in H0.
          destruct H0 as [??]; unfold id in *; subst.
          eauto.
        - Case "NNRCimpishBinop".
          apply some_olift2 in H0.
          destruct H0 as [?[?? [??]]].
          eauto.
        - Case "NNRCimpishUnop".
          apply some_olift in H0.
          destruct H0 as [??]; unfold id in *; subst.
          eauto.
        - Case "NNRCimpishGroupBy".
          match_case_in H0;
            [intros ? eqq | intros eqq]; rewrite eqq in H0;
              try discriminate.
          destruct d; try discriminate.
          apply some_olift in H0.
          destruct H0 as [??]; unfold id in *; subst.
          invcs e1.
          eauto.
      }
  Qed.

  Ltac destr H :=
    let eqq := fresh "eqq" in
    first [
        match goal with
          [H:  _ * _ |- _ ] => destruct H
        end |
        (match_case_in H;
         [intros [???] eqq | intros eqq]; rewrite eqq in H; try discriminate)
        | (match_case_in H;
           [intros [??] eqq | intros eqq]; rewrite eqq in H; try discriminate)
        | (match_case_in H;
           [intros ?? eqq | intros eqq]; rewrite eqq in H; try discriminate)
        | (match_case_in H;
           [intros ? eqq | intros eqq]; rewrite eqq in H; try discriminate)
        | (match_case_in H;
           [intros eqq | intros ? ? eqq]; try rewrite eqq in H; try discriminate)
        | (match_case_in H;
           [intros eqq | intros ? eqq]; try rewrite eqq in H; try discriminate)
      ]; subst.

  Lemma nnrc_impish_stmt_sem_eval σc σ₁ ψc₁ ψd₁ s σ₂ ψc₂ ψd₂ :
    [ h , σc ⊢ s, σ₁, ψc₁ , ψd₁ ⇓ σ₂, ψc₂ , ψd₂ ] <-> nnrc_impish_stmt_eval h σc σ₁ ψc₁ ψd₁ s = Some (σ₂, ψc₂, ψd₂).
  Proof.
    split; revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
    - {
        nnrc_impish_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; invcs sem; simpl; trivial.
        - Case "NNRCimpishSeq".
          erewrite IHs1 by eauto.
          eauto.
        - Case "NNRCimpishLet".
          apply nnrc_impish_expr_sem_eval in H8; rewrite H8.
          erewrite IHs by eauto.
          simpl; trivial.
        - Case "NNRCimpishLetMut".
          erewrite IHs1 by eauto; simpl.
          erewrite IHs2 by eauto; simpl; trivial.
        - Case "NNRCimpishLetMutColl".
          erewrite IHs1 by eauto; simpl.
          erewrite IHs2 by eauto; simpl; trivial.
        - Case "NNRCimpishAssign".
          rewrite nnrc_impish_expr_sem_eval in H8; rewrite H8.
          rewrite H1; simpl; trivial.
        - Case "NNRCimpishPush".
          rewrite nnrc_impish_expr_sem_eval in H8; rewrite H8.
          rewrite H1; simpl; trivial.
        - Case "NNRCimpishFor".
          rewrite nnrc_impish_expr_sem_eval in H8; rewrite H8; clear H8.
          revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ H9.
          induction dl; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ seval; invcs seval; trivial.
          erewrite IHs by eauto; simpl.
          eauto.
        - Case "NNRCimpishIf".
          rewrite nnrc_impish_expr_sem_eval in H8; rewrite H8.
          eauto.
        - Case "NNRCimpishIf".
          rewrite nnrc_impish_expr_sem_eval in H8; rewrite H8.
          eauto.
        - Case "NNRCimpishEither".
          rewrite nnrc_impish_expr_sem_eval in H10; rewrite H10.
          erewrite IHs1 by eauto.
          simpl; trivial.
        - Case "NNRCimpishEither".
          rewrite nnrc_impish_expr_sem_eval in H10; rewrite H10.
          erewrite IHs2 by eauto.
          simpl; trivial.
      }
    - {
        Hint Constructors nnrc_impish_stmt_sem.
        Hint Constructors nnrc_impish_stmt_sem_iter.
        Hint Resolve nnrc_impish_stmt_sem_env_cons_same.
        Hint Resolve nnrc_impish_stmt_sem_mcenv_cons_same.

        nnrc_impish_stmt_cases (induction s) Case; simpl; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; repeat destr sem.
        - Case "NNRCimpishSeq".
          eauto.
        - Case "NNRCimpishLet".
          invcs sem.
          apply nnrc_impish_expr_sem_eval in eqq.
          eauto.
        - Case "NNRCimpishLetMut".
          invcs sem.
          apply IHs1 in eqq.
          apply nnrc_impish_stmt_sem_mdenv_cons_same in eqq.
          eauto.
        - Case "NNRCimpishLetMutColl".
          invcs sem.
          apply IHs1 in eqq.
          apply nnrc_impish_stmt_sem_mcenv_cons_same in eqq.
          eauto.
        - Case "NNRCimpishAssign".
          invcs sem.
          apply nnrc_impish_expr_sem_eval in eqq.
          eauto.
        - Case "NNRCimpishPush".
          invcs sem.
          apply nnrc_impish_expr_sem_eval in eqq.
          eauto.
        - Case "NNRCimpishFor".
          destruct d; try discriminate.
          apply nnrc_impish_expr_sem_eval in eqq.
          econstructor; eauto.
          clear eqq.
          revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem.
          induction l; intros σ₁  ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; invcs sem; eauto 1.
          repeat destr H0.
          eauto.
        - Case "NNRCimpishIf".
          apply nnrc_impish_expr_sem_eval in eqq.
          destruct d; try discriminate.
          destruct b; eauto.
        - Case "NNRCimpishEither".
          apply nnrc_impish_expr_sem_eval in eqq.
          destruct d; try discriminate;
            repeat destr sem; invcs sem; eauto.
      }
  Qed.

  Theorem nnrc_impish_sem_eval σc q d :
    [ h , σc ⊢ q ⇓ d ] <-> nnrc_impish_eval h σc q = Some d.
  Proof.
    destruct q.
    unfold nnrc_impish_eval.
    split; intros hyp.
    - invcs hyp.
      apply nnrc_impish_stmt_sem_eval in H.
      simpl in H.
      rewrite H; trivial.
    - destr hyp.
      destruct p.
      destruct m; try discriminate.
      destruct p0.
      invcs hyp.
      apply nnrc_impish_stmt_sem_eval in eqq.
      generalize (nnrc_impish_stmt_sem_env_stack eqq).
      simpl; intros eqq2; invcs eqq2.
      symmetry in H0; apply domain_nil in H0; subst.
      generalize (nnrc_impish_stmt_sem_mcenv_stack eqq).
      simpl; intros eqq2.
      symmetry in eqq2; apply domain_nil in eqq2; subst.
      generalize (nnrc_impish_stmt_sem_mdenv_stack eqq).
      simpl; intros eqq2.
      invcs eqq2.
      symmetry in H1; apply domain_nil in H1; subst.
      constructor; simpl; trivial.
  Qed.

  Theorem nnrc_impish_sem_eval_top σc q d :
    [ h , (rec_sort σc) ⊢ q ⇓ Some d ] <-> nnrc_impish_eval_top h σc q = Some d.
  Proof.
    destruct q.
    unfold nnrc_impish_eval_top, nnrc_impish_sem_top.
    rewrite nnrc_impish_sem_eval.
    unfold olift.
    match_destr; unfold id; simpl; intuition congruence.
  Qed.

  Section Core.
    Theorem nnrc_impish_core_sem_eval σc q d :
      [ h , σc ⊢ q ⇓ᶜ d ] <-> nnrc_impish_core_eval h σc q = Some d.
    Proof.
      destruct q; simpl.
      apply nnrc_impish_sem_eval.
    Qed.

    Theorem nnrc_impish_core_sem_eval_top σc q d :
      [ h , (rec_sort σc) ⊢ q ⇓ᶜ Some d ] <-> nnrc_impish_core_eval_top h σc q = Some d.
    Proof.
      destruct q; simpl.
      apply nnrc_impish_sem_eval_top.
    Qed.

  End Core.

End NNRCimpishSemEval.
