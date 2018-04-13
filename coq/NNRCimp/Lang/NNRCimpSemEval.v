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

(** NNRCimp is a variant of the named nested relational calculus
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
Require Import NNRCimp.
Require Import NNRCimpSem.
Require Import NNRCimpEval.

Section NNRCimpSemEval.

  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  Local Open Scope nnrc_imp.
  Local Open Scope string.

  Lemma nnrc_imp_expr_sem_eval σc σ e d :
    [ h , σc ; σ ⊢ e ⇓ d ] <-> nnrc_imp_expr_eval h σc σ e = Some d.
  Proof.
    split; revert σ d.
    - {
        nnrc_imp_expr_cases (induction e) Case; intros σ d₀ sem; invcs sem; simpl; trivial.
        - Case "NNRCimpVar".
          rewrite H1; simpl; reflexivity.
        - Case "NNRCimpBinop".
          erewrite IHe1 by eauto.
          erewrite IHe2 by eauto.
          simpl; trivial.
        - Case "NNRCimpUnop".
          erewrite IHe by eauto.
          simpl; trivial.
        - Case "NNRCimpGroupBy".
          erewrite IHe by eauto.
          simpl; rewrite H5; simpl; trivial.
      }
    - {
        Hint Constructors nnrc_imp_expr_sem.
        nnrc_imp_expr_cases (induction e) Case; intros σ d₀ sem; invcs sem; simpl; trivial; eauto 3.
        - Case "NNRCimpVar".
          apply some_olift in H0.
          destruct H0 as [??]; unfold id in *; subst.
          eauto.
        - Case "NNRCimpBinop".
          apply some_olift2 in H0.
          destruct H0 as [?[?? [??]]].
          eauto.
        - Case "NNRCimpUnop".
          apply some_olift in H0.
          destruct H0 as [??]; unfold id in *; subst.
          eauto.
        - Case "NNRCimpGroupBy".
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

  Lemma nnrc_imp_stmt_sem_eval σc s σ₁ σ₂ :
    [ h , σc ⊢ s, σ₁ ⇓ σ₂ ] <-> nnrc_imp_stmt_eval h σc s σ₁ = Some σ₂.
  Proof.
    split; revert σ₁ σ₂.
    - {
        nnrc_imp_stmt_cases (induction s) Case; intros σ₁ σ₂ sem; invcs sem; simpl; trivial.
        - Case "NNRCimpSeq".
          erewrite IHs1 by eauto.
          eauto.
        - Case "NNRCimpAssign".
          rewrite nnrc_imp_expr_sem_eval in H4; rewrite H4.
          apply in_dom_lookup with (dec := string_dec) in H1.
          destruct H1 as [? eqq1]; rewrite eqq1; trivial.
        - Case "NNRCimpLet".
          erewrite IHs by eauto.
          simpl; trivial.
        - Case "NNRCimpLet".
          apply nnrc_imp_expr_sem_eval in H4; rewrite H4; simpl.
          erewrite IHs by eauto.
          simpl; trivial.
        - Case "NNRCimpFor".
          rewrite nnrc_imp_expr_sem_eval in H4; rewrite H4; clear H4.
          revert σ₁ σ₂ H5.
          induction dl; intros σ₁ σ₂ seval; invcs seval; trivial.
          erewrite IHs by eauto; simpl.
          eauto.
        - Case "NNRCimpIf".
          rewrite nnrc_imp_expr_sem_eval in H4; rewrite H4.
          eauto.
        - Case "NNRCimpIf".
          rewrite nnrc_imp_expr_sem_eval in H4; rewrite H4.
          eauto.
        - Case "NNRCimpEither".
          rewrite nnrc_imp_expr_sem_eval in H6; rewrite H6.
          erewrite IHs1 by eauto.
          simpl; trivial.
        - Case "NNRCimpEither".
          rewrite nnrc_imp_expr_sem_eval in H6; rewrite H6.
          erewrite IHs2 by eauto.
          simpl; trivial.
      }
    - {
        Hint Constructors nnrc_imp_stmt_sem.
        Hint Constructors nnrc_imp_stmt_sem_iter.
        Hint Resolve nnrc_imp_stmt_sem_env_cons_same.

        nnrc_imp_stmt_cases (induction s) Case; simpl; intros σ₁ σ₂ sem; repeat destr sem.
        - Case "NNRCimpSeq".
          apply some_olift in sem.
          destruct sem as [???].
          eauto.
        - Case "NNRCimpAssign".
          invcs sem.
          apply nnrc_imp_expr_sem_eval in eqq.
          apply lookup_in_domain in eqq0.
          eauto.
        - Case "NNRCimpLet".
          apply some_olift in sem.
          destruct sem as [? eqq1 eqq2].
          apply some_lift in eqq1.
          destruct eqq1 as [? eqq1 ?]; subst.
          match_option_in eqq2.
          destruct p; try discriminate.
          destruct p.
          invcs eqq2.
          apply nnrc_imp_expr_sem_eval in eqq1.
          eauto.
        - Case "NNRCimpLet".
          invcs sem.
          eauto.
        - Case "NNRCimpFor".
          destruct d; try discriminate.
          apply nnrc_imp_expr_sem_eval in eqq.
          econstructor; eauto.
          clear eqq.
          revert σ₁ σ₂ sem.
          induction l; intros σ₁ σ₂ sem; invcs sem; eauto 1.
          repeat destr H0.
          eauto.
        - Case "NNRCimpIf".
          apply nnrc_imp_expr_sem_eval in eqq.
          destruct d; try discriminate.
          destruct b; eauto.
        - Case "NNRCimpEither".
          apply nnrc_imp_expr_sem_eval in eqq.
          destruct d; try discriminate;
            repeat destr sem; invcs sem; eauto.
      }
  Qed.

  Theorem nnrc_imp_sem_eval σc q d :
    [ h , σc ⊢ q ⇓ d ] <-> nnrc_imp_eval h σc q = Some d.
  Proof.
    destruct q.
    unfold nnrc_imp_eval.
    split; intros hyp.
    - invcs hyp.
      apply nnrc_imp_stmt_sem_eval in H.
      simpl in H.
      rewrite H; trivial.
    - destr hyp.
      destruct p; try discriminate.
      destruct p.
      invcs hyp.
      apply nnrc_imp_stmt_sem_eval in eqq.
      generalize (nnrc_imp_stmt_sem_env_stack eqq).
      simpl; intros eqq2; invcs eqq2.
      symmetry in H1; apply domain_nil in H1; subst.
      constructor; simpl; trivial.
  Qed.

  Theorem nnrc_imp_sem_eval_top σc q d :
    [ h , (rec_sort σc) ⊢ q ⇓ Some d ] <-> nnrc_imp_eval_top h σc q = Some d.
  Proof.
    destruct q.
    unfold nnrc_imp_eval_top, nnrc_imp_sem_top.
    rewrite nnrc_imp_sem_eval.
    unfold olift.
    match_destr; unfold id; simpl; intuition congruence.
  Qed.

  Section Core.
    Theorem nnrc_imp_core_sem_eval σc q d :
      [ h , σc ⊢ q ⇓ᶜ d ] <-> nnrc_imp_core_eval h σc q = Some d.
    Proof.
      destruct q; simpl.
      apply nnrc_imp_sem_eval.
    Qed.

    Theorem nnrc_imp_core_sem_eval_top σc q d :
      [ h , (rec_sort σc) ⊢ q ⇓ᶜ Some d ] <-> nnrc_imp_core_eval_top h σc q = Some d.
    Proof.
      destruct q; simpl.
      apply nnrc_imp_sem_eval_top.
    Qed.

  End Core.

End NNRCimpSemEval.
