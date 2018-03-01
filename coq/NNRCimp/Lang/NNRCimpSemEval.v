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

Section NNRCimpSemEval.
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

  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).
  Context (σc:list (string*data)).

  Local Open Scope nnrc_imp.
  Local Open Scope string.

  Lemma nnrc_imp_expr_sem_eval σ e d :
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

  Lemma nnrc_imp_stmt_sem_eval σ₁ ψc₁ ψd₁ s σ₂ ψc₂ ψd₂ :
    [ h , σc ⊢ s, σ₁, ψc₁ , ψd₁ ⇓ σ₂, ψc₂ , ψd₂ ] <-> nnrc_imp_stmt_eval h σc σ₁ ψc₁ ψd₁ s = Some (σ₂, ψc₂, ψd₂).
  Proof.
    split; revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
    - {
        nnrc_imp_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; invcs sem; simpl; trivial.
        - Case "NNRCimpSeq".
          erewrite IHs1 by eauto.
          eauto.
        - Case "NNRCimpLet".
          apply nnrc_imp_expr_sem_eval in H8; rewrite H8.
          erewrite IHs by eauto.
          simpl; trivial.
        - Case "NNRCimpLetMut".
          erewrite IHs1 by eauto; simpl.
          erewrite IHs2 by eauto; simpl; trivial.
        - Case "NNRCimpLetMutColl".
          erewrite IHs1 by eauto; simpl.
          erewrite IHs2 by eauto; simpl; trivial.
        - Case "NNRCimpAssign".
          rewrite nnrc_imp_expr_sem_eval in H8; rewrite H8.
          rewrite H1; simpl; trivial.
        - Case "NNRCimpPush".
          rewrite nnrc_imp_expr_sem_eval in H8; rewrite H8.
          rewrite H1; simpl; trivial.
        - Case "NNRCimpFor".
          rewrite nnrc_imp_expr_sem_eval in H8; rewrite H8; clear H8.
          revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ H9.
          induction dl; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ seval; invcs seval; trivial.
          erewrite IHs by eauto; simpl.
          eauto.
        - Case "NNRCimpIf".
          rewrite nnrc_imp_expr_sem_eval in H8; rewrite H8.
          eauto.
        - Case "NNRCimpIf".
          rewrite nnrc_imp_expr_sem_eval in H8; rewrite H8.
          eauto.
        - Case "NNRCimpEither".
          rewrite nnrc_imp_expr_sem_eval in H10; rewrite H10.
          erewrite IHs1 by eauto.
          simpl; trivial.
        - Case "NNRCimpEither".
          rewrite nnrc_imp_expr_sem_eval in H10; rewrite H10.
          erewrite IHs2 by eauto.
          simpl; trivial.
      }
    - {
        Hint Constructors nnrc_imp_stmt_sem.
        Hint Constructors nnrc_imp_stmt_sem_iter.
        Hint Resolve nnrc_imp_stmt_sem_env_cons_same.
        Hint Resolve nnrc_imp_stmt_sem_mcenv_cons_same.

        nnrc_imp_stmt_cases (induction s) Case; simpl; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; repeat destr sem.
        - Case "NNRCimpSeq".
          eauto.
        - Case "NNRCimpLet".
          invcs sem.
          apply nnrc_imp_expr_sem_eval in eqq.
          eauto.
        - Case "NNRCimpLetMut".
          invcs sem.
          apply IHs1 in eqq.
          apply nnrc_imp_stmt_sem_mdenv_cons_same in eqq.
          eauto.
        - Case "NNRCimpLetMutColl".
          invcs sem.
          apply IHs1 in eqq.
          apply nnrc_imp_stmt_sem_mcenv_cons_same in eqq.
          eauto.
        - Case "NNRCimpAssign".
          invcs sem.
          apply nnrc_imp_expr_sem_eval in eqq.
          eauto.
        - Case "NNRCimpPush".
          invcs sem.
          apply nnrc_imp_expr_sem_eval in eqq.
          eauto.
        - Case "NNRCimpFor".
          destruct d; try discriminate.
          apply nnrc_imp_expr_sem_eval in eqq.
          econstructor; eauto.
          clear eqq.
          revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem.
          induction l; intros σ₁  ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; invcs sem; eauto 1.
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

  Lemma nnrc_imp_sem_eval q d :
    [ h , σc ⊢ q ⇓ d ] <-> nnrc_imp_eval_top h σc q = Some d.
  Proof.
    destruct q.
    unfold nnrc_imp_eval_top.
    split; intros hyp.
    - invcs hyp.
      apply nnrc_imp_stmt_sem_eval in H.
      simpl in H.
      rewrite H; trivial.
    - destr hyp.
      destruct p.
      destruct m; try discriminate.
      destruct p0.
      destruct o; try discriminate.
      apply nnrc_imp_stmt_sem_eval in eqq.
      invcs hyp.
      generalize (nnrc_imp_stmt_sem_env_stack eqq).
      simpl; intros eqq2; invcs eqq2.
      symmetry in H0; apply domain_nil in H0; subst.
      generalize (nnrc_imp_stmt_sem_mcenv_stack eqq).
      simpl; intros eqq2.
      symmetry in eqq2; apply domain_nil in eqq2; subst.
      generalize (nnrc_imp_stmt_sem_mdenv_stack eqq).
      simpl; intros eqq2.
      invcs eqq2.
      symmetry in H1; apply domain_nil in H1; subst.
      constructor; simpl; trivial.
  Qed.

End NNRCimpSemEval.
