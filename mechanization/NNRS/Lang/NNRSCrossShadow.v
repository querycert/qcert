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

(* Cross Shadowing is when a variable in one namespace "shadows" 
   a variable in another namespace.  This is not a problem for nnrs, since 
   the namespaces are all distinct.  However, it poses a problem when compiling to
   a language like nnrs_imp that has a single namespace.
 *)

Require Import String.
Require Import List.
Require Import Permutation.
Require Import ListSet.
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
Require Import NNRS.
Require Import NNRSEval.
Require Import NNRSVars.
Require Import NNRSRename.

Section NNRSCrossShadow.
  
  Context {fruntime:foreign_runtime}.

  Local Open Scope nnrs.

  (** The definition of the cross shadow free predicate.  This definition is used by
       the impish->imp translation.  If it holds, then collapsing namespaces is safe.
   *)
  Section def.
    
    Fixpoint nnrs_stmt_cross_shadow_free_under
             (s:nnrs_stmt)
             (σ ψc ψd:list var)
    : Prop
      := match s with
         | NNRSSeq s₁ s₂ =>
           nnrs_stmt_cross_shadow_free_under s₁ σ ψc ψd
           /\ nnrs_stmt_cross_shadow_free_under s₂ σ ψc ψd
         | NNRSLet v e s₀ =>
           disjoint (nnrs_expr_free_vars e) ψc
           /\ disjoint (nnrs_expr_free_vars e) ψd
           (* not the same: incl (nnrs_expr_free_vars e) σ *)
           /\ ~ In v ψc
           /\ ~ In v ψd
           /\ nnrs_stmt_cross_shadow_free_under s₀ (v::σ) ψc ψd
         | NNRSLetMut v s₁ s₂ =>
           ~ In v σ
           /\ ~ In v ψc
           /\ ~ In v ψd      
           /\ nnrs_stmt_cross_shadow_free_under s₁ σ ψc (v::ψd)
           /\ nnrs_stmt_cross_shadow_free_under s₂ (v::σ) ψc ψd
         | NNRSLetMutColl v s₁ s₂ =>
           ~ In v σ
           /\ ~ In v ψc
           /\ ~ In v ψd      
           /\ nnrs_stmt_cross_shadow_free_under s₁ σ (v::ψc) ψd
           /\ nnrs_stmt_cross_shadow_free_under s₂ (v::σ) ψc ψd
         | NNRSAssign v e =>
           disjoint (nnrs_expr_free_vars e) ψc
           /\ disjoint (nnrs_expr_free_vars e) ψd
           /\ ~ In v σ
           /\ ~ In v ψc
         (* not the same: In v ψd *)
         | NNRSPush v e =>
           disjoint (nnrs_expr_free_vars e) ψc
           /\ disjoint (nnrs_expr_free_vars e) ψd
           /\ ~ In v σ
           /\ ~ In v ψd
         (* not the same: In v ψc *)
         | NNRSFor v e s₀ =>
           disjoint (nnrs_expr_free_vars e) ψc
           /\ disjoint (nnrs_expr_free_vars e) ψd
           (* not the same: incl (nnrs_expr_free_vars e) σ *)          
           /\ ~ In v ψc
           /\ ~ In v ψd
           /\ nnrs_stmt_cross_shadow_free_under s₀ (v::σ) ψc ψd
         | NNRSIf e s₁ s₂ =>
           disjoint (nnrs_expr_free_vars e) ψc
           /\ disjoint (nnrs_expr_free_vars e) ψd
           (* not the same: incl (nnrs_expr_free_vars e) σ *)
           /\ nnrs_stmt_cross_shadow_free_under s₁ σ ψc ψd
           /\ nnrs_stmt_cross_shadow_free_under s₂ σ ψc ψd
         | NNRSEither e x₁ s₁ x₂ s₂ =>
           disjoint (nnrs_expr_free_vars e) ψc
           /\ disjoint (nnrs_expr_free_vars e) ψd
           (* not the same: incl (nnrs_expr_free_vars e) σ *)
           /\ ~ In x₁ ψc
           /\ ~ In x₁ ψd
           /\ ~ In x₂ ψc
           /\ ~ In x₂ ψd
           /\ nnrs_stmt_cross_shadow_free_under s₁ (x₁::σ) ψc ψd
           /\ nnrs_stmt_cross_shadow_free_under s₂ (x₂::σ) ψc ψd
         end.

    Definition nnrs_cross_shadow_free (s:nnrs)
      := nnrs_stmt_cross_shadow_free_under (fst s) nil nil (snd s::nil).

  End def.

  (** If the cross shadow predicate holds, then the environments in question 
      must obey certain disjointness conditions *)
  Section cross_shadow_free_disjointness.

    Lemma nnrs_stmt_cross_shadow_free_under_free_mcenv_env
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_free_mcenv_vars s) σ.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        eapply IHs2; eauto; simpl; eauto.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        + apply remove_inv in H4.
          eapply IHs1; eauto; tauto.
        + eapply IHs2; eauto; simpl; eauto.
      - Case "NNRSAssign"%string.
        contradiction.
      - Case "NNRSPush"%string.
        intuition congruence.
      - Case "NNRSFor"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + eapply IHs1; eauto; simpl; eauto.
        + eapply IHs2; eauto; simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_free_mdenv_env
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_free_mdenv_vars s) σ.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        + apply remove_inv in H4.
          eapply IHs1; eauto; tauto.
        + eapply IHs2; eauto; simpl; eauto.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        eapply IHs2; eauto; simpl; eauto.
      - Case "NNRSAssign"%string.
        intuition congruence.
      - Case "NNRSPush"%string.
        contradiction.
      - Case "NNRSFor"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + eapply IHs1; eauto; simpl; eauto.
        + eapply IHs2; eauto; simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_free_env_mcenv
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_free_env_vars s) ψc.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        apply remove_inv in H4.
        eapply IHs; eauto; simpl; tauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        apply remove_inv in H4.
        eapply IHs2; eauto; simpl; tauto.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        + eapply IHs1; eauto; simpl; eauto. 
        + apply remove_inv in H4.
          eapply IHs2; eauto; tauto.
      - Case "NNRSAssign"%string.
        intuition eauto.
      - Case "NNRSPush"%string.
        intuition eauto.
      - Case "NNRSFor"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        apply remove_inv in H4.
        eapply IHs; eauto; simpl; tauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + eapply H0; eauto.
        + apply remove_inv in H9.
          eapply IHs1; eauto; tauto.
        + apply remove_inv in H9.
          eapply IHs2; eauto; tauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_free_mdenv_mcenv
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_free_mdenv_vars s) ψc.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        apply remove_inv in H4.
        eapply IHs1; eauto; tauto.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        eapply IHs1; eauto; simpl; eauto.
      - Case "NNRSAssign"%string.
        intuition congruence.
      - Case "NNRSPush"%string.
        contradiction.
      - Case "NNRSFor"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + eapply IHs1; eauto; simpl; eauto.
        + eapply IHs2; eauto; simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_free_env_mdenv
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_free_env_vars s) ψd.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        apply remove_inv in H4.
        eapply IHs; eauto; simpl; tauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        + eapply IHs1; eauto; simpl; tauto.
        + apply remove_inv in H4.
          eapply IHs2; eauto; simpl; tauto.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        apply remove_inv in H4.
        eapply IHs2; eauto; tauto.
      - Case "NNRSAssign"%string.
        intuition eauto.
      - Case "NNRSPush"%string.
        intuition eauto.
      - Case "NNRSFor"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        apply remove_inv in H4.
        eapply IHs; eauto; simpl; tauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + eapply H2; eauto.
        + apply remove_inv in H9.
          eapply IHs1; eauto; tauto.
        + apply remove_inv in H9.
          eapply IHs2; eauto; tauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_free_mcenv_mdenv
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_free_mcenv_vars s) ψd.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        eapply IHs1; eauto; simpl; tauto.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        apply remove_inv in H4.
        eapply IHs1; eauto; tauto.
      - Case "NNRSAssign"%string.
        contradiction.
      - Case "NNRSPush"%string.
        intuition congruence.
      - Case "NNRSFor"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + eapply IHs1; eauto; simpl; eauto.
        + eapply IHs2; eauto; simpl; eauto.
    Qed.
    
    Lemma nnrs_stmt_cross_shadow_free_under_free_env_cons
          {s:nnrs_stmt} {σ ψc ψd:list var} {v} :
      nnrs_stmt_cross_shadow_free_under s (v::σ) ψc ψd ->
      ~ In v (nnrs_stmt_free_mcenv_vars s) /\ ~ In v (nnrs_stmt_free_mdenv_vars s).
    Proof.
      intros sf; split; intros inn.
      - eapply nnrs_stmt_cross_shadow_free_under_free_mcenv_env; eauto
        ;  simpl; eauto.
      - eapply nnrs_stmt_cross_shadow_free_under_free_mdenv_env; eauto
        ;  simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_free_mcenv_cons
          {s:nnrs_stmt} {σ ψc ψd:list var} {v} :
      nnrs_stmt_cross_shadow_free_under s σ (v::ψc) ψd ->
      ~ In v (nnrs_stmt_free_env_vars s) /\ ~ In v (nnrs_stmt_free_mdenv_vars s).
    Proof.
      intros sf; split; intros inn.
      - eapply nnrs_stmt_cross_shadow_free_under_free_env_mcenv; eauto
        ;  simpl; eauto.
      - eapply nnrs_stmt_cross_shadow_free_under_free_mdenv_mcenv; eauto
        ;  simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_free_mdenv_cons
          {s:nnrs_stmt} {σ ψc ψd:list var} {v} :
      nnrs_stmt_cross_shadow_free_under s σ ψc (v::ψd) ->
      ~ In v (nnrs_stmt_free_env_vars s) /\ ~ In v (nnrs_stmt_free_mcenv_vars s).
    Proof.
      intros sf; split; intros inn.
      - eapply nnrs_stmt_cross_shadow_free_under_free_env_mdenv; eauto
        ;  simpl; eauto.
      - eapply nnrs_stmt_cross_shadow_free_under_free_mcenv_mdenv; eauto
        ;  simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_free_cons
          (s:nnrs_stmt) (σ ψc ψd:list var) v :
      (nnrs_stmt_cross_shadow_free_under s (v::σ) ψc ψd ->
       ~ In v (nnrs_stmt_free_mcenv_vars s) /\ ~ In v (nnrs_stmt_free_mdenv_vars s))
      /\ (nnrs_stmt_cross_shadow_free_under s σ (v::ψc) ψd ->
          ~ In v (nnrs_stmt_free_env_vars s) /\ ~ In v (nnrs_stmt_free_mdenv_vars s))
      /\ (nnrs_stmt_cross_shadow_free_under s σ ψc (v::ψd) ->
          ~ In v (nnrs_stmt_free_env_vars s) /\ ~ In v (nnrs_stmt_free_mcenv_vars s))

    .
    Proof.
      split; [ | split ].
      -  apply nnrs_stmt_cross_shadow_free_under_free_env_cons.
      -  apply nnrs_stmt_cross_shadow_free_under_free_mcenv_cons.
      -  apply nnrs_stmt_cross_shadow_free_under_free_mdenv_cons.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_bound_mcenv_env
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_bound_mcenv_vars s) σ.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        eapply IHs2; eauto; simpl; eauto.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto; subst; intuition.
        eapply IHs2 in H5; eauto; simpl; tauto.
      - Case "NNRSAssign"%string.
        contradiction.
      - Case "NNRSPush"%string.
        intuition congruence.
      - Case "NNRSFor"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + eapply IHs1; eauto; simpl; eauto.
        + eapply IHs2; eauto; simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_bound_mdenv_env
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_bound_mdenv_vars s) σ.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto; subst; try tauto.
        eapply IHs2 in H5; intuition eauto.
        simpl; tauto.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        eapply IHs2; eauto; simpl; eauto.
      - Case "NNRSAssign"%string.
        intuition congruence.
      - Case "NNRSPush"%string.
        contradiction.
      - Case "NNRSFor"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + eapply IHs1; eauto; simpl; eauto.
        + eapply IHs2; eauto; simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_bound_env_mcenv
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_bound_env_vars s) ψc.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        destruct inn.
        + subst; intuition.
        + intuition.
          eapply IHs in H6; intuition eauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        subst; intuition.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        + subst; tauto.
        + eapply IHs1 in H3; intuition eauto.
          simpl; tauto.
      - Case "NNRSAssign"%string.
        intuition eauto.
      - Case "NNRSPush"%string.
        intuition eauto.
      - Case "NNRSFor"%string.
        intuition eauto; subst; tauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + subst; tauto.
        + subst; tauto.
        + eapply IHs1; eauto.
        + eapply IHs2; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_bound_mdenv_mcenv
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_bound_mdenv_vars s) ψc.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        subst; tauto.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        eapply IHs1; eauto; simpl; eauto.
      - Case "NNRSAssign"%string.
        intuition congruence.
      - Case "NNRSPush"%string.
        contradiction.
      - Case "NNRSFor"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + eapply IHs1; eauto; simpl; eauto.
        + eapply IHs2; eauto; simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_bound_env_mdenv
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_bound_env_vars s) ψd.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        intuition eauto.
        subst; tauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        + subst; tauto.
        + eapply IHs1; eauto; simpl; tauto.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        subst; tauto.
      - Case "NNRSAssign"%string.
        intuition eauto.
      - Case "NNRSPush"%string.
        intuition eauto.
      - Case "NNRSFor"%string.
        intuition eauto.
        subst; tauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + subst; tauto.
        + subst; tauto.
        + eapply IHs1; eauto; tauto.
        + eapply IHs2; eauto; tauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_bound_mcenv_mdenv
          (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      disjoint (nnrs_stmt_bound_mcenv_vars s) ψd.
    Proof.
      unfold disjoint.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf x inn.
      - Case "NNRSSeq"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
      - Case "NNRSLet"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSLetMut"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        eapply IHs1; eauto; simpl; tauto.
      - Case "NNRSLetMutColl"%string.
        rewrite in_app_iff in inn.
        intuition eauto.
        subst; tauto.
      - Case "NNRSAssign"%string.
        contradiction.
      - Case "NNRSPush"%string.
        intuition congruence.
      - Case "NNRSFor"%string.
        intuition.
        eapply IHs; eauto; simpl; eauto.
      - Case "NNRSIf"%string.
        repeat rewrite in_app_iff in inn.
        intuition eauto. 
      - Case "NNRSEither"%string.
        repeat rewrite in_app_iff in inn.
        intuition.
        + eapply IHs1; eauto; simpl; eauto.
        + eapply IHs2; eauto; simpl; eauto.
    Qed.
    
    Lemma nnrs_stmt_cross_shadow_free_under_bound_env_cons
          {s:nnrs_stmt} {σ ψc ψd:list var} {v} :
      nnrs_stmt_cross_shadow_free_under s (v::σ) ψc ψd ->
      ~ In v (nnrs_stmt_bound_mcenv_vars s) /\ ~ In v (nnrs_stmt_bound_mdenv_vars s).
    Proof.
      intros sf; split; intros inn.
      - eapply nnrs_stmt_cross_shadow_free_under_bound_mcenv_env; eauto
        ;  simpl; eauto.
      - eapply nnrs_stmt_cross_shadow_free_under_bound_mdenv_env; eauto
        ;  simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_bound_mcenv_cons
          {s:nnrs_stmt} {σ ψc ψd:list var} {v} :
      nnrs_stmt_cross_shadow_free_under s σ (v::ψc) ψd ->
      ~ In v (nnrs_stmt_bound_env_vars s) /\ ~ In v (nnrs_stmt_bound_mdenv_vars s).
    Proof.
      intros sf; split; intros inn.
      - eapply nnrs_stmt_cross_shadow_free_under_bound_env_mcenv; eauto
        ;  simpl; eauto.
      - eapply nnrs_stmt_cross_shadow_free_under_bound_mdenv_mcenv; eauto
        ;  simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_bound_mdenv_cons
          {s:nnrs_stmt} {σ ψc ψd:list var} {v} :
      nnrs_stmt_cross_shadow_free_under s σ ψc (v::ψd) ->
      ~ In v (nnrs_stmt_bound_env_vars s) /\ ~ In v (nnrs_stmt_bound_mcenv_vars s).
    Proof.
      intros sf; split; intros inn.
      - eapply nnrs_stmt_cross_shadow_free_under_bound_env_mdenv; eauto
        ;  simpl; eauto.
      - eapply nnrs_stmt_cross_shadow_free_under_bound_mcenv_mdenv; eauto
        ;  simpl; eauto.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_bound_cons
          (s:nnrs_stmt) (σ ψc ψd:list var) v :
      (nnrs_stmt_cross_shadow_free_under s (v::σ) ψc ψd ->
       ~ In v (nnrs_stmt_bound_mcenv_vars s) /\ ~ In v (nnrs_stmt_bound_mdenv_vars s))
      /\ (nnrs_stmt_cross_shadow_free_under s σ (v::ψc) ψd ->
          ~ In v (nnrs_stmt_bound_env_vars s) /\ ~ In v (nnrs_stmt_bound_mdenv_vars s))
      /\ (nnrs_stmt_cross_shadow_free_under s σ ψc (v::ψd) ->
          ~ In v (nnrs_stmt_bound_env_vars s) /\ ~ In v (nnrs_stmt_bound_mcenv_vars s))

    .
    Proof.
      split; [ | split ].
      -  apply nnrs_stmt_cross_shadow_free_under_bound_env_cons.
      -  apply nnrs_stmt_cross_shadow_free_under_bound_mcenv_cons.
      -  apply nnrs_stmt_cross_shadow_free_under_bound_mdenv_cons.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_under_vars_cons
          (s:nnrs_stmt) (σ ψc ψd:list var) v :
      (nnrs_stmt_cross_shadow_free_under s (v::σ) ψc ψd ->
       ~ In v (nnrs_stmt_free_mcenv_vars s) /\ ~ In v (nnrs_stmt_free_mdenv_vars s)
       /\ ~ In v (nnrs_stmt_bound_mcenv_vars s) /\ ~ In v (nnrs_stmt_bound_mdenv_vars s))
      /\ (nnrs_stmt_cross_shadow_free_under s σ (v::ψc) ψd ->
          ~ In v (nnrs_stmt_free_env_vars s) /\ ~ In v (nnrs_stmt_free_mdenv_vars s)
          /\ ~ In v (nnrs_stmt_bound_env_vars s) /\ ~ In v (nnrs_stmt_bound_mdenv_vars s))
      /\ (nnrs_stmt_cross_shadow_free_under s σ ψc (v::ψd) ->
          ~ In v (nnrs_stmt_free_env_vars s) /\ ~ In v (nnrs_stmt_free_mcenv_vars s)
          /\ ~ In v (nnrs_stmt_bound_env_vars s) /\ ~ In v (nnrs_stmt_bound_mcenv_vars s))
           
    .
    Proof.
      generalize (nnrs_stmt_cross_shadow_free_under_free_cons s σ ψc ψd v).
      generalize (nnrs_stmt_cross_shadow_free_under_bound_cons s σ ψc ψd v).
      intuition.
    Qed.
    
  End cross_shadow_free_disjointness.

  (** The cross shadow predicate is preserved by equivalence an inclusion of the variable lists *)
  Section cross_shadow_free_equivs.
    
    Global Instance nnrs_stmt_cross_shadow_free_under_equivs :
      Proper (eq ==> equivlist ==> equivlist ==> equivlist ==> iff) nnrs_stmt_cross_shadow_free_under.
    Proof.
      cut (Proper (eq ==> equivlist ==> equivlist ==> equivlist ==> Basics.impl) nnrs_stmt_cross_shadow_free_under).
      {
        unfold Proper, respectful, equivlist; unfold Basics.impl; split; [eauto | ].
        symmetry in H1, H2, H3; eauto.
      }
      Ltac re_equivs_tac
        := match goal with
           | [H1: equivlist ?x ?y, H2: In ?v ?x, H3: In ?v ?y -> False |- _ ] =>
             rewrite H1 in H2; contradiction
           | [H1: equivlist ?y ?x, H2: In ?v ?x, H3: In ?v ?y -> False |- _ ] =>
             rewrite <- H1 in H2; contradiction
           | [ H1: equivlist ?x ?y, H2: disjoint _ ?x |- _ ] => rewrite H1 in H2
           | [ H1: equivlist ?x ?y |- disjoint _ ?x] => rewrite H1
           | [ |- equivlist (?x :: _ ) (?x :: _ ) ] => apply equivlist_cons_proper; [reflexivity | ]
           end.

      unfold Proper, respectful, Basics.impl; intros ? s ?; subst.
      nnrs_stmt_cases (induction s) Case
      ; simpl; intros.
      -  Case "NNRSSeq"%string.
         intuition eauto.
      -  Case "NNRSLet"%string.
         intuition; repeat re_equivs_tac; eauto 2.
         + eapply (IHs (v::x)); eauto.
           re_equivs_tac; trivial.
      - Case "NNRSLetMut"%string.
        intuition; repeat re_equivs_tac; eauto 2.
        + eapply IHs1; (try (eapply equivlist_cons; trivial; eapply H1)); eauto.
        + eapply IHs2; eauto. 
          re_equivs_tac; trivial.
      - Case "NNRSLetMutColl"%string.
        intuition; repeat re_equivs_tac; eauto 2.
        + eapply IHs1; (try (eapply equivlist_cons; trivial; eapply H0)); eauto.
        + eapply IHs2; eauto. 
          re_equivs_tac; trivial.
      - Case "NNRSAssign"%string.
        intuition; repeat re_equivs_tac; eauto 2.
      - Case "NNRSPush"%string.
        intuition; repeat re_equivs_tac; eauto 2.
      - Case "NNRSFor"%string.
        intuition; repeat re_equivs_tac; eauto 2.
        + eapply (IHs (v::x)); eauto.
          re_equivs_tac; trivial.
      - Case "NNRSIf"%string.
        intuition; repeat re_equivs_tac; eauto 2.
      - Case "NNRSEither"%string.
        intuition; repeat re_equivs_tac; eauto 2.
        + eapply IHs1; eauto; re_equivs_tac; trivial.
        + eapply IHs2; eauto; re_equivs_tac; trivial.
    Qed.

    Global Instance nnrs_stmt_cross_shadow_free_under_incls :
      Proper (eq ==> (@incl string) --> (@incl string) --> (@incl string) --> Basics.impl) nnrs_stmt_cross_shadow_free_under.
    Proof.
      Ltac re_incl_tac
        := match goal with
           | [H1: incl ?x ?y, H2: In ?v ?x, H3: In ?v ?y -> False |- _ ] =>
             rewrite H1 in H2; contradiction
           | [H1: incl ?y ?x, H2: In ?v ?x, H3: In ?v ?y -> False |- _ ] =>
             rewrite <- H1 in H2; contradiction
           | [ H1: incl ?x ?y, H2: disjoint _ ?x |- _ ] => rewrite H1 in H2
           | [ H1: incl ?x ?y |- disjoint _ ?x] => rewrite H1
           | [ |- incl (?x :: _ ) (?x :: _ ) ] => apply incl_cons_proper; [reflexivity | ]
           end.

      Ltac re_incl_tact := intuition; try solve [repeat re_incl_tac; intuition].


      unfold Proper, respectful, Basics.impl, Basics.flip; intros ? s ?; subst.
      nnrs_stmt_cases (induction s) Case
      ; simpl; intros.
      -  Case "NNRSSeq"%string.
         intuition eauto.
      -  Case "NNRSLet"%string.
         re_incl_tact.
         + eapply (IHs (v::x)); eauto.
           re_incl_tact.
      - Case "NNRSLetMut"%string.
        re_incl_tact.
        + eapply IHs1; (try (eapply incl_cons_proper; trivial; eapply H1)); eauto.
        + eapply IHs2; eauto. 
          re_incl_tact.
      - Case "NNRSLetMutColl"%string.
        re_incl_tact.
        + eapply IHs1; (try (eapply incl_cons_proper; trivial; eapply H0)); eauto.
        + eapply IHs2; eauto. 
          re_incl_tact.
      - Case "NNRSAssign"%string.
        re_incl_tact.
      - Case "NNRSPush"%string.
        re_incl_tact.
      - Case "NNRSFor"%string.
        re_incl_tact.
        + eapply (IHs (v::x)); eauto.
          re_incl_tact.
      - Case "NNRSIf"%string.
        re_incl_tact; eauto.
      - Case "NNRSEither"%string.
        re_incl_tact.
        + eapply IHs1; eauto; re_incl_tact.
        + eapply IHs2; eauto; re_incl_tact.
    Qed.

  End cross_shadow_free_equivs.

  (** The cross shadow under predicate is "top down".  This version is more bottom up.
        The former is easier for the translation to work with, the latter for the uncross_shadow transformation introduced later.
        The latter implies the former for suitably disjoint variable lists.
   *)

  Section cross_shadow_free_alt.

    Fixpoint nnrs_stmt_cross_shadow_free_alt
             (s:nnrs_stmt)
    : Prop
      := match s with
         | NNRSSeq s₁ s₂ =>
           nnrs_stmt_cross_shadow_free_alt s₁
           /\ nnrs_stmt_cross_shadow_free_alt s₂
         | NNRSLet v e s₀ =>
           ~ In v (nnrs_stmt_free_mcenv_vars s₀)
           /\ ~ In v (nnrs_stmt_bound_mcenv_vars s₀)
           /\ ~ In v (nnrs_stmt_free_mdenv_vars s₀)
           /\ ~ In v (nnrs_stmt_bound_mdenv_vars s₀)
           /\ nnrs_stmt_cross_shadow_free_alt s₀
         | NNRSLetMut v s₁ s₂ =>
           ~ In v (nnrs_stmt_free_env_vars s₁)
           /\ ~ In v (nnrs_stmt_bound_env_vars s₁)
           /\ ~ In v (nnrs_stmt_free_mcenv_vars s₁)
           /\ ~ In v (nnrs_stmt_bound_mcenv_vars s₁)
           /\ ~ In v (nnrs_stmt_free_mcenv_vars s₂)
           /\ ~ In v (nnrs_stmt_bound_mcenv_vars s₂)
           /\ ~ In v (nnrs_stmt_bound_mdenv_vars s₂)
           /\ ~ In v (nnrs_stmt_free_mdenv_vars s₂)
           /\ nnrs_stmt_cross_shadow_free_alt s₁
           /\ nnrs_stmt_cross_shadow_free_alt s₂
         | NNRSLetMutColl v s₁ s₂ =>
           ~ In v (nnrs_stmt_free_env_vars s₁)
           /\ ~ In v (nnrs_stmt_bound_env_vars s₁)
           /\ ~ In v (nnrs_stmt_free_mdenv_vars s₁)
           /\ ~ In v (nnrs_stmt_bound_mdenv_vars s₁)
           /\ ~ In v (nnrs_stmt_free_mcenv_vars s₂)
           /\ ~ In v (nnrs_stmt_bound_mcenv_vars s₂)
           /\ ~ In v (nnrs_stmt_bound_mdenv_vars s₂)
           /\ ~ In v (nnrs_stmt_free_mdenv_vars s₂)
           /\ nnrs_stmt_cross_shadow_free_alt s₁
           /\ nnrs_stmt_cross_shadow_free_alt s₂ 
         | NNRSAssign v e => True
         | NNRSPush v e => True
         | NNRSFor v e s₀ =>
           ~ In v (nnrs_stmt_free_mcenv_vars s₀)
           /\ ~ In v (nnrs_stmt_bound_mcenv_vars s₀)
           /\ ~ In v (nnrs_stmt_free_mdenv_vars s₀)
           /\ ~ In v (nnrs_stmt_bound_mdenv_vars s₀)
           /\ nnrs_stmt_cross_shadow_free_alt s₀
         | NNRSIf e s₁ s₂ =>
           nnrs_stmt_cross_shadow_free_alt s₁
           /\ nnrs_stmt_cross_shadow_free_alt s₂
         | NNRSEither e x₁ s₁ x₂ s₂ =>
           ~ In x₁ (nnrs_stmt_free_mcenv_vars s₁)
           /\ ~ In x₁ (nnrs_stmt_bound_mcenv_vars s₁)
           /\ ~ In x₁ (nnrs_stmt_free_mdenv_vars s₁)
           /\ ~ In x₁ (nnrs_stmt_bound_mdenv_vars s₁)
           /\ ~ In x₂ (nnrs_stmt_free_mcenv_vars s₂)
           /\ ~ In x₂ (nnrs_stmt_bound_mcenv_vars s₂)
           /\ ~ In x₂ (nnrs_stmt_free_mdenv_vars s₂)
           /\ ~ In x₂ (nnrs_stmt_bound_mdenv_vars s₂)
           /\ nnrs_stmt_cross_shadow_free_alt s₁ 
           /\ nnrs_stmt_cross_shadow_free_alt s₂ 
         end.

    Ltac disj_tac :=
      repeat
        (match goal with
         | [ H : disjoint (_ ++ _) _ |- _ ] => apply disjoint_app_l in H; destruct H
         | [ H : disjoint (_ :: _) _ |- _ ] => apply disjoint_cons_inv1 in H; destruct H
         | [ H : disjoint _ (_ :: _) |- _ ] => apply disjoint_cons_inv2 in H; destruct H
         | [H1:disjoint (remove _ ?v ?l1) ?l2,
               H2:In ?v ?l1 -> False |- _ ] => rewrite nin_remove in H1 by apply H2
         | [H1:disjoint (remove _ ?v ?l1) ?l2,
               H2:~ In ?v ?l1 |- _ ] => rewrite nin_remove in H1 by apply H2
         | [H1:disjoint (remove _ ?v ?l1) ?l2,
               H2:In ?v ?l2 -> False |- _ ] => rewrite disjoint_remove_swap in H1; rewrite nin_remove in H1 by apply H2
         | [H1:disjoint (remove _ ?v ?l1) ?l2,
               H2:~ In ?v ?l2 |- _ ] => rewrite disjoint_remove_swap in H1; rewrite nin_remove in H1 by apply H2
         | [H : In _ (replace_all _ _ _ ) |- _ ] => apply in_replace_all in H; try solve [destruct H as [?|[??]]; subst; eauto]
         | [H: ~ In _ (remove _ _ _) |- _ ] => try rewrite <- remove_in_neq in H by congruence
         | [H: In _ (remove _ _ _) -> False |- _ ] => try rewrite <- remove_in_neq in H by congruence
         | [ |- disjoint (_ :: _) _ ] => apply disjoint_cons1
         | [ |- disjoint _ (_ :: _) ] => apply disjoint_cons2
         | [ |- disjoint _ (replace_all _ _ _ )] => try solve [apply disjoint_replace_all; intuition]
                                                        
         end; repeat rewrite in_app_iff in *
        ).

    Theorem  nnrs_stmt_cross_shadow_free_alt_under
             (s:nnrs_stmt) :
      nnrs_stmt_cross_shadow_free_alt s ->
      forall (σ ψc ψd:list var),
        disjoint (nnrs_stmt_free_mcenv_vars s) σ ->
        disjoint (nnrs_stmt_bound_mcenv_vars s) σ ->
        disjoint (nnrs_stmt_free_mdenv_vars s) σ ->
        disjoint (nnrs_stmt_bound_mdenv_vars s) σ ->
        disjoint (nnrs_stmt_free_env_vars s) ψc ->
        disjoint (nnrs_stmt_bound_env_vars s) ψc ->
        disjoint (nnrs_stmt_free_mdenv_vars s) ψc ->
        disjoint (nnrs_stmt_bound_mdenv_vars s) ψc ->
        disjoint (nnrs_stmt_free_env_vars s) ψd ->
        disjoint (nnrs_stmt_bound_env_vars s) ψd ->
        disjoint (nnrs_stmt_free_mcenv_vars s) ψd ->
        disjoint (nnrs_stmt_bound_mcenv_vars s) ψd ->
        nnrs_stmt_cross_shadow_free_under s σ ψc ψd.
    Proof.
      nnrs_stmt_cases (induction s) Case
      ; simpl; intros 
      ; disj_tac
      ; repeat split
      ; try solve [
              tauto
            | eapply IHs; disj_tac; intuition
            | eapply IHs1; disj_tac; intuition
            | eapply IHs2; disj_tac; intuition].
    Qed.

    Theorem  nnrs_stmt_cross_shadow_free_under_alt (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      nnrs_stmt_cross_shadow_free_alt s.
    Proof.
      revert σ ψc ψd.
      nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf
      ; disj_tac
      ; try solve[
              repeat match goal with
                     | [H: _ /\ _ |- _ ] => destruct H
                     end
              ; repeat split; eauto 3
              ; repeat match goal with
                       | [H: nnrs_stmt_cross_shadow_free_under _ _ _ _ |- _ ] => apply nnrs_stmt_cross_shadow_free_under_vars_cons in H
                       end; try tauto].
    Qed.


    Ltac fresh_simpl_rewriter
      := repeat autorewrite with nnrs_rename in *
         ; repeat rewrite in_app_iff in *
         ; repeat match goal with
                  | [H: In _ (nnrs_stmt_free_env_vars (nnrs_stmt_rename_env _ _ _)) |- _] => apply nnrs_stmt_free_env_vars_rename_env_in in H
                  | [H: In _ (nnrs_stmt_free_mcenv_vars (nnrs_stmt_rename_mc _ _ _)) |- _] => apply nnrs_stmt_free_mcenv_vars_rename_mcenv_in in H
                  | [H: In _ (nnrs_stmt_free_mdenv_vars (nnrs_stmt_rename_md _ _ _)) |- _] => apply nnrs_stmt_free_mdenv_vars_rename_mdenv_in in H
                  | [H: In _ (remove _ _ _) -> False |- _ ] =>
                    try rewrite <- remove_in_neq in H by congruence
                  end
         ; intuition.

    
    Lemma nnrs_stmt_cross_shadow_free_alt_rename_env s v v' :
      ~ In v' (nnrs_stmt_free_mcenv_vars s) ->
      ~ In v' (nnrs_stmt_bound_mcenv_vars s )->
      ~ In v' (nnrs_stmt_free_mdenv_vars s) ->
      ~ In v' (nnrs_stmt_bound_mdenv_vars s) ->
      nnrs_stmt_cross_shadow_free_alt s ->
      nnrs_stmt_cross_shadow_free_alt
        (nnrs_stmt_rename_env s v v').
    Proof.
      nnrs_stmt_cases (induction s) Case
      ; simpl.
      - Case "NNRSSeq"%string.
        fresh_simpl_rewriter.
      - Case "NNRSLet"%string.
        match_destr.
        fresh_simpl_rewriter.
      - Case "NNRSLetMut"%string.
        repeat split
        ; do 2 fresh_simpl_rewriter
        ; try (match_destr_in H4
               ; fresh_simpl_rewriter).
        match_destr; fresh_simpl_rewriter.
      - Case "NNRSLetMutColl"%string.
        repeat split
        ; do 2 fresh_simpl_rewriter
        ; try (match_destr_in H4
               ; fresh_simpl_rewriter).
        match_destr; fresh_simpl_rewriter.
      - Case "NNRSAssign"%string.
        trivial.
      - Case "NNRSPush"%string.
        trivial.
      - Case "NNRSFor"%string.
        match_destr.
        fresh_simpl_rewriter.
      - Case "NNRSIf"%string.
        fresh_simpl_rewriter.
      - Case "NNRSEither"%string.
        fresh_simpl_rewriter
        ; try (match_destr_in H2; fresh_simpl_rewriter)
        ; match_destr; fresh_simpl_rewriter.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_alt_rename_mcenv s v v' :
      ~ In v' (nnrs_stmt_free_env_vars s) ->
      ~ In v' (nnrs_stmt_bound_env_vars s )->
      ~ In v' (nnrs_stmt_free_mdenv_vars s) ->
      ~ In v' (nnrs_stmt_bound_mdenv_vars s) ->
      nnrs_stmt_cross_shadow_free_alt s ->
      nnrs_stmt_cross_shadow_free_alt
        (nnrs_stmt_rename_mc s v v').
    Proof.
      nnrs_stmt_cases (induction s) Case
      ; simpl.
      - Case "NNRSSeq"%string.
        fresh_simpl_rewriter.
      - Case "NNRSLet"%string.
        do 2 fresh_simpl_rewriter.
      - Case "NNRSLetMut"%string.
        repeat split
        ; do 2 fresh_simpl_rewriter.
      - Case "NNRSLetMutColl"%string.
        repeat split
        ; do 2 fresh_simpl_rewriter
        ; try (match_destr_in H4
               ; fresh_simpl_rewriter).
        match_destr; fresh_simpl_rewriter.
      - Case "NNRSAssign"%string.
        trivial.
      - Case "NNRSPush"%string.
        trivial.
      - Case "NNRSFor"%string.
        do 2 fresh_simpl_rewriter.
      - Case "NNRSIf"%string.
        fresh_simpl_rewriter.
      - Case "NNRSEither"%string.
        do 2 fresh_simpl_rewriter.
    Qed.

    Lemma nnrs_stmt_cross_shadow_free_alt_rename_mdenv s v v' :
      ~ In v' (nnrs_stmt_free_env_vars s) ->
      ~ In v' (nnrs_stmt_bound_env_vars s )->
      ~ In v' (nnrs_stmt_free_mcenv_vars s) ->
      ~ In v' (nnrs_stmt_bound_mcenv_vars s) ->
      nnrs_stmt_cross_shadow_free_alt s ->
      nnrs_stmt_cross_shadow_free_alt
        (nnrs_stmt_rename_md s v v').
    Proof.
      nnrs_stmt_cases (induction s) Case
      ; simpl.
      - Case "NNRSSeq"%string.
        fresh_simpl_rewriter.
      - Case "NNRSLet"%string.
        do 2 fresh_simpl_rewriter.
      - Case "NNRSLetMut"%string.
        repeat split
        ; do 2 fresh_simpl_rewriter
        ; try (match_destr_in H4
               ; fresh_simpl_rewriter).
        match_destr; fresh_simpl_rewriter.
      - Case "NNRSLetMutColl"%string.
        repeat split
        ; do 2 fresh_simpl_rewriter
        ; try (match_destr_in H4
               ; fresh_simpl_rewriter).
      - Case "NNRSAssign"%string.
        trivial.
      - Case "NNRSPush"%string.
        trivial.
      - Case "NNRSFor"%string.
        do 2 fresh_simpl_rewriter.
      - Case "NNRSIf"%string.
        fresh_simpl_rewriter.
      - Case "NNRSEither"%string.
        do 2 fresh_simpl_rewriter.
    Qed.

  End cross_shadow_free_alt.


  Section uncross.

    Context (sep:string).
    Fixpoint nnrs_stmt_uncross_shadow_under
             (s:nnrs_stmt)
             (σ ψc ψd:list var)
      : nnrs_stmt
      := match s with
         | NNRSSeq s₁ s₂ =>
           NNRSSeq
             (nnrs_stmt_uncross_shadow_under s₁ σ ψc ψd)
             (nnrs_stmt_uncross_shadow_under s₂ σ ψc ψd)
         | NNRSLet v e s₀ =>
           let s₀' := nnrs_stmt_uncross_shadow_under s₀ (v::σ) ψc ψd in
           let problems :=
               remove equiv_dec v (nnrs_stmt_free_env_vars s₀')
                      ++ remove equiv_dec v (nnrs_stmt_bound_env_vars s₀')
                      ++ (nnrs_stmt_free_mcenv_vars s₀')
                      ++ (nnrs_stmt_bound_mcenv_vars s₀')
                      ++ (nnrs_stmt_free_mdenv_vars s₀')
                      ++ (nnrs_stmt_bound_mdenv_vars s₀')
           in
           let v' := fresh_var_from sep v problems in
           NNRSLet v' e (mk_lazy_lift nnrs_stmt_rename_env s₀' v v')
         | NNRSLetMut v s₁ s₂ =>
           let s₁' := nnrs_stmt_uncross_shadow_under s₁ σ ψc (v::ψd) in
           let s₂' := nnrs_stmt_uncross_shadow_under s₂ (v::σ) ψc ψd in
           let problems := remove equiv_dec v (nnrs_stmt_free_mdenv_vars s₁')
                                  ++ remove equiv_dec v (nnrs_stmt_bound_mdenv_vars s₁')
                                  ++ remove equiv_dec v (nnrs_stmt_free_env_vars s₂')
                                  ++ remove equiv_dec v (nnrs_stmt_bound_env_vars s₂')
                                  ++ σ
                                  ++ ψd
                                  ++ nnrs_stmt_free_env_vars s₁'
                                  ++ nnrs_stmt_bound_env_vars s₁'
                                  ++ nnrs_stmt_free_mcenv_vars s₁'
                                  ++ nnrs_stmt_bound_mcenv_vars s₁'
                                  ++ nnrs_stmt_free_mcenv_vars s₂'
                                  ++ nnrs_stmt_bound_mcenv_vars s₂'
                                  ++ nnrs_stmt_free_mdenv_vars s₂'
                                  ++ nnrs_stmt_bound_mdenv_vars s₂' in
           let v' := fresh_var_from sep v problems in
           NNRSLetMut v'
                      (mk_lazy_lift nnrs_stmt_rename_md s₁' v v')
                      (mk_lazy_lift nnrs_stmt_rename_env s₂' v v')
         | NNRSLetMutColl v s₁ s₂ =>
           let s₁' := nnrs_stmt_uncross_shadow_under s₁ σ (v::ψc) ψd in
           let s₂' := nnrs_stmt_uncross_shadow_under s₂ (v::σ) ψc ψd in
           let problems :=  remove equiv_dec v (nnrs_stmt_free_mcenv_vars s₁')
                                   ++ remove equiv_dec v (nnrs_stmt_bound_mcenv_vars s₁')
                                   ++ remove equiv_dec v (nnrs_stmt_free_env_vars s₂')
                                   ++ remove equiv_dec v (nnrs_stmt_bound_env_vars s₂')
                                   ++ σ
                                   ++ ψd
                                   ++ ψc
                                   ++ nnrs_stmt_free_env_vars s₁'
                                   ++ nnrs_stmt_bound_env_vars s₁'
                                   ++ nnrs_stmt_free_mdenv_vars s₁'
                                   ++ nnrs_stmt_bound_mdenv_vars s₁'
                                   ++ nnrs_stmt_free_mcenv_vars s₂'
                                   ++ nnrs_stmt_bound_mcenv_vars s₂'
                                   ++ nnrs_stmt_free_mdenv_vars s₂'
                                   ++ nnrs_stmt_bound_mdenv_vars s₂' in
           let v' := fresh_var_from sep v problems in
           NNRSLetMutColl v' 
                          (mk_lazy_lift nnrs_stmt_rename_mc s₁' v v')
                          (mk_lazy_lift nnrs_stmt_rename_env s₂' v v')
         | NNRSAssign v e =>
           NNRSAssign v e
         | NNRSPush v e =>
           NNRSPush v e
         | NNRSFor v e s₀ =>
           let s₀' := nnrs_stmt_uncross_shadow_under s₀ (v::σ) ψc ψd in
           let problems := remove equiv_dec v (nnrs_stmt_free_env_vars s₀')
                                  ++ remove equiv_dec v (nnrs_stmt_bound_env_vars s₀')
                                  ++ (nnrs_stmt_free_mcenv_vars s₀')
                                  ++ (nnrs_stmt_bound_mcenv_vars s₀')
                                  ++ (nnrs_stmt_free_mdenv_vars s₀')
                                  ++ (nnrs_stmt_bound_mdenv_vars s₀') in
           let v' := fresh_var_from sep v problems in
           NNRSFor v' e (mk_lazy_lift nnrs_stmt_rename_env s₀' v v')
         | NNRSIf e s₁ s₂ =>
           NNRSIf
             e
             (nnrs_stmt_uncross_shadow_under s₁ σ ψc ψd)
             (nnrs_stmt_uncross_shadow_under s₂ σ ψc ψd)
         | NNRSEither e x₁ s₁ x₂ s₂ =>
           let s₁' := nnrs_stmt_uncross_shadow_under s₁ (x₁::σ) ψc ψd in
           let problems₁ :=  remove equiv_dec x₁ (nnrs_stmt_free_env_vars s₁')
                                    ++ remove equiv_dec x₁ (nnrs_stmt_bound_env_vars s₁')
                                    ++ (nnrs_stmt_free_mcenv_vars s₁')
                                    ++ (nnrs_stmt_bound_mcenv_vars s₁')
                                    ++ (nnrs_stmt_free_mdenv_vars s₁')
                                    ++ (nnrs_stmt_bound_mdenv_vars s₁') in
           let x₁' := fresh_var_from sep x₁ problems₁ in
           let s₂' := nnrs_stmt_uncross_shadow_under s₂ (x₂::σ) ψc ψd in
           let problems₂ := remove equiv_dec x₂ (nnrs_stmt_free_env_vars s₂')
                                   ++ remove equiv_dec x₂ (nnrs_stmt_bound_env_vars s₂')
                                   ++ (nnrs_stmt_free_mcenv_vars s₂')
                                   ++ (nnrs_stmt_bound_mcenv_vars s₂')
                                   ++ (nnrs_stmt_free_mdenv_vars s₂')
                                   ++ (nnrs_stmt_bound_mdenv_vars s₂') in
           let x₂' := fresh_var_from sep x₂ problems₂ in
           NNRSEither e
                      x₁'
                      (mk_lazy_lift nnrs_stmt_rename_env s₁' x₁ x₁')
                      x₂'
                      (mk_lazy_lift nnrs_stmt_rename_env s₂' x₂ x₂')
         end.

    Definition nnrs_uncross_shadow
               (s:nnrs)
      : nnrs
      :=
        let s' := nnrs_stmt_uncross_shadow_under (fst s) nil nil (snd s::nil) in
        let problems := nnrs_stmt_free_env_vars s'
                                                ++ nnrs_stmt_bound_env_vars s'
                                                ++ nnrs_stmt_free_mcenv_vars s'
                                                ++ nnrs_stmt_bound_mcenv_vars s' 
                                                ++ remove equiv_dec (snd s) (nnrs_stmt_free_mdenv_vars s')
                                                ++ remove equiv_dec (snd s) (nnrs_stmt_bound_mdenv_vars s') in
        let v' := fresh_var_from sep (snd s) problems in
        (mk_lazy_lift nnrs_stmt_rename_md s' (snd s) v', v').

  End uncross.

  (* nnrs_stmt_uncross_shadow_under does not affect free variables *)
  Section uncross_free.

    Ltac unlazy_tac := 
      try (apply mk_lazy_lift_prop;
         let H := fresh "eqq" in
         intros H; subst; try rewrite <- H; eauto).


    Ltac addremove_inclin_tac
      := let HH:= fresh "inn" in
         let HH2 := fresh "inn" in
         intros HH
         ; match type of HH with
             In ?fv ?l =>
             match fv with
             | (fresh_var_from _ ?v _) => assert (HH2:In fv (remove equiv_dec v l))
                 by (apply remove_in_neq; auto)
             end
           end; revert HH2
         ; apply fresh_var_from_incl_nin
         ; intros ? ?; repeat rewrite in_app_iff; tauto.

    Ltac freeuncross_t IH renH
      := unlazy_tac
         ; [rewrite IH; trivial
           | rewrite renH
             ; [rewrite IH
                ; apply remove_replace_all_nin
                ; addremove_inclin_tac
               | addremove_inclin_tac
           ]].

      Ltac fresh_prover
    :=
      repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_env_vars_rename_env)          
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_mcenv_vars_rename_env)
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mcenv_vars_rename_env)
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_mdenv_vars_rename_env)
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mdenv_vars_rename_env)
               
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_env_vars_rename_mcenv)
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_env_vars_rename_mcenv)
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mcenv_vars_rename_mcenv)
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_mdenv_vars_rename_mcenv)
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mdenv_vars_rename_mcenv)

      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_env_vars_rename_mdenv)
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_env_vars_rename_mdenv)
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_mcenv_vars_rename_mdenv)
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mcenv_vars_rename_mdenv)
      ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mdenv_vars_rename_mdenv)

      ; try solve [apply fresh_var_from_incl_nin
                   ; unfold incl; intros; repeat rewrite in_app_iff; intuition].

    Lemma nnrs_stmt_free_env_vars_uncross_under sep s σ ψc ψd :
      nnrs_stmt_free_env_vars (nnrs_stmt_uncross_shadow_under sep s σ ψc ψd) 
      = nnrs_stmt_free_env_vars s.
    Proof.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; intros σ ψc ψd
      ; simpl
      ; fresh_prover; eauto
      ; try rewrite IHs
      ; try rewrite IHs1
      ; try rewrite IHs2
      ; try rewrite IHs3; trivial
      ; try solve
            [f_equal; freeuncross_t IHs nnrs_stmt_free_env_vars_rename_env
            | f_equal; freeuncross_t IHs2 nnrs_stmt_free_env_vars_rename_env].
      - Case "NNRSEither"%string.
        f_equal.
        f_equal.
        + freeuncross_t IHs1 nnrs_stmt_free_env_vars_rename_env.
        + freeuncross_t IHs2 nnrs_stmt_free_env_vars_rename_env.
    Qed.

    Lemma nnrs_stmt_free_mdenv_vars_uncross_under sep s σ ψc ψd :
      nnrs_stmt_free_mdenv_vars (nnrs_stmt_uncross_shadow_under sep s σ ψc ψd) 
      = nnrs_stmt_free_mdenv_vars s.
    Proof.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; intros σ ψc ψd
      ; simpl
      ; fresh_prover; eauto
      ; try rewrite IHs
      ; try rewrite IHs1
      ; try rewrite IHs2
      ; try rewrite IHs3; trivial.
      - Case "NNRSLetMut"%string.
        f_equal.
        freeuncross_t IHs1 nnrs_stmt_free_mdenv_vars_rename_md.
    Qed.

    Lemma nnrs_stmt_free_mcenv_vars_uncross_under sep s σ ψc ψd :
      nnrs_stmt_free_mcenv_vars (nnrs_stmt_uncross_shadow_under sep s σ ψc ψd) 
      = nnrs_stmt_free_mcenv_vars s.
    Proof.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; intros σ ψc ψd
      ; simpl
      ; fresh_prover; eauto
      ; try rewrite IHs
      ; try rewrite IHs1
      ; try rewrite IHs2
      ; try rewrite IHs3; trivial.
      - Case "NNRSLetMutColl"%string.
        f_equal.
        freeuncross_t IHs1 nnrs_stmt_free_mcenv_vars_rename_mc.
    Qed.

  End uncross_free.

  Section correctness.

    Ltac fresh_prover
      :=
        repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_env_vars_rename_env)          
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_mcenv_vars_rename_env)
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mcenv_vars_rename_env)
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_mdenv_vars_rename_env)
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mdenv_vars_rename_env)
                 
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_env_vars_rename_mcenv)
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_env_vars_rename_mcenv)
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mcenv_vars_rename_mcenv)
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_mdenv_vars_rename_mcenv)
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mdenv_vars_rename_mcenv)

        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_env_vars_rename_mdenv)
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_env_vars_rename_mdenv)
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_free_mcenv_vars_rename_mdenv)
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mcenv_vars_rename_mdenv)
        ; repeat rewrite (mk_lazy_lift_under nnrs_stmt_bound_mdenv_vars_rename_mdenv)

        ; try solve [apply fresh_var_from_incl_nin
                     ; unfold incl; intros; repeat rewrite in_app_iff; intuition].
    
    Lemma nnrs_stmt_uncross_shadow_free_alt sep (s:nnrs_stmt)
          (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_alt 
        (nnrs_stmt_uncross_shadow_under sep s σ ψc ψd).
    Proof.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd; intros.
      - Case "NNRSSeq"%string.
        intuition.
      - Case "NNRSLet"%string.
        specialize (IHs (v::σ) ψc ψd).
        fresh_prover.
        repeat split; try fresh_prover.
        apply mk_lazy_lift_prop; trivial; intros neq.
        apply nnrs_stmt_cross_shadow_free_alt_rename_env; trivial
        ; apply fresh_var_from_incl_nin
        ; unfold incl; intros; repeat rewrite in_app_iff; tauto.
      - Case "NNRSLetMut"%string.
        specialize (IHs1 σ ψc (v::ψd)).
        specialize (IHs2 (v::σ) ψc ψd).
        fresh_prover.
        repeat split; try fresh_prover.
        + apply mk_lazy_lift_prop; trivial; intros neq.
          apply nnrs_stmt_cross_shadow_free_alt_rename_mdenv; trivial
          ; apply fresh_var_from_incl_nin
          ; unfold incl; intros; repeat rewrite in_app_iff; tauto.
        + apply mk_lazy_lift_prop; trivial; intros neq.
          apply nnrs_stmt_cross_shadow_free_alt_rename_env; trivial
          ; apply fresh_var_from_incl_nin
          ; unfold incl; intros; repeat rewrite in_app_iff; tauto.
      - Case "NNRSLetMutColl"%string.
        specialize (IHs1 σ (v::ψc) ψd).
        specialize (IHs2 (v::σ) ψc ψd).
        fresh_prover.
        repeat split; try fresh_prover.
        + apply mk_lazy_lift_prop; trivial; intros neq.
          apply nnrs_stmt_cross_shadow_free_alt_rename_mcenv; trivial
          ; apply fresh_var_from_incl_nin
          ; unfold incl; intros; repeat rewrite in_app_iff; tauto.
        + apply mk_lazy_lift_prop; trivial; intros neq.
          apply nnrs_stmt_cross_shadow_free_alt_rename_env; trivial
          ; apply fresh_var_from_incl_nin
          ; unfold incl; intros; repeat rewrite in_app_iff; tauto.
      - Case "NNRSAssign"%string.
        trivial.
      - Case "NNRSPush"%string.
        trivial.
      - Case "NNRSFor"%string.
        specialize (IHs (v::σ) ψc ψd).
        fresh_prover.
        repeat split; try fresh_prover.
        apply mk_lazy_lift_prop; trivial; intros neq.
        apply nnrs_stmt_cross_shadow_free_alt_rename_env; trivial
        ; apply fresh_var_from_incl_nin
        ; unfold incl; intros; repeat rewrite in_app_iff; tauto.
      - Case "NNRSIf"%string.
        intuition.
      - Case "NNRSEither"%string.
        specialize (IHs1 (v::σ) ψc ψd).
        specialize (IHs2 (v0::σ) ψc ψd).
        fresh_prover.
        repeat split; try fresh_prover
        ; apply mk_lazy_lift_prop; trivial; intros neq
        ; apply nnrs_stmt_cross_shadow_free_alt_rename_env; trivial
        ; apply fresh_var_from_incl_nin
        ; unfold incl; intros; repeat rewrite in_app_iff; tauto.
    Qed.

    Theorem nnrs_uncross_shadow_free sep (s:nnrs) :
      nnrs_cross_shadow_free (nnrs_uncross_shadow sep s).
    Proof.
      destruct s as [s ret]
      ; unfold nnrs_cross_shadow_free, nnrs_uncross_shadow; simpl.
      apply nnrs_stmt_cross_shadow_free_alt_under; simpl
      ; try apply disjoint_nil_r
      ; try
          (fresh_prover
           ; unfold disjoint; simpl; intros ? inn1 inn2; intuition; subst
           ; apply (fresh_var_from_nincl inn1)
           ; intros ? inn3
           ; repeat rewrite in_app_iff in *; tauto).
      apply mk_lazy_lift_prop; intros.
      - apply nnrs_stmt_uncross_shadow_free_alt.
      - apply nnrs_stmt_cross_shadow_free_alt_rename_mdenv; trivial
        ; try (apply fresh_var_from_incl_nin
               ; unfold incl; intros; repeat rewrite in_app_iff; tauto).
        apply nnrs_stmt_uncross_shadow_free_alt.
    Qed.

    Lemma nnrs_stmt_uncross_shadow_under_eval h c sep (s:nnrs_stmt) σ ψc ψd domσ domψc domψd :
      nnrs_stmt_eval h c σ ψc ψd (nnrs_stmt_uncross_shadow_under sep s domσ domψc domψd) = nnrs_stmt_eval h c σ ψc ψd s.
    Proof.

      Ltac prove_freshness 
        := match goal with
             [ H: ?v = fresh_var_from _ ?v _ -> False |- _ ] =>

             unfold fresh_var_from in H
             ; match_destr_in H; try congruence
             ; apply fresh_var_from_incl_nin
             ; let a := (fresh "a") in
               intros a inn; repeat rewrite in_app_iff in *
               ; destruct (a == v); unfold equiv, complement in *
               ; [subst; trivial
                 | eapply remove_in_neq in inn; eauto; try congruence
                 ]
           end.
      
      revert σ ψc ψd domσ domψc domψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd domσ domψc domψd.
      - Case "NNRSSeq"%string.
        rewrite IHs1.
        repeat match_destr.
      - Case "NNRSLet"%string.
        match_destr.
        unfold mk_lazy_lift.
        dest_eqdec.
        + rewrite <- e.
          rewrite IHs; trivial.
        + rewrite nnrs_stmt_eval_rename_env; try prove_freshness.
          rewrite IHs; trivial.
          case_eq (nnrs_stmt_eval h c ((v, Some d) :: σ) ψc ψd s )
          ; simpl; trivial; intros [[??]?] eqq.
          destruct p; trivial.
          destruct p; trivial.            
      - Case "NNRSLetMut"%string.
        unfold mk_lazy_lift.
        dest_eqdec.
        + rewrite <- e.
          rewrite IHs1.
          match_destr.
          destruct p as [[??]?]
          ; destruct m0; trivial
          ; destruct p0; trivial.
          rewrite IHs2; trivial.
        + rewrite nnrs_stmt_eval_rename_mdenv; try prove_freshness.
          rewrite IHs1.
          unfold var in *.
          case_eq (nnrs_stmt_eval h c σ ψc ((v, None) :: ψd) s1)
          ; simpl; trivial; intros [[??]?] eqq.
          destruct m0; trivial.
          destruct p0; simpl.
          rewrite nnrs_stmt_eval_rename_env; try prove_freshness.
          rewrite IHs2; trivial.
          unfold var in *.
          case_eq (nnrs_stmt_eval h c ((v, o) :: p) m m0 s2)
          ; simpl; trivial; intros [[??]?] eqq2.
          destruct p0; trivial.
          destruct p0; trivial.
      - Case "NNRSLetMutColl"%string.
        unfold mk_lazy_lift.
        dest_eqdec.
        + rewrite <- e.
          rewrite IHs1.
          match_destr.
          destruct p as [[??]?]
          ; destruct m; trivial
          ; destruct p0; trivial.
          rewrite IHs2; trivial.
        + rewrite nnrs_stmt_eval_rename_mcenv; try prove_freshness.
          rewrite IHs1.
          unfold var in *.
          case_eq (nnrs_stmt_eval h c σ ((v, nil) :: ψc) ψd s1)
          ; simpl; trivial; intros [[??]?] eqq.
          destruct m; trivial.
          destruct p0; simpl.
          rewrite nnrs_stmt_eval_rename_env; try prove_freshness.
          rewrite IHs2; trivial.
          unfold var in *.
          case_eq (nnrs_stmt_eval h c ((v, Some (dcoll l)) :: p) m m0 s2)
          ; simpl; trivial; intros [[??]?] eqq2.
          destruct p0; trivial.
          destruct p0; trivial.
      - Case "NNRSAssign"%string.
        trivial.
      - Case "NNRSPush"%string.
        trivial.
      - Case "NNRSFor"%string.
        match_destr.
        unfold mk_lazy_lift.
        dest_eqdec.
        + rewrite <- e.
          clear e.
          destruct d; trivial.
          revert σ ψc ψd domσ domψc domψd.
          induction l
          ; simpl; intros σ ψc ψd domσ domψc domψd; trivial.
          rewrite IHs; trivial.
          match_destr.
          destruct p as [[??]?].
          destruct p; trivial.
          unfold var in *.
          apply (IHl p0 m m0 domσ domψc domψd).
        + destruct d; trivial.
          revert σ ψc ψd domσ domψc domψd c0.
          induction l
          ; simpl; intros σ ψc ψd domσ domψc domψd c0; trivial.
          rewrite nnrs_stmt_eval_rename_env; try prove_freshness.
          rewrite IHs.
          case_eq ( nnrs_stmt_eval h c ((v, Some a) :: σ) ψc ψd s); trivial
          ; intros [[??]?] eqq2.
          destruct p; trivial.
          destruct p; trivial.
          unfold var in *.
          apply (IHl p0 m m0 domσ domψc domψd); trivial.
      - Case "NNRSIf"%string.
        match_destr.
        destruct d; trivial.
        destruct b; eauto.
      - Case "NNRSEither"%string.
        match_destr.
        destruct d; trivial.
        + unfold mk_lazy_lift.
          dest_eqdec.
          *  rewrite <- e.
             rewrite IHs1; trivial.
          * rewrite nnrs_stmt_eval_rename_env; try prove_freshness.
            rewrite IHs1; trivial.
            case_eq (nnrs_stmt_eval h c ((v, Some d) :: σ) ψc ψd s1 )
            ; simpl; trivial; intros [[??]?] eqq.
            destruct p; trivial.
            destruct p; trivial.            
        + unfold mk_lazy_lift.
          dest_eqdec.
          *  rewrite <- e.
             rewrite IHs2; trivial.
          * rewrite nnrs_stmt_eval_rename_env; try prove_freshness.
            rewrite IHs2; trivial.
            case_eq (nnrs_stmt_eval h c ((v0, Some d) :: σ) ψc ψd s2 )
            ; simpl; trivial; intros [[??]?] eqq.
            destruct p; trivial.
            destruct p; trivial.            
    Qed.

    Theorem nnrs_uncross_shadow_eval h c sep (s:nnrs) :
      nnrs_eval h c (nnrs_uncross_shadow sep s) = nnrs_eval h c s.
    Proof.
      destruct s as [s ret]
      ; unfold nnrs_cross_shadow_free, nnrs_uncross_shadow; simpl.
      unfold mk_lazy_lift.
      dest_eqdec.
      + rewrite <- e.
        rewrite nnrs_stmt_uncross_shadow_under_eval; trivial.
      + rewrite nnrs_stmt_eval_rename_mdenv
        ; [| try prove_freshness ; intuition..].

        rewrite nnrs_stmt_uncross_shadow_under_eval; trivial.
        destruct (nnrs_stmt_eval h c nil nil ((ret, None) :: nil) s); trivial.
        destruct p as [[??]?].
        destruct m0; simpl; trivial.
        destruct p0; trivial.
    Qed. 

  End correctness.

  Section idempotence.

    Ltac disj_tac :=
      repeat progress
             (repeat rewrite in_app_iff in *
              ; try match goal with
                    | [ H : disjoint (_ ++ _) _ |- _ ] => apply disjoint_app_l in H; destruct H
                    | [ H : disjoint (_ :: _) _ |- _ ] => apply disjoint_cons_inv1 in H; destruct H
                    | [ H : disjoint _ (_ :: _) |- _ ] => apply disjoint_cons_inv2 in H; destruct H
                    | [H1:disjoint (remove _ ?v ?l1) ?l2,
                          H2:In ?v ?l1 -> False |- _ ] => rewrite nin_remove in H1 by apply H2
                    | [H1:disjoint (remove _ ?v ?l1) ?l2,
                          H2:~ In ?v ?l1 |- _ ] => rewrite nin_remove in H1 by apply H2
                    | [H1:disjoint (remove _ ?v ?l1) ?l2,
                          H2:In ?v ?l2 -> False |- _ ] => rewrite disjoint_remove_swap in H1; rewrite nin_remove in H1 by apply H2
                    | [H1:disjoint (remove _ ?v ?l1) ?l2,
                          H2:~ In ?v ?l2 |- _ ] => rewrite disjoint_remove_swap in H1; rewrite nin_remove in H1 by apply H2
                    | [H : In _ (replace_all _ _ _ ) |- _ ] => apply in_replace_all in H; try solve [destruct H as [?|[??]]; subst; eauto]
                    | [H: ~ In _ (remove _ _ _) |- _ ] => try rewrite <- remove_in_neq in H by congruence
                    | [H: In _ (remove _ _ _) -> False |- _ ] => try rewrite <- remove_in_neq in H by congruence
                    | [ |- disjoint (_ :: _) _ ] => apply disjoint_cons1
                    | [ |- disjoint _ (_ :: _) ] => apply disjoint_cons2
                    | [ |- disjoint _ (replace_all _ _ _ )] => try solve [apply disjoint_replace_all; intuition]
                    | [ H: In _ (remove _ _ _) |- _ ] => apply remove_inv in H; destruct H; try congruence
                    end
             ).
    
    Lemma nnrs_stmt_uncross_shadow_under_alt_id sep (s:nnrs_stmt) :
      nnrs_stmt_cross_shadow_free_alt s ->
      forall (σ ψc ψd:list var),
        disjoint (nnrs_stmt_free_mcenv_vars s) σ ->
        disjoint (nnrs_stmt_bound_mcenv_vars s) σ ->
        disjoint (nnrs_stmt_free_mdenv_vars s) σ ->
        disjoint (nnrs_stmt_bound_mdenv_vars s) σ ->
        disjoint (nnrs_stmt_free_env_vars s) ψc ->
        disjoint (nnrs_stmt_bound_env_vars s) ψc ->
        disjoint (nnrs_stmt_free_mdenv_vars s) ψc ->
        disjoint (nnrs_stmt_bound_mdenv_vars s) ψc ->
        disjoint (nnrs_stmt_free_env_vars s) ψd ->
        disjoint (nnrs_stmt_bound_env_vars s) ψd ->
        disjoint (nnrs_stmt_free_mcenv_vars s) ψd ->
        disjoint (nnrs_stmt_bound_mcenv_vars s) ψd ->
        nnrs_stmt_uncross_shadow_under sep s σ ψc ψd = s.
    Proof.
      Ltac ucsid_tac := repeat intuition disj_tac.
      
      nnrs_stmt_cases (induction s) Case
      ; simpl; intros sf σ ψc ψd
      ; intros; disj_tac.
      - Case "NNRSSeq"%string.
        rewrite IHs1, IHs2; intuition.
      - Case "NNRSLet"%string.
        destruct sf as [sf1 [sf2 [nin1 [nin2 sf]]]].
        rewrite IHs; ucsid_tac.
        rewrite fresh_var_from_id; ucsid_tac.
        rewrite mk_lazy_lift_id; trivial.
      - Case "NNRSLetMut"%string.
        destruct sf as [nin1 [nin2 [nin3 [sf1 sf2]]]].
        rewrite IHs1 by ucsid_tac.
        rewrite IHs2 by ucsid_tac.
        rewrite fresh_var_from_id by ucsid_tac.
        repeat rewrite mk_lazy_lift_id; trivial.
      - Case "NNRSLetMutColl"%string.
        destruct sf as [nin1 [nin2 [nin3 [sf1 sf2]]]].
        rewrite IHs1 by ucsid_tac.
        rewrite IHs2 by ucsid_tac.
        rewrite fresh_var_from_id by ucsid_tac.
        repeat rewrite mk_lazy_lift_id; trivial.
      - Case "NNRSAssign"%string.
        trivial.
      - Case "NNRSPush"%string.
        trivial.
      - Case "NNRSFor"%string.
        destruct sf as [sf1 [sf2 [nin1 [nin2 sf]]]].
        rewrite IHs by ucsid_tac.
        rewrite fresh_var_from_id by ucsid_tac.
        rewrite mk_lazy_lift_id; trivial.
      - Case "NNRSIf"%string.
        rewrite IHs1, IHs2; tauto.
      - Case "NNRSEither"%string.
        destruct sf as [disj1 [disj2 [nin11 [nin12 [nin21 [nin22 [sf1 sf2]]]]]]].
        rewrite IHs1, IHs2 by ucsid_tac.
        repeat rewrite fresh_var_from_id by ucsid_tac.
        repeat rewrite mk_lazy_lift_id; trivial.
    Qed.

    Lemma nnrs_stmt_uncross_shadow_under_id sep (s:nnrs_stmt)  (σ ψc ψd:list var) :
      nnrs_stmt_cross_shadow_free_under s σ ψc ψd ->
      nnrs_stmt_uncross_shadow_under sep s σ ψc ψd = s.
    Proof.
      Hint Resolve nnrs_stmt_cross_shadow_free_under_alt
           nnrs_stmt_cross_shadow_free_under_free_mcenv_env
           nnrs_stmt_cross_shadow_free_under_bound_mcenv_env
           nnrs_stmt_cross_shadow_free_under_free_mdenv_env
           nnrs_stmt_cross_shadow_free_under_bound_mdenv_env
           nnrs_stmt_cross_shadow_free_under_free_env_mcenv
           nnrs_stmt_cross_shadow_free_under_bound_env_mcenv
           nnrs_stmt_cross_shadow_free_under_free_mdenv_mcenv
           nnrs_stmt_cross_shadow_free_under_bound_mdenv_mcenv
           nnrs_stmt_cross_shadow_free_under_free_env_mdenv
           nnrs_stmt_cross_shadow_free_under_bound_env_mdenv
           nnrs_stmt_cross_shadow_free_under_free_mcenv_mdenv
           nnrs_stmt_cross_shadow_free_under_bound_mcenv_mdenv.
      
      intros cs.
      apply nnrs_stmt_uncross_shadow_under_alt_id; eauto.
    Qed.

    Theorem nnrs_uncross_shadow_id sep (s:nnrs) :
      nnrs_cross_shadow_free s ->
      nnrs_uncross_shadow sep s = s.
    Proof.
      destruct s.
      unfold nnrs_cross_shadow_free, nnrs_uncross_shadow
      ; simpl in *.
      intros cs.
      rewrite nnrs_stmt_uncross_shadow_under_id by trivial.
      rewrite fresh_var_from_id.
      - rewrite mk_lazy_lift_id; trivial.
      - repeat rewrite in_app_iff.
        intuition.
        + apply nnrs_stmt_cross_shadow_free_under_free_env_mdenv in cs.
          disj_tac; tauto.
        + apply nnrs_stmt_cross_shadow_free_under_bound_env_mdenv in cs.
          disj_tac; tauto.
        + apply nnrs_stmt_cross_shadow_free_under_free_mcenv_mdenv in cs.
          disj_tac; tauto.
        + apply nnrs_stmt_cross_shadow_free_under_bound_mcenv_mdenv in cs.
          disj_tac; tauto.
        + disj_tac.
        + disj_tac.
    Qed.

    Lemma nnrs_uncross_shadow_idempotent' sep sep2 (s:nnrs) :
      nnrs_uncross_shadow sep2 (nnrs_uncross_shadow sep s) = (nnrs_uncross_shadow sep s).
    Proof.
      destruct s as [s ret].
      rewrite nnrs_uncross_shadow_id; trivial.
      apply nnrs_uncross_shadow_free.
    Qed.

    Theorem nnrs_uncross_shadow_idempotent sep  (s:nnrs) :
      nnrs_uncross_shadow sep (nnrs_uncross_shadow sep s) = (nnrs_uncross_shadow sep s).
    Proof.
      apply nnrs_uncross_shadow_idempotent'.
    Qed.
    
  End idempotence.
  
  Section core.
    
    Lemma nnrs_stmt_uncross_shadow_under_preserves_core_f sep (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmtIsCore s ->
      nnrs_stmtIsCore (nnrs_stmt_uncross_shadow_under sep s σ ψc ψd).
    Proof.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf.
      - Case "NNRSSeq"%string.
        intuition.
      - Case "NNRSLet"%string.
        destruct sf as [sf1 sf2]; split; trivial.
        apply mk_lazy_lift_prop; [eauto | intros].
        apply nnrs_stmt_rename_env_core_f.
        eauto.
      - Case "NNRSLetMut"%string.
        destruct sf as [sf1 sf2]; split; trivial.
        apply mk_lazy_lift_prop; [eauto | intros].
        + apply nnrs_stmt_rename_md_core; eauto.
        + apply mk_lazy_lift_prop; [eauto | intros].
          apply nnrs_stmt_rename_env_core; eauto.
      - Case "NNRSLetMutColl"%string.
        destruct sf as [sf1 sf2]; split; trivial.
        apply mk_lazy_lift_prop; [eauto | intros].
        + apply nnrs_stmt_rename_mc_core; eauto.
        + apply mk_lazy_lift_prop; [eauto | intros].
          apply nnrs_stmt_rename_env_core; eauto.
      - Case "NNRSAssign"%string.
        trivial.
      - Case "NNRSPush"%string.
        trivial.
      - Case "NNRSFor"%string.
        destruct sf as [sf1 sf2]; split; trivial.
        apply mk_lazy_lift_prop; [eauto | intros].
        apply nnrs_stmt_rename_env_core.
        eauto.
      - Case "NNRSIf"%string.
        intuition.
      - Case "NNRSEither"%string.
        destruct sf as [sf1 sf2]; split; trivial.
        split
        ; (apply mk_lazy_lift_prop; [intuition | intros]
           ; apply nnrs_stmt_rename_env_core
           ; intuition).
    Qed.

    Lemma nnrs_stmt_uncross_shadow_under_preserves_core_b sep (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmtIsCore (nnrs_stmt_uncross_shadow_under sep s σ ψc ψd) ->
      nnrs_stmtIsCore s.
    Proof.
      revert σ ψc ψd
      ; nnrs_stmt_cases (induction s) Case
      ; simpl; intros σ ψc ψd sf.
      - Case "NNRSSeq"%string.
        intuition eauto.
      - Case "NNRSLet"%string.
        destruct sf as [sf1 sf2]; split; trivial.
        apply mk_lazy_lift_prop_inv in sf2.
        destruct sf2 as [[??]|[sf2 a]]; [eauto|].
        apply nnrs_stmt_rename_env_core in a; eauto.
      - Case "NNRSLetMut"%string.
        destruct sf as [sf1 sf2].
        split.
        + apply mk_lazy_lift_prop_inv in sf1.
          destruct sf1 as [[??]|[sf1 a]]; [eauto|].
          apply nnrs_stmt_rename_md_core in a; eauto.
        + apply mk_lazy_lift_prop_inv in sf2.
          destruct sf2 as [[??]|[sf2 a]]; [eauto|].
          apply nnrs_stmt_rename_env_core in a; eauto.
      - Case "NNRSLetMutColl"%string.
        destruct sf as [sf1 sf2].
        split.
        + apply mk_lazy_lift_prop_inv in sf1.
          destruct sf1 as [[??]|[sf1 a]]; [eauto|].
          apply nnrs_stmt_rename_mc_core in a; eauto.
        + apply mk_lazy_lift_prop_inv in sf2.
          destruct sf2 as [[??]|[sf2 a]]; [eauto|].
          apply nnrs_stmt_rename_env_core in a; eauto.
      - Case "NNRSAssign"%string.
        trivial.
      - Case "NNRSPush"%string.
        trivial.
      - Case "NNRSFor"%string.
        destruct sf as [sf1 sf2]; split; trivial.
        apply mk_lazy_lift_prop_inv in sf2.
        destruct sf2 as [[??]|[sf2 a]]; [eauto|].
        apply nnrs_stmt_rename_env_core in a.
        eauto.
      - Case "NNRSIf"%string.
        intuition eauto.
      - Case "NNRSEither"%string.
        destruct sf as [sf1 [sf2 sf3]]; split; trivial.
        split.
        + apply mk_lazy_lift_prop_inv in sf2.
          destruct sf2 as [[??]|[sf2 a]]; [eauto|].
          apply nnrs_stmt_rename_env_core in a.
          eauto.
        + apply mk_lazy_lift_prop_inv in sf3.
          destruct sf3 as [[??]|[sf3 a]]; [eauto|].
          apply nnrs_stmt_rename_env_core in a.
          eauto.
    Qed.

    Lemma nnrs_stmt_uncross_shadow_under_preserves_core
          sep (s:nnrs_stmt) (σ ψc ψd:list var) :
      nnrs_stmtIsCore (nnrs_stmt_uncross_shadow_under sep s σ ψc ψd) <->
      nnrs_stmtIsCore s.
    Proof.
      split.
      - apply  nnrs_stmt_uncross_shadow_under_preserves_core_b.
      - apply  nnrs_stmt_uncross_shadow_under_preserves_core_f.
    Qed.
    
    Theorem nnrs_uncross_shadow_preserves_core sep (s:nnrs) :
      nnrsIsCore (nnrs_uncross_shadow sep s) <->
      nnrsIsCore s.
    Proof.
      destruct s as [s ret]
      ; unfold nnrsIsCore, nnrs_cross_shadow_free, nnrs_uncross_shadow; simpl.
      apply mk_lazy_lift_prop; intros.
      - apply nnrs_stmt_uncross_shadow_under_preserves_core.
      - split; intros HH.
        + apply nnrs_stmt_rename_md_core in HH; eauto.
          eapply nnrs_stmt_uncross_shadow_under_preserves_core; eauto.
        + apply nnrs_stmt_rename_md_core; eauto.
          apply nnrs_stmt_uncross_shadow_under_preserves_core; trivial.
    Qed.

  End core.
  Section examples.

    Local Open Scope nnrs.
    Local Open Scope string.

    Example expr1 : nnrs_stmt
      := NNRSLet "x"
                 (NNRSConst (dnat 3))
                 (NNRSLetMutColl
                    "x"
                    (NNRSLetMutColl
                       "y"
                       (NNRSLetMutColl
                          "x"
                          (NNRSLetMut
                             "x"
                             (NNRSAssign "x" (NNRSConst (dnat 5)))
                             (NNRSPush "x" (NNRSConst (dnat 4))))
                          (NNRSPush "x" (NNRSConst (dnat 6))))
                       (NNRSPush "x" (NNRSConst (dnat 7))))
                    (NNRSAssign "ret" (NNRSConst (dnat 8)))).
    (*    Eval vm_compute in (nnrs_stmt_uncross_shadow_under "$" expr1 nil nil nil). *)
    
    Example expr2 : nnrs_stmt
      := NNRSLet "x"
                 (NNRSConst (dnat 3))
                 (NNRSLetMutColl
                    "x"
                    (NNRSPush "x" (NNRSConst (dnat 8)))
                    (NNRSAssign "ret" (NNRSConst (dnat 8)))).

    (*    Eval vm_compute in (nnrs_stmt_uncross_shadow_under "$" expr2 nil nil nil). *)

    Example expr3 : nnrs_stmt
      := (NNRSLetMut
            "x"
            (NNRSPush "x" (NNRSConst (dnat 8)))
            (NNRSAssign "ret" (NNRSConst (dnat 8)))).

    (*    Eval vm_compute in (nnrs_stmt_uncross_shadow_under "$" expr3 nil nil nil). *)
    
  End examples.

End NNRSCrossShadow.
