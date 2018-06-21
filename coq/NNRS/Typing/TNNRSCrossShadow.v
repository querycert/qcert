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
Require Import CommonSystem.
Require Import NNRS.
Require Import NNRSEval.
Require Import NNRSVars.
Require Import NNRSRename.
Require Import NNRSCrossShadow.
Require Import TNNRS.
Require Import TNNRSRename.

Section TNNRSCrossShadow.
  
  Context {m:basic_model}.

  Local Open Scope nnrs.

  Lemma nnrs_stmt_must_assign_uncross_shadow_under_f sep s σ ψc ψd v :
    nnrs_stmt_must_assign s v ->
    nnrs_stmt_must_assign (nnrs_stmt_uncross_shadow_under sep s σ ψc ψd) v.
  Proof.

    Ltac maus_tac := 
      try (apply mk_lazy_lift_prop;
           let H := fresh "eqq" in
           intros H; subst; try rewrite <- H; eauto)
      ; try (apply nnrs_stmt_must_assign_rename_env; eauto)
      ; try (apply nnrs_stmt_must_assign_rename_mc; eauto).

    revert σ ψc ψd
    ; nnrs_stmt_cases (induction s) Case
    ; simpl; intros σ ψc ψd
    ; try solve [intuition eauto]
    ; intros ma.
    - Case "NNRSLet"%string.
      repeat maus_tac.
    - Case "NNRSLetMut"%string.
      destruct ma as [[neq ma]|ma].
      + apply mk_lazy_lift_prop; intros eqq
        ; [repeat rewrite <- eqq; eauto |].
        assert (inn: In v (remove equiv_dec v0
                                  (nnrs_stmt_free_mdenv_vars (nnrs_stmt_uncross_shadow_under sep s1 σ ψc (v0 :: ψd))))).
        { apply remove_in_neq; [congruence| ].
          apply nnrs_stmt_must_assign_is_free.
          apply IHs1; trivial.
        }
        left.
        split; [|  apply nnrs_stmt_must_assign_rename_md_neq; eauto]
        ; intros ?; subst
        ; apply fresh_var_from_nincl in inn
        ; apply inn; intros ??
        ; repeat rewrite in_app_iff; tauto.
      + right.
        apply mk_lazy_lift_prop; intros eqq
        ; [repeat rewrite <- eqq; eauto |].
        apply nnrs_stmt_must_assign_rename_env; eauto.
    - Case "NNRSLetMutColl"%string.
      repeat maus_tac; intuition eauto.
      + left.
        apply nnrs_stmt_must_assign_rename_mc; eauto.
      + right.
        apply nnrs_stmt_must_assign_rename_env; eauto.
    - Case "NNRSEither"%string.
      repeat maus_tac; intuition eauto
      ; try apply nnrs_stmt_must_assign_rename_env; eauto.
  Qed.

  Lemma nnrs_stmt_must_assign_uncross_shadow_under_b sep s σ ψc ψd v :
    nnrs_stmt_must_assign (nnrs_stmt_uncross_shadow_under sep s σ ψc ψd) v ->
    nnrs_stmt_must_assign s v.
  Proof.
    revert σ ψc ψd
    ; nnrs_stmt_cases (induction s) Case
    ; simpl; intros σ ψc ψd
    ; try solve [intuition eauto]
    ; intros ma.
    - Case "NNRSLet"%string.
      apply mk_lazy_lift_prop_inv in ma.
      destruct ma as [[eqq ma]|[eqq ma]]
      ; subst; eauto.
      apply nnrs_stmt_must_assign_rename_env in ma; eauto.
    - Case "NNRSLetMut"%string.
      apply mk_lazy_lift_prop_inv in ma.
      destruct ma as [[eqq ma]|[eqq ma]]
      ; subst; eauto.
      + rewrite <- eqq in ma.
        destruct ma as [[eqq2 ma2]|eqq2]; eauto.
        apply mk_lazy_lift_prop_inv in eqq2.
        intuition eauto.
      + destruct ma as [[eqq2 ma2]|eqq2].
        *
          assert (neq:v <> v0).
          {
            apply nnrs_stmt_must_assign_is_free in ma2.
            apply nnrs_stmt_free_mdenv_vars_rename_mdenv_in in ma2.
            intuition.
          }
          apply nnrs_stmt_must_assign_rename_md_neq in ma2; eauto.
        * apply mk_lazy_lift_prop_inv in eqq2.
          intuition eauto.
          apply nnrs_stmt_must_assign_rename_env in H0; eauto.
    - Case "NNRSLetMutColl"%string.
      apply mk_lazy_lift_prop_inv in ma.
      destruct ma as [[eqq ma]|[eqq ma]]
      ; subst; eauto.
      + rewrite <- eqq in ma.
        apply mk_lazy_lift_prop_inv in ma.
        intuition eauto.
      + destruct ma as [ma|ma].
        * apply nnrs_stmt_must_assign_rename_mc in ma; eauto.
        * apply mk_lazy_lift_prop_inv in ma.
          destruct ma as [[? ma]|[? ma]]
          ; subst; eauto.
          eapply nnrs_stmt_must_assign_rename_env in ma; eauto.
    - Case "NNRSEither"%string.
      apply mk_lazy_lift_prop_inv in ma.
      destruct ma as [[eqq ma]|[eqq ma]]
      ; subst; eauto.
      + destruct ma as [ma1 ma2].
        split; eauto.
        apply mk_lazy_lift_prop_inv in ma2.
        destruct ma2 as [[? ma2]|[? ma2]]
        ; subst; eauto.
        eapply nnrs_stmt_must_assign_rename_env in ma2; eauto.
      + destruct ma as [ma1 ma2].
        split.
        * eapply nnrs_stmt_must_assign_rename_env in ma1; eauto.
        * apply mk_lazy_lift_prop_inv in ma2.
          destruct ma2 as [[? ma2]|[? ma2]]
          ; subst; eauto.
          eapply nnrs_stmt_must_assign_rename_env in ma2; eauto.
  Qed.

  Lemma nnrs_stmt_must_assign_uncross_shadow_under sep s σ ψc ψd v :
    nnrs_stmt_must_assign (nnrs_stmt_uncross_shadow_under sep s σ ψc ψd) v <->
    nnrs_stmt_must_assign s v.
  Proof.
    split; intros.
    - eapply nnrs_stmt_must_assign_uncross_shadow_under_b; eauto.
    - eapply nnrs_stmt_must_assign_uncross_shadow_under_f; eauto.
  Qed.


  Ltac prove_freshness 
    := match goal with
       | [ H: ?v = fresh_var_from _ ?v _ -> False |- _ ] =>
         
         unfold fresh_var_from in H
         ; match_destr_in H; try congruence
         ; apply fresh_var_from_incl_nin
         ; let a := (fresh "a") in
           intros a inn; repeat rewrite in_app_iff in *
           ; destruct (a == v); unfold equiv, complement in *
           ; [subst; trivial
             | eapply remove_in_neq in inn; eauto; try congruence
             ]
       | [ H: ?v <> fresh_var_from _ ?v _  |- _ ] =>
         
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

  Lemma nnrs_stmt_uncross_shadow_under_type_f {Γc Γ Δc Δd s} sep σ ψc ψd :
    [ Γc ; Γ , Δc , Δd  ⊢ s ] ->
    [ Γc ; Γ , Δc , Δd  ⊢ nnrs_stmt_uncross_shadow_under sep s σ ψc ψd ].
  Proof.
    
    Ltac lazy_fresh_rename_tac :=
      apply mk_lazy_lift_prop
      ; intros eqq; [rewrite <- eqq; eauto | ]
      ; (apply nnrs_stmt_type_rename_env_in_cons
         || apply nnrs_stmt_type_rename_mcenv_in_cons
         || apply nnrs_stmt_type_rename_mdenv_in_cons)
      ; trivial; eauto
      ; prove_freshness.
    
    
    revert Γ Δc Δd σ ψc ψd
    ; nnrs_stmt_cases (induction s) Case
    ; simpl
    ; intros Γ Δc Δd σ ψc ψd typ
    ; invcs typ
    ; try solve [econstructor; eauto; lazy_fresh_rename_tac].
    - Case "NNRSLetMut"%string.
      econstructor; eauto
      ; try lazy_fresh_rename_tac.
      + apply mk_lazy_lift_prop
        ; intros eqq; [rewrite <- eqq; eauto | ].
        * apply nnrs_stmt_must_assign_uncross_shadow_under; trivial.
        * { apply nnrs_stmt_must_assign_rename_md_eq_f; eauto.
            - prove_freshness.
            - apply nnrs_stmt_must_assign_uncross_shadow_under; trivial.
          }
  Qed.

  Lemma nnrs_stmt_uncross_shadow_under_type_b {Γc Γ Δc Δd s sep σ ψc ψd} :
    [ Γc ; Γ , Δc , Δd  ⊢ nnrs_stmt_uncross_shadow_under sep s σ ψc ψd ] ->
    [ Γc ; Γ , Δc , Δd  ⊢ s ].
  Proof.

    Ltac lazy_fresh_rename_in_tac HH :=
      apply mk_lazy_lift_prop_inv in HH
      ; let ma := fresh "ma" in
        let eqq := fresh "eqq" in
        destruct HH as [[eqq ma]|[eqq ma]]
        ; [try rewrite <- eqq in *; eauto | ]
        ; (apply nnrs_stmt_type_rename_env_in_cons in ma
                                                      || apply nnrs_stmt_type_rename_mcenv_in_cons in ma
                                                                                                      || apply nnrs_stmt_type_rename_mdenv_in_cons in ma)
        ; trivial; eauto
        ; prove_freshness.

    Ltac try_lazy_fresh_rename_in_tac
      := try match goal with 
               [H: nnrs_stmt_type _ _ _ _ _  |- _ ] => solve[lazy_fresh_rename_in_tac H]
             end.
    
    revert Γ Δc Δd σ ψc ψd
    ; nnrs_stmt_cases (induction s) Case
    ; simpl
    ; intros Γ Δc Δd σ ψc ψd typ
    ; invcs typ
    ; try solve [
            econstructor
            ; eauto
            ; try_lazy_fresh_rename_in_tac].
    - Case "NNRSLetMut"%string.
      econstructor; try_lazy_fresh_rename_in_tac.
      + apply mk_lazy_lift_prop_inv in H5.
        destruct H5 as [[? ma]|[? ma]]
        ; subst; eauto.
        * rewrite <- H in ma.
          apply nnrs_stmt_must_assign_uncross_shadow_under in ma; trivial.
        * apply nnrs_stmt_must_assign_rename_md_eq_b in ma
          ; try prove_freshness.
          apply nnrs_stmt_must_assign_uncross_shadow_under in ma; trivial.
  Qed.
  
  Lemma nnrs_stmt_uncross_shadow_under_type Γc Γ Δc Δd s sep σ ψc ψd :
    [ Γc ; Γ , Δc , Δd  ⊢ nnrs_stmt_uncross_shadow_under sep s σ ψc ψd ] <->
    [ Γc ; Γ , Δc , Δd  ⊢ s ].
  Proof.
    split; intros.
    - eapply nnrs_stmt_uncross_shadow_under_type_b; eauto.
    - eapply nnrs_stmt_uncross_shadow_under_type_f; eauto.
  Qed.

  Lemma nnrs_uncross_shadow_type_f {Γc si τ} sep :
    [ Γc ⊢ si ▷ τ ] ->
    [ Γc ⊢ nnrs_uncross_shadow sep si ▷ τ ].
  Proof.
    destruct si; simpl; intros typ.
    maus_tac.
    - apply nnrs_stmt_uncross_shadow_under_type_f; eauto.
    - apply nnrs_stmt_type_rename_mdenv_in_cons; eauto
      ; try solve [prove_freshness; intuition].
      apply nnrs_stmt_uncross_shadow_under_type_f; eauto.
  Qed.
      
  Lemma nnrs_uncross_shadow_type_b {Γc si τ sep} :
    [ Γc ⊢ nnrs_uncross_shadow sep si ▷ τ ] ->
    [ Γc ⊢ si ▷ τ ].
  Proof.
    destruct si; simpl; intros typ.
    apply mk_lazy_lift_prop_inv in typ.
    destruct typ as [[eqq ma]|[eqq ma]]
    ; [try rewrite <- eqq in *; eauto | ].
    - apply nnrs_stmt_uncross_shadow_under_type_b in ma; trivial.
    - apply nnrs_stmt_type_rename_mdenv_in_cons in ma
      ; try solve [prove_freshness; intuition].
      apply nnrs_stmt_uncross_shadow_under_type_b in ma; trivial.
  Qed.

  Theorem nnrs_uncross_shadow_type Γc si τ sep :
    [ Γc ⊢ nnrs_uncross_shadow sep si ▷ τ ] <->
    [ Γc ⊢ si ▷ τ ].
  Proof.
    split; intros.
    - eapply nnrs_uncross_shadow_type_b; eauto.
    - eapply nnrs_uncross_shadow_type_f; eauto.
  Qed.

End TNNRSCrossShadow.