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
Require Import NNRSimp.
Require Import NNRSimpVars.
Require Import NNRSimpUsage.
Require Import NNRSimpRename.
Require Import TNNRSimp.

Section TNNRSimpRename.
  Local Open Scope nnrs_imp.

  Context {m:basic_model}.

  Hint Constructors nnrs_imp_expr_type.
  Hint Constructors nnrs_imp_stmt_type.

  Lemma nnrs_imp_expr_type_rename_in_f Γc l Γ e (v v':var) τ (τo:rtype) :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_imp_expr_free_vars e) ->
    [ Γc ; (l++(v,τ)::Γ)  ⊢ e ▷ τo ] ->
    [ Γc ; (l++(v',τ)::Γ)  ⊢ nnrs_imp_expr_rename e v v' ▷ τo ]%nnrs_imp_scope.
  Proof.
    revert τo.
    nnrs_imp_expr_cases (induction e) Case; simpl; trivial
    ; intros τo ??? typ
    ; invcs typ
    ; repeat rewrite in_app_iff in *
    ; eauto 3.
    -  Case "NNRSimpVar"%string.
       econstructor.
       repeat rewrite lookup_app in *.
       destruct (equiv_dec v0 v); unfold equiv, complement in *
       ; subst.
       + repeat match_option
         ; try solve [(try apply lookup_in_domain in eqq
                       ; try apply lookup_in_domain in eqq0; try contradiction)].
         repeat match_option_in H4
         ; try solve [(try apply lookup_in_domain in eqq
                       ; try apply lookup_in_domain in eqq0; try contradiction)].
         simpl in *.
         match_destr_in H4; try congruence.
         match_destr; try congruence.
       + match_option; simpl.
         * rewrite eqq in H4; trivial.
         * rewrite eqq in H4; simpl in *.
           match_destr_in H4; try congruence.
           match_destr; try congruence.
           intuition.
    - Case "NNRSimpBinop"%string.
      econstructor; eauto.
  Qed.

  Lemma nnrs_imp_expr_type_rename_f Γc Γ e (v v':var) τ (τo:rtype) :
    ~ In v' (nnrs_imp_expr_free_vars e) ->
    [ Γc ; ((v,τ)::Γ)  ⊢ e ▷ τo ] ->
    [ Γc ; ((v',τ)::Γ)  ⊢ nnrs_imp_expr_rename e v v' ▷ τo ]%nnrs_imp_scope.
  Proof.
    intros.
    apply (nnrs_imp_expr_type_rename_in_f Γc nil Γ); simpl; tauto.
  Qed.

  Lemma nnrs_imp_stmt_type_rename_in_f Γc l Γ s (v v':var) τ :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_imp_stmt_free_vars s) ->
    ~ In v' (nnrs_imp_stmt_bound_vars s) ->
    [ Γc ; (l++(v,τ)::Γ)   ⊢ s ] ->
    [ Γc ; (l++(v',τ)::Γ) ⊢ nnrs_imp_stmt_rename s v v' ].
  Proof.
    Hint Resolve nnrs_imp_expr_type_rename_in_f.

    revert l Γ τ
    ; nnrs_imp_stmt_cases (induction s) Case
    ; simpl; intros l Γ τ ninl ninl' nine ninb typ
    ; repeat rewrite in_app_iff in nine
    ; repeat rewrite in_app_iff in ninb
    ; invcs typ.
    - Case "NNRSimpSkip"%string.
      eauto.
    - Case "NNRSimpSeq"%string.
      intuition eauto.
    - Case "NNRSimpAssign"%string.
      match_destr; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        repeat rewrite lookup_app in *.
        repeat rewrite lookup_nin_none in * by trivial.
        simpl in *.
        match_destr_in H3; try contradiction.
        match_destr; try contradiction.
      + econstructor; eauto.
        repeat rewrite lookup_app in *.
        simpl in *.
        match_destr_in H3; try contradiction.
        match_destr_in H3; try contradiction.
        match_destr; try tauto.
    - Case "NNRSimpLet"%string.
      match_destr; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        apply (nnrs_imp_stmt_type_unused_remove Γc ((v,τ0)::l)) in H4
        ; simpl; try tauto.
        apply (nnrs_imp_stmt_type_unused_add Γc ((v, τ0)::l))
        ; simpl; trivial.
        intuition.
        destruct (remove_nin_inv H3); eauto.
      + econstructor; eauto.
        specialize (IHs ((v0, τ0) :: l)); simpl in IHs.
        eapply IHs; eauto
        ; intuition.
        destruct (remove_nin_inv H1); eauto.
    - Case "NNRSimpLet"%string.
      match_destr; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        apply (nnrs_imp_stmt_type_unused_remove Γc ((v,τ0)::l)) in H4
        ; simpl; try tauto.
        apply (nnrs_imp_stmt_type_unused_add Γc ((v, τ0)::l))
        ; simpl; trivial.
        intuition.
        destruct (remove_nin_inv H3); eauto.
      + econstructor; eauto.
        * rewrite nnrs_imp_stmt_rename_var_usage_neq; tauto.
        * specialize (IHs ((v0, τ0) :: l)); simpl in IHs.
          eapply IHs; eauto
          ; intuition.
          destruct (remove_nin_inv H1); eauto.
    - Case "NNRSimpFor"%string.
      match_destr; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        apply (nnrs_imp_stmt_type_unused_remove Γc ((v,τ0)::l)) in H4
        ; simpl; try tauto.
        apply (nnrs_imp_stmt_type_unused_add Γc ((v, τ0)::l))
        ; simpl; trivial.
        intuition.
        destruct (remove_nin_inv H3); eauto.
      + econstructor; eauto.
        specialize (IHs ((v0, τ0) :: l)); simpl in IHs.
        eapply IHs; eauto
        ; intuition.
        destruct (remove_nin_inv H1); eauto.
    - Case "NNRSimpIf"%string.
      econstructor; intuition eauto.
    - Case "NNRSimpEither"%string.
      econstructor; eauto.
      + match_destr; unfold equiv, complement in *.
        * subst.
          apply (nnrs_imp_stmt_type_unused_remove Γc ((v,τl)::l)) in H6
          ; simpl; try tauto.
          apply (nnrs_imp_stmt_type_unused_add Γc ((v,τl)::l))
          ; simpl; trivial.
          intuition.
          destruct (remove_nin_inv H0); eauto.
        * specialize (IHs1 ((v0, τl) :: l)); simpl in IHs1.
          eapply IHs1; eauto
          ; intuition.
          destruct (remove_nin_inv H5); eauto.
      + match_destr; unfold equiv, complement in *.
        * subst.
          apply (nnrs_imp_stmt_type_unused_remove Γc ((v,τr)::l)) in H7
          ; simpl; try tauto.
          apply (nnrs_imp_stmt_type_unused_add Γc ((v,τr)::l))
          ; simpl; trivial.
          intuition.
          destruct (remove_nin_inv H8); eauto.
        * specialize (IHs2 ((v1, τr) :: l)); simpl in IHs2.
          eapply IHs2; simpl in *; eauto
          ; intuition.
          destruct (remove_nin_inv H8); eauto.
  Qed.

  Lemma nnrs_imp_stmt_type_rename_f Γc Γ s (v v':var) τ :
    ~ In v' (nnrs_imp_stmt_free_vars s) ->
    ~ In v' (nnrs_imp_stmt_bound_vars s) ->
    [ Γc ; ((v,τ)::Γ)   ⊢ s ] ->
    [ Γc ; ((v',τ)::Γ) ⊢ nnrs_imp_stmt_rename s v v' ].
  Proof.
    intros.
    apply (nnrs_imp_stmt_type_rename_in_f Γc nil); tauto.
  Qed.
  
  Lemma nnrs_imp_expr_type_rename_in_b Γc l Γ e (v v':var) τ (τo:rtype) :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_imp_expr_free_vars e) ->
    [ Γc ; (l++(v',τ)::Γ)  ⊢ nnrs_imp_expr_rename e v v' ▷ τo ]%nnrs_imp_scope ->
    [ Γc ; (l++(v,τ)::Γ)  ⊢ e ▷ τo ].
  Proof.
    revert τo.
    nnrs_imp_expr_cases (induction e) Case; simpl; trivial
    ; intros τo ??? typ
    ; invcs typ
    ; repeat rewrite in_app_iff in *
    ; eauto 3.
    - Case "NNRSimpVar"%string.
      econstructor.
      repeat rewrite lookup_app in *.
      destruct (equiv_dec v0 v); unfold equiv, complement in *
      ; subst; simpl in *.
      + repeat match_option
        ; try solve [(try apply lookup_in_domain in eqq
                      ; try apply lookup_in_domain in eqq0; try contradiction)].
        repeat match_option_in H4
        ; try solve [(try apply lookup_in_domain in eqq
                      ; try apply lookup_in_domain in eqq0; try contradiction)].
        simpl in *.
        match_destr_in H4; try congruence.
        match_destr; try congruence.
      + match_option; simpl.
        * rewrite eqq in H4; trivial.
        * rewrite eqq in H4; simpl in *.
          match_destr; try congruence.
          match_destr_in H4; try congruence.
          intuition.
    - Case "NNRSimpBinop"%string.
      econstructor; eauto.
  Qed.

  Lemma nnrs_imp_expr_type_rename_b Γc Γ e (v v':var) τ (τo:rtype) :
    ~ In v' (nnrs_imp_expr_free_vars e) ->
    [ Γc ; ((v',τ)::Γ)  ⊢ nnrs_imp_expr_rename e v v' ▷ τo ]%nnrs_imp_scope ->
    [ Γc ; ((v,τ)::Γ)  ⊢ e ▷ τo ].
  Proof.
    intros.
    eapply (nnrs_imp_expr_type_rename_in_b Γc nil Γ); eauto; tauto.
  Qed.

  Lemma nnrs_imp_stmt_type_rename_in_b Γc l Γ s (v v':var) τ :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_imp_stmt_free_vars s) ->
    ~ In v' (nnrs_imp_stmt_bound_vars s) ->
    [ Γc ; (l++(v',τ)::Γ) ⊢ nnrs_imp_stmt_rename s v v' ] ->
    [ Γc ; (l++(v,τ)::Γ)   ⊢ s ].
  Proof.
    Hint Resolve nnrs_imp_expr_type_rename_in_b.

    revert l Γ τ
    ; nnrs_imp_stmt_cases (induction s) Case
    ; simpl; intros l Γ τ ninl ninl' nine ninb typ
    ; repeat rewrite in_app_iff in nine
    ; repeat rewrite in_app_iff in ninb
    ; invcs typ.
    - Case "NNRSimpSkip"%string.
      eauto.
    - Case "NNRSimpSeq"%string.
      intuition eauto.
    - Case "NNRSimpAssign"%string.
      match_destr_in H3; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        repeat rewrite lookup_app in *.
        repeat rewrite lookup_nin_none in * by trivial.
        simpl in *.
        match_destr_in H3; try contradiction.
        invcs H3.
        match_destr; try contradiction.
      + econstructor; eauto.
        repeat rewrite lookup_app in *.
        simpl in *.
        match_destr_in H3; try contradiction.
        match_destr; try tauto.
        match_destr_in H3; try contradiction.
        tauto.
    - Case "NNRSimpLet"%string.
      destruct o; try discriminate.
      invcs H0.
      econstructor; eauto.
      match_destr_in H4; unfold equiv, complement in *.
      + subst.
        apply (nnrs_imp_stmt_type_unused_add Γc ((v, τ0)::l))
        ; simpl; try tauto.
        apply (nnrs_imp_stmt_type_unused_remove Γc ((v,τ0)::l)) in H4
        ; simpl; try tauto.
        intuition.
        destruct (remove_nin_inv H3); eauto.
      + specialize (IHs ((v0, τ0) :: l)); simpl in IHs.
        eapply IHs; eauto
        ; intuition.
        destruct (remove_nin_inv H1); eauto.
    - Case "NNRSimpLet"%string.
      destruct o; try discriminate.
      match_destr_in H4; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        apply (nnrs_imp_stmt_type_unused_add Γc ((v, τ0)::l))
        ; simpl; try tauto.
        apply (nnrs_imp_stmt_type_unused_remove Γc ((v,τ0)::l)) in H4
        ; simpl; try tauto.
        intuition.
        destruct (remove_nin_inv H5); eauto.
      + econstructor; eauto.
        * rewrite nnrs_imp_stmt_rename_var_usage_neq in H2; tauto.
        * specialize (IHs ((v0, τ0) :: l)); simpl in IHs.
          eapply IHs; eauto
          ; intuition.
          destruct (remove_nin_inv H3); eauto.
    - Case "NNRSimpFor"%string.
      match_destr_in H4; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        apply (nnrs_imp_stmt_type_unused_add Γc ((v, τ0)::l))
        ; simpl; try tauto.
        apply (nnrs_imp_stmt_type_unused_remove Γc ((v,τ0)::l)) in H4
        ; simpl; try tauto.
        intuition.
        destruct (remove_nin_inv H3); eauto.
      + econstructor; eauto.
        specialize (IHs ((v0, τ0) :: l)); simpl in IHs.
        eapply IHs; eauto
        ; intuition.
        destruct (remove_nin_inv H1); eauto.
    - Case "NNRSimpIf"%string.
      econstructor; intuition eauto.
    - Case "NNRSimpEither"%string.
      econstructor; eauto.
      + match_destr_in H6; unfold equiv, complement in *.
        * subst.
          apply (nnrs_imp_stmt_type_unused_add Γc ((v,τl)::l))
          ; simpl; try tauto.
          apply (nnrs_imp_stmt_type_unused_remove Γc ((v,τl)::l)) in H6
          ; simpl; try tauto.
          intuition.
          destruct (remove_nin_inv H0); eauto.
        * specialize (IHs1 ((v0, τl) :: l)); simpl in IHs1.
          eapply IHs1; eauto
          ; intuition.
          destruct (remove_nin_inv H5); eauto.
      + match_destr_in H7; unfold equiv, complement in *.
        * subst.
          apply (nnrs_imp_stmt_type_unused_add Γc ((v,τr)::l))
          ; simpl; try tauto.
          apply (nnrs_imp_stmt_type_unused_remove Γc ((v,τr)::l)) in H7
          ; simpl; try tauto.
          intuition.
          destruct (remove_nin_inv H8); eauto.
        * specialize (IHs2 ((v1, τr) :: l)); simpl in IHs2.
          eapply IHs2; simpl in *; eauto
          ; intuition.
          destruct (remove_nin_inv H8); eauto.
  Qed.

  Lemma nnrs_imp_stmt_type_rename_b Γc Γ s (v v':var) τ :
    ~ In v' (nnrs_imp_stmt_free_vars s) ->
    ~ In v' (nnrs_imp_stmt_bound_vars s) ->
    [ Γc ; ((v',τ)::Γ) ⊢ nnrs_imp_stmt_rename s v v' ] ->
    [ Γc ; ((v,τ)::Γ)   ⊢ s ].
  Proof.
    intros.
    eapply (nnrs_imp_stmt_type_rename_in_b Γc nil); eauto.
  Qed.

  Theorem nnrs_imp_expr_type_rename_in Γc l Γ e (v v':var) τ (τo:rtype) :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_imp_expr_free_vars e) ->
    [ Γc ; (l++(v',τ)::Γ)  ⊢ nnrs_imp_expr_rename e v v' ▷ τo ]%nnrs_imp_scope <->
    [ Γc ; (l++(v,τ)::Γ)  ⊢ e ▷ τo ].
  Proof.
    intros; split; intros.
    - eapply nnrs_imp_expr_type_rename_in_b; eauto.
    - eapply nnrs_imp_expr_type_rename_in_f; eauto.
  Qed.

  Corollary nnrs_imp_expr_type_rename Γc Γ e (v v':var) τ (τo:rtype) :
    ~ In v' (nnrs_imp_expr_free_vars e) ->
    [ Γc ; ((v',τ)::Γ)  ⊢ nnrs_imp_expr_rename e v v' ▷ τo ]%nnrs_imp_scope <->
    [ Γc ; ((v,τ)::Γ)  ⊢ e ▷ τo ].
  Proof.
    intros; split; intros.
    - eapply nnrs_imp_expr_type_rename_b; eauto.
    - eapply nnrs_imp_expr_type_rename_f; eauto.
  Qed.

  Theorem nnrs_imp_stmt_type_rename_in Γc l Γ s (v v':var) τ :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_imp_stmt_free_vars s) ->
    ~ In v' (nnrs_imp_stmt_bound_vars s) ->
    [ Γc ; (l++(v',τ)::Γ) ⊢ nnrs_imp_stmt_rename s v v' ] <->
    [ Γc ; (l++(v,τ)::Γ)   ⊢ s ].
  Proof.
    intros; split; intros.
    - eapply nnrs_imp_stmt_type_rename_in_b; eauto.
    - eapply nnrs_imp_stmt_type_rename_in_f; eauto.
  Qed.

  Corollary nnrs_imp_stmt_type_rename Γc Γ s (v v':var) τ :
    ~ In v' (nnrs_imp_stmt_free_vars s) ->
    ~ In v' (nnrs_imp_stmt_bound_vars s) ->
    [ Γc ; ((v',τ)::Γ) ⊢ nnrs_imp_stmt_rename s v v' ] <->
    [ Γc ; ((v,τ)::Γ)   ⊢ s ].
  Proof.
    intros; split; intros.
    - eapply nnrs_imp_stmt_type_rename_b; eauto.
    - eapply nnrs_imp_stmt_type_rename_f; eauto.
  Qed.
  
End TNNRSimpRename.
