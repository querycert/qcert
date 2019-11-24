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
Require Import NNRS.
Require Import NNRSVars.
Require Import NNRSRename.

Require Import TNNRS.

Section TNNRSRename.
  Context {m:basic_model}.
  Local Open Scope nnrs.

  Hint Constructors nnrs_expr_type.
  Hint Constructors nnrs_stmt_type.


  Lemma nnrs_stmt_must_assign_rename_env s v v1 v2 :
    nnrs_stmt_must_assign s v
    <->
    nnrs_stmt_must_assign (nnrs_stmt_rename_env s v1 v2) v.
  Proof.
    induction s; simpl; repeat match_destr; intuition.
  Qed.

  Lemma nnrs_stmt_must_assign_rename_mc s v v1 v2 :
    nnrs_stmt_must_assign s v
    <->
    nnrs_stmt_must_assign (nnrs_stmt_rename_mc s v1 v2) v.
  Proof.
    induction s; simpl; repeat match_destr; intuition.
  Qed.

  Lemma nnrs_stmt_must_assign_rename_md_neq s v v1 v2 :
    v <> v1 ->
    v <> v2 ->
    nnrs_stmt_must_assign s v
    <->
    nnrs_stmt_must_assign (nnrs_stmt_rename_md s v1 v2) v.
  Proof.
    induction s; simpl; repeat match_destr; intuition.
    congruence.
  Qed.

    Lemma nnrs_stmt_must_assign_rename_md_eq_f s v1 v2 :
    ~ In v2 (nnrs_stmt_bound_mdenv_vars s) ->
    nnrs_stmt_must_assign s v1 ->
    nnrs_stmt_must_assign (nnrs_stmt_rename_md s v1 v2) v2.
  Proof.
    nnrs_stmt_cases (induction s) Case
    ; simpl; intros; repeat match_destr; unfold equiv, complement in *; subst; intuition.
  Qed.

    Lemma nnrs_stmt_must_assign_rename_md_eq_b s v1 v2 :
    ~ In v2 (nnrs_stmt_free_mdenv_vars s) ->
    nnrs_stmt_must_assign (nnrs_stmt_rename_md s v1 v2) v2 ->
    nnrs_stmt_must_assign s v1.
  Proof.
    nnrs_stmt_cases (induction s) Case
    ; simpl; try solve [repeat match_destr; unfold equiv, complement in *; subst
    ; repeat rewrite in_app_iff; intuition].
    - Case "NNRSLetMut"%string.
      repeat rewrite in_app_iff.
      intros nin ma.
      apply not_or in nin.
      destruct nin as [nin1 nin2].
      intuition.
      rewrite <- remove_in_neq in nin1 by congruence.
      match_destr_in H1; intuition; unfold equiv, complement in *; subst.
      apply nnrs_stmt_must_assign_is_free in H1; tauto.
  Qed.

  Lemma nnrs_expr_type_rename_env_in Γc l Γ e (v v':var) τ (τo:rtype) :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_expr_free_vars e) ->
    [ Γc ; (l++(v,τ)::Γ)   ⊢ e ▷ τo ] ->
    [ Γc ; (l++(v',τ)::Γ)   ⊢ nnrs_expr_rename_env e v v' ▷ τo ].
  Proof.
    revert τo.
    nnrs_expr_cases (induction e) Case; simpl; trivial
    ; intros τo ??? typ
    ; invcs typ
    ; repeat rewrite in_app_iff in *
    ; eauto 3.
    - econstructor.
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
    - econstructor; eauto.
  Qed.

  Ltac rename_inv_tac1 stac
    := unfold var in *
       ; repeat rewrite or_assoc
       ; try match goal with
             | [ H: domain (_ ++ _) = domain _ |- _ ] =>
               rewrite domain_app in H
               ; unfold domain in H
               ; symmetry in H; apply map_app_break in H
               ; destruct H as [? [?[?[??]]]]; subst; simpl in *
             | [ H: map (_ ++ _) = map _ |- _ ] =>
               rewrite map_app in H
               ; symmetry in H; apply map_app_break in H
               ; destruct H as [? [?[?[??]]]]; subst; simpl in *
             | [ H: _ :: _ = map _ ?x |- _ ] =>
               destruct x; try discriminate; simpl in H; invcs H
             | [ H: _ :: _ = domain ?x |- _ ] =>
               destruct x; try discriminate; simpl in H; invcs H
             | [H: _ * _ * _ |- _ ] => destruct H as [[??]?]; simpl in *
             | [H: _ * _ |- _ ] => destruct H as [??]; simpl in *
             | [H: ~ (_ \/ _) |- _] => apply not_or in H
             | [H: _ /\ _ |- _ ] => destruct H
             | [H: ?x = ?x |- _] => clear H
             end.

  Lemma nnrs_stmt_type_rename_env_in Γc l Γ Δc Δd s (v v':var) τ :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_stmt_free_env_vars s) ->
    ~ In v' (nnrs_stmt_bound_env_vars s) ->
    [ Γc ; (l++(v,τ)::Γ) , Δc , Δd  ⊢ s ] ->
    [ Γc ; (l++(v',τ)::Γ) , Δc , Δd  ⊢ nnrs_stmt_rename_env s v v' ].
  Proof.
    Hint Resolve nnrs_expr_type_rename_env_in.

    revert l Γ Δc Δd τ
    ; nnrs_stmt_cases (induction s) Case
    ; simpl; intros l Γ Δc Δd τ ninl ninl' nine ninb typ
    ; repeat rewrite in_app_iff in nine
    ; repeat rewrite in_app_iff in ninb
    ; invcs typ.
    - Case "NNRSSeq"%string.
      intuition eauto.
    - Case "NNRSLet"%string.
      match_destr; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        apply (nnrs_stmt_type_unused_remove_env Γc ((v,Some τ0)::l)) in H6
        ; simpl; try tauto.
        apply (nnrs_stmt_type_unused_add_env Γc ((v,Some τ0)::l))
        ; simpl; trivial.
        intuition.
        destruct (remove_nin_inv H2); eauto.
      + econstructor; eauto.
        specialize (IHs ((v0, Some τ0) :: l)); simpl in IHs.
        eapply IHs; eauto
        ; intuition.
        destruct (remove_nin_inv H1); eauto.
    - Case "NNRSLetMut"%string.
      match_destr; unfold equiv, complement in *.
      + subst.
        econstructor.
        * apply nnrs_stmt_must_assign_rename_env; trivial.
        * eapply IHs1; eauto.
        * apply (nnrs_stmt_type_unused_remove_env Γc ((v, Some τ0) :: l)) in H7
          ; simpl; [| tauto].
          apply (nnrs_stmt_type_unused_add_env Γc ((v, Some τ0) :: l)); trivial; simpl.
          intuition.
          destruct (remove_nin_inv H2); eauto.
      + econstructor.
        * apply nnrs_stmt_must_assign_rename_env; trivial.
        * eapply IHs1; eauto.
        * specialize (IHs2 ((v0, Some τ0) :: l)); simpl in IHs2.
          eapply IHs2; intuition.
          destruct (remove_nin_inv H1); eauto.
    - Case "NNRSLetMut"%string.
      match_destr; unfold equiv, complement in *.
      + subst.
        eapply type_NNRSLetMutNotUsed.
        * eapply IHs1; eauto.
        * apply (nnrs_stmt_type_unused_remove_env Γc ((v, None) :: l)) in H6
          ; simpl; [| tauto].
          apply (nnrs_stmt_type_unused_add_env Γc ((v, None) :: l)); trivial; simpl.
          intuition.
          destruct (remove_nin_inv H2); eauto.
      + eapply type_NNRSLetMutNotUsed.
        * eapply IHs1; eauto.
        * specialize (IHs2 ((v0, None) :: l)); simpl in IHs2.
          eapply IHs2; intuition.
          destruct (remove_nin_inv H1); eauto.
    - Case "NNRSLetMutColl"%string.
      econstructor; [intuition eauto | ].
      match_destr; unfold equiv, complement in *.
      + subst.
        apply (nnrs_stmt_type_unused_remove_env Γc ((v, Some (Coll τ0)) :: l)) in H6
        ; simpl; [| tauto].
        apply (nnrs_stmt_type_unused_add_env Γc ((v,  Some (Coll τ0)) :: l)); trivial; simpl.
        intuition.
        destruct (remove_nin_inv H2); eauto.
      + specialize (IHs2 ((v0, Some (Coll τ0)) :: l)); simpl in IHs2.
        eapply IHs2; intuition.
        destruct (remove_nin_inv H1); eauto.
    - Case "NNRSAssign"%string.
      eauto.
    - Case "NNRSPush"%string.
      eauto.
    - econstructor; eauto.
      match_destr; unfold equiv, complement in *.
      + subst.
        apply (nnrs_stmt_type_unused_remove_env Γc ((v, Some τ0) :: l)) in H6
        ; simpl; [| tauto].
        apply (nnrs_stmt_type_unused_add_env Γc ((v,  Some τ0) :: l)); trivial; simpl.
        intuition.
        destruct (remove_nin_inv H2); eauto.
      + specialize (IHs ((v0, Some τ0) :: l)); simpl in IHs.
        eapply IHs; intuition.
        destruct (remove_nin_inv H1); eauto.
    - Case "NNRSIf"%string.
      econstructor; intuition eauto.
    - Case "NNRSEither"%string.
      econstructor; eauto.
      + match_destr; unfold equiv, complement in *.
        * subst.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v,Some τl)::l)) in H8
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_add_env Γc ((v,Some τl)::l))
          ; simpl; trivial.
          intuition.
          destruct (remove_nin_inv H0); eauto.
        * specialize (IHs1 ((v0, Some τl) :: l)); simpl in IHs1.
          eapply IHs1; eauto
          ; intuition.
          destruct (remove_nin_inv H4); eauto.
      + match_destr; unfold equiv, complement in *.
        * subst.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v,Some τr)::l)) in H9
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_add_env Γc ((v,Some τr)::l))
          ; simpl; trivial.
          intuition.
          destruct (remove_nin_inv H6); eauto.
        * specialize (IHs2 ((v1, Some τr) :: l)); simpl in IHs2.
          eapply IHs2; eauto
          ; intuition.
          destruct (remove_nin_inv H6); eauto.
  Qed.

  Lemma nnrs_stmt_type_rename_mdenv_in Γc l Γ Δc Δd s (v v':var) τ :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_stmt_free_mdenv_vars s) ->
    ~ In v' (nnrs_stmt_bound_mdenv_vars s) ->
    [ Γc ; Γ , Δc , (l++(v,τ)::Δd)  ⊢ s ] ->
    [ Γc ; Γ , Δc , (l++(v',τ)::Δd)  ⊢ nnrs_stmt_rename_md s v v' ].
  Proof.

    revert l Γ Δc Δd τ
    ; nnrs_stmt_cases (induction s) Case
    ; simpl; intros l Γ Δc Δd τ ninl ninl' nine ninb typ
    ; repeat rewrite in_app_iff in nine
    ; repeat rewrite in_app_iff in ninb
    ; invcs typ
    ; intuition eauto.
    - Case "NNRSLetMut"%string.
      match_destr; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        apply (nnrs_stmt_type_unused_remove_mdenv Γc ((v, τ0) :: l)) in H6
        ; simpl; [| tauto].
        apply (nnrs_stmt_type_unused_add_mdenv Γc ((v, τ0) :: l)); trivial; simpl.
        intuition.
        destruct (remove_nin_inv H); eauto.
      + econstructor; eauto.
        * apply nnrs_stmt_must_assign_rename_md_neq; trivial.
        * specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
          eapply IHs1; intuition.
          destruct (remove_nin_inv H); eauto.
    - Case "NNRSLetMut"%string.
      match_destr; unfold equiv, complement in *.
      + subst.
        eapply type_NNRSLetMutNotUsed; eauto.
        * apply (nnrs_stmt_type_unused_remove_mdenv Γc ((v, τ0) :: l)) in H4
          ; simpl; [| tauto].
          apply (nnrs_stmt_type_unused_add_mdenv Γc ((v, τ0) :: l)); trivial; simpl.
          intuition.
          destruct (remove_nin_inv H); eauto.
      + eapply type_NNRSLetMutNotUsed; eauto.
        * specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
          eapply IHs1; intuition.
          destruct (remove_nin_inv H); eauto.
    - Case "NNRSAssign"%string.
      econstructor; eauto.
      repeat rewrite lookup_app in *.
      destruct (equiv_dec v0 v); unfold equiv, complement in *
      ; subst.
      + repeat match_option
        ; try solve [(try apply lookup_in_domain in eqq
                      ; try apply lookup_in_domain in eqq0; try contradiction)].
        repeat match_option_in H5
        ; try solve [(try apply lookup_in_domain in eqq
                      ; try apply lookup_in_domain in eqq0; try contradiction)].
        simpl in *.
        match_destr_in H5; try congruence.
        match_destr; try congruence.
      + match_option; simpl.
        * rewrite eqq in H5; trivial.
        * rewrite eqq in H5; simpl in *.
          match_destr_in H5; try congruence.
          match_destr; try congruence.
  Qed.

  Lemma nnrs_stmt_type_rename_mcenv_in Γc l Γ Δc Δd s (v v':var) τ :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_stmt_free_mcenv_vars s) ->
    ~ In v' (nnrs_stmt_bound_mcenv_vars s) ->
    [ Γc ; Γ ,  (l++(v,τ)::Δc), Δd  ⊢ s ] ->
    [ Γc ; Γ , (l++(v',τ)::Δc), Δd  ⊢ nnrs_stmt_rename_mc s v v' ].
  Proof.
    revert l Γ Δc Δd τ
    ; nnrs_stmt_cases (induction s) Case
    ; simpl; intros l Γ Δc Δd τ ninl ninl' nine ninb typ
    ; repeat rewrite in_app_iff in nine
    ; repeat rewrite in_app_iff in ninb
    ; invcs typ
    ; intuition eauto.
    - Case "NNRSLetMut"%string.
      econstructor; intuition eauto.
      apply nnrs_stmt_must_assign_rename_mc; trivial.
    - Case "NNRSLetMutColl"%string.
      match_destr; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        * apply (nnrs_stmt_type_unused_remove_mcenv Γc ((v, τ0) :: l)) in H4
          ; simpl; [| tauto].
          apply (nnrs_stmt_type_unused_add_mcenv Γc ((v, τ0) :: l)); trivial; simpl.
          intuition.
          destruct (remove_nin_inv H); eauto.
      + econstructor; eauto.
        * specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
          eapply IHs1; intuition.
          destruct (remove_nin_inv H); eauto.
    - Case "NNRSPush"%string.
      econstructor; eauto.
      repeat rewrite lookup_app in *.
      destruct (equiv_dec v0 v); unfold equiv, complement in *
      ; subst.
      + repeat match_option
        ; try solve [(try apply lookup_in_domain in eqq
                      ; try apply lookup_in_domain in eqq0; try contradiction)].
        repeat match_option_in H5
        ; try solve [(try apply lookup_in_domain in eqq
                      ; try apply lookup_in_domain in eqq0; try contradiction)].
        simpl in *.
        match_destr_in H5; try congruence.
        match_destr; try congruence.
      + match_option; simpl.
        * rewrite eqq in H5; trivial.
        * rewrite eqq in H5; simpl in *.
          match_destr_in H5; try congruence.
          match_destr; try congruence.
  Qed.

  (* These lemmas almost follows from *_involutive and the forward direction,
      but doing it that way requires the extra assumption
      (~ In v (nnrs_stmt_bound_*_vars s)).
      Instead, we prove them directly, eliminating this unneeded hypothesis.
   *)
    Lemma nnrs_expr_type_rename_env_in_inv Γc l Γ e (v v':var) τ (τo:rtype) :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_expr_free_vars e) ->
    [ Γc ; (l++(v',τ)::Γ)   ⊢ nnrs_expr_rename_env e v v' ▷ τo ] ->
    [ Γc ; (l++(v,τ)::Γ)   ⊢ e ▷ τo ].
  Proof.
    revert τo.
    nnrs_expr_cases (induction e) Case; simpl; trivial
    ; intros τo ??? typ
    ; invcs typ
    ; repeat rewrite in_app_iff in *
    ; eauto 3.
    - econstructor.
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
          match_destr; congruence.
    - econstructor; eauto.
  Qed.

    Lemma nnrs_stmt_type_rename_env_in_inv Γc l Γ Δc Δd s (v v':var) τ :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_stmt_free_env_vars s) ->
    ~ In v' (nnrs_stmt_bound_env_vars s) ->
    [ Γc ; (l++(v',τ)::Γ) , Δc , Δd  ⊢ nnrs_stmt_rename_env s v v' ] ->
    [ Γc ; (l++(v,τ)::Γ) , Δc , Δd  ⊢ s ].
  Proof.
    Hint Resolve nnrs_expr_type_rename_env_in_inv.

    revert l Γ Δc Δd τ
    ; nnrs_stmt_cases (induction s) Case
    ; simpl; intros l Γ Δc Δd τ ninl ninl' nine ninb typ
    ; repeat rewrite in_app_iff in nine
    ; repeat rewrite in_app_iff in ninb
    ; invcs typ.
    - Case "NNRSSeq"%string.
      intuition eauto.
    - Case "NNRSLet"%string.
      match_destr_in H6; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        apply (nnrs_stmt_type_unused_add_env Γc ((v,Some τ0)::l))
        ; simpl; try tauto.
        apply (nnrs_stmt_type_unused_remove_env Γc ((v,Some τ0)::l)) in H6
        ; simpl; try tauto.
        intuition.
        destruct (remove_nin_inv H2); eauto.
      + econstructor; eauto.
        specialize (IHs ((v0, Some τ0) :: l)); simpl in IHs.
        eapply IHs; eauto
        ; intuition.
        destruct (remove_nin_inv H1); eauto.
    - Case "NNRSLetMut"%string.
      match_destr_in H7; unfold equiv, complement in *.
      + subst.
        econstructor.
        * eapply nnrs_stmt_must_assign_rename_env; eauto.
        * eapply IHs1; eauto.
        * apply (nnrs_stmt_type_unused_add_env Γc ((v, Some τ0) :: l))
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v, Some τ0) :: l)) in H7
          ; simpl; try tauto.
          intuition.
          destruct (remove_nin_inv H2); eauto.
      + econstructor.
        * eapply nnrs_stmt_must_assign_rename_env; eauto.
        * eapply IHs1; eauto.
        * specialize (IHs2 ((v0, Some τ0) :: l)); simpl in IHs2.
          eapply IHs2; intuition.
          destruct (remove_nin_inv H1); eauto.
    - Case "NNRSLetMut"%string.
      match_destr_in H6; unfold equiv, complement in *.
      + subst.
        eapply type_NNRSLetMutNotUsed.
        * eapply IHs1; eauto.
        *  apply (nnrs_stmt_type_unused_add_env Γc ((v, None) :: l))
           ; simpl; try tauto.
           apply (nnrs_stmt_type_unused_remove_env Γc ((v, None) :: l)) in H6
          ; simpl; try tauto.
          intuition.
          destruct (remove_nin_inv H2); eauto.
      + eapply type_NNRSLetMutNotUsed.
        * eapply IHs1; eauto.
        * specialize (IHs2 ((v0, None) :: l)); simpl in IHs2.
          eapply IHs2; intuition.
          destruct (remove_nin_inv H1); eauto.
    - Case "NNRSLetMutColl"%string.
      econstructor; [intuition eauto | ].
      match_destr_in H6; unfold equiv, complement in *.
      + subst.
        apply (nnrs_stmt_type_unused_add_env Γc ((v,  Some (Coll τ0)) :: l))
        ; simpl; try tauto.
        apply (nnrs_stmt_type_unused_remove_env Γc ((v, Some (Coll τ0)) :: l)) in H6
        ; simpl; try tauto.
        intuition.
        destruct (remove_nin_inv H2); eauto.
      + specialize (IHs2 ((v0, Some (Coll τ0)) :: l)); simpl in IHs2.
        eapply IHs2; intuition.
        destruct (remove_nin_inv H1); eauto.
    - Case "NNRSAssign"%string.
      eauto.
    - Case "NNRSPush"%string.
      eauto.
    - econstructor; eauto.
      match_destr_in H6; unfold equiv, complement in *.
      + subst.
        apply (nnrs_stmt_type_unused_add_env Γc ((v,  Some τ0) :: l));
          simpl; try tauto.
        apply (nnrs_stmt_type_unused_remove_env Γc ((v, Some τ0) :: l)) in H6
        ; simpl; try tauto.
        intuition.
        destruct (remove_nin_inv H2); eauto.
      + specialize (IHs ((v0, Some τ0) :: l)); simpl in IHs.
        eapply IHs; intuition.
        destruct (remove_nin_inv H1); eauto.
    - Case "NNRSIf"%string.
      econstructor; intuition eauto.
    - Case "NNRSEither"%string.
      econstructor; eauto.
      + match_destr_in H8; unfold equiv, complement in *.
        * subst.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v,Some τl)::l)) in H8
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_add_env Γc ((v,Some τl)::l))
          ; simpl; try tauto.
          intuition.
          destruct (remove_nin_inv H0); eauto.
        * specialize (IHs1 ((v0, Some τl) :: l)); simpl in IHs1.
          eapply IHs1; eauto
          ; intuition.
          destruct (remove_nin_inv H4); eauto.
      + match_destr_in H9; unfold equiv, complement in *.
        * subst.
          apply (nnrs_stmt_type_unused_add_env Γc ((v,Some τr)::l))
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_remove_env Γc ((v,Some τr)::l)) in H9
          ; simpl; try tauto.
          intuition.
          destruct (remove_nin_inv H6); eauto.
        * specialize (IHs2 ((v1, Some τr) :: l)); simpl in IHs2.
          eapply IHs2; eauto
          ; intuition.
          destruct (remove_nin_inv H6); eauto.
  Qed.

  Lemma nnrs_stmt_type_rename_mdenv_in_inv Γc l Γ Δc Δd s (v v':var) τ :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_stmt_free_mdenv_vars s) ->
    ~ In v' (nnrs_stmt_bound_mdenv_vars s) ->
    [ Γc ; Γ , Δc , (l++(v',τ)::Δd)  ⊢ nnrs_stmt_rename_md s v v' ] ->
    [ Γc ; Γ , Δc , (l++(v,τ)::Δd)  ⊢ s ].
  Proof.
    revert l Γ Δc Δd τ
    ; nnrs_stmt_cases (induction s) Case
    ; simpl; intros l Γ Δc Δd τ ninl ninl' nine ninb typ
    ; repeat rewrite in_app_iff in nine
    ; repeat rewrite in_app_iff in ninb
    ; invcs typ
    ; intuition eauto.
    - Case "NNRSLetMut"%string.
      match_destr_in H6; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        apply (nnrs_stmt_type_unused_add_mdenv Γc ((v, τ0) :: l))
        ; simpl; try tauto.
        apply (nnrs_stmt_type_unused_remove_mdenv Γc ((v, τ0) :: l)) in H6
        ; simpl; try tauto.
        intuition.
        destruct (remove_nin_inv H); eauto.
      + econstructor; eauto.
        * eapply nnrs_stmt_must_assign_rename_md_neq; [| | eauto]; tauto.
        * specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
          eapply IHs1; intuition.
          destruct (remove_nin_inv H); eauto.
    - Case "NNRSLetMut"%string.
      match_destr_in H4; unfold equiv, complement in *.
      + subst.
        eapply type_NNRSLetMutNotUsed; eauto.
        * apply (nnrs_stmt_type_unused_add_mdenv Γc ((v, τ0) :: l))
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_remove_mdenv Γc ((v, τ0) :: l)) in H4
          ; simpl; try tauto.
          intuition.
          destruct (remove_nin_inv H); eauto.
      + eapply type_NNRSLetMutNotUsed; eauto.
        * specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
          eapply IHs1; intuition.
          destruct (remove_nin_inv H); eauto.
    - Case "NNRSAssign"%string.
      econstructor; eauto.
      repeat rewrite lookup_app in *.
      destruct (equiv_dec v0 v); unfold equiv, complement in *
      ; subst.
      + repeat match_option
        ; try solve [(try apply lookup_in_domain in eqq
                      ; try apply lookup_in_domain in eqq0; try contradiction)].
        repeat match_option_in H5
        ; try solve [(try apply lookup_in_domain in eqq
                      ; try apply lookup_in_domain in eqq0; try contradiction)].
        simpl in *.
        match_destr_in H5; try congruence.
        match_destr; try congruence.
      + match_option; simpl.
        * rewrite eqq in H5; trivial.
        * rewrite eqq in H5; simpl in *.
          match_destr_in H5; try congruence.
          match_destr; try congruence.
  Qed.

  Lemma nnrs_stmt_type_rename_mcenv_in_inv Γc l Γ Δc Δd s (v v':var) τ :
    ~ In v (domain l) ->
    ~ In v' (domain l) ->
    ~ In v' (nnrs_stmt_free_mcenv_vars s) ->
    ~ In v' (nnrs_stmt_bound_mcenv_vars s) ->
    [ Γc ; Γ , (l++(v',τ)::Δc), Δd  ⊢ nnrs_stmt_rename_mc s v v' ] ->
    [ Γc ; Γ ,  (l++(v,τ)::Δc), Δd  ⊢ s ].
  Proof.
    revert l Γ Δc Δd τ
    ; nnrs_stmt_cases (induction s) Case
    ; simpl; intros l Γ Δc Δd τ ninl ninl' nine ninb typ
    ; repeat rewrite in_app_iff in nine
    ; repeat rewrite in_app_iff in ninb
    ; invcs typ
    ; intuition eauto.
    - Case "NNRSLetMut"%string.
      econstructor; intuition eauto.
      eapply nnrs_stmt_must_assign_rename_mc; eauto.
    - Case "NNRSLetMutColl"%string.
      match_destr_in H4; unfold equiv, complement in *.
      + subst.
        econstructor; eauto.
        * apply (nnrs_stmt_type_unused_add_mcenv Γc ((v, τ0) :: l))
          ; simpl; try tauto.
          apply (nnrs_stmt_type_unused_remove_mcenv Γc ((v, τ0) :: l)) in H4
          ; simpl; try tauto.
          intuition.
          destruct (remove_nin_inv H); eauto.
      + econstructor; eauto.
        * specialize (IHs1 ((v0, τ0) :: l)); simpl in IHs1.
          eapply IHs1; intuition.
          destruct (remove_nin_inv H); eauto.
    - Case "NNRSPush"%string.
      econstructor; eauto.
      repeat rewrite lookup_app in *.
      destruct (equiv_dec v0 v); unfold equiv, complement in *
      ; subst.
      + repeat match_option
        ; try solve [(try apply lookup_in_domain in eqq
                      ; try apply lookup_in_domain in eqq0; try contradiction)].
        repeat match_option_in H5
        ; try solve [(try apply lookup_in_domain in eqq
                      ; try apply lookup_in_domain in eqq0; try contradiction)].
        simpl in *.
        match_destr_in H5; try congruence.
        match_destr; try congruence.
      + match_option; simpl.
        * rewrite eqq in H5; trivial.
        * rewrite eqq in H5; simpl in *.
          match_destr_in H5; try congruence.
          match_destr; try congruence.
  Qed.

    Lemma nnrs_expr_type_rename_env_cons Γc Γ e (v v':var) τ (τo:rtype) :
    ~ In v' (nnrs_expr_free_vars e) ->
    [ Γc ; (v',τ)::Γ   ⊢ nnrs_expr_rename_env e v v' ▷ τo ] <->
    [ Γc ; (v,τ)::Γ   ⊢ e ▷ τo ].
  Proof.
    intros; split; intros.
    - eapply (nnrs_expr_type_rename_env_in_inv Γc nil); eauto.
    - eapply (nnrs_expr_type_rename_env_in Γc nil); eauto.
  Qed.

    Lemma nnrs_stmt_type_rename_env_in_cons Γc Γ Δc Δd s (v v':var) τ :
    ~ In v' (nnrs_stmt_free_env_vars s) ->
    ~ In v' (nnrs_stmt_bound_env_vars s) ->
    [ Γc ; (v',τ)::Γ , Δc , Δd  ⊢ nnrs_stmt_rename_env s v v' ] <->
    [ Γc ; (v,τ)::Γ , Δc , Δd  ⊢ s ].
    Proof.
      intros; split; intros.
      - eapply (nnrs_stmt_type_rename_env_in_inv Γc nil); eauto.
      - eapply (nnrs_stmt_type_rename_env_in Γc nil); eauto.
    Qed.

  Lemma nnrs_stmt_type_rename_mdenv_in_cons Γc Γ Δc Δd s (v v':var) τ :
    ~ In v' (nnrs_stmt_free_mdenv_vars s) ->
    ~ In v' (nnrs_stmt_bound_mdenv_vars s) ->
    [ Γc ; Γ , Δc , (v',τ)::Δd  ⊢ nnrs_stmt_rename_md s v v' ] <->
    [ Γc ; Γ , Δc , (v,τ)::Δd  ⊢ s ].
  Proof.
      intros; split; intros.
      - eapply (nnrs_stmt_type_rename_mdenv_in_inv Γc nil); eauto.
      - eapply (nnrs_stmt_type_rename_mdenv_in Γc nil); eauto.
  Qed.

  Lemma nnrs_stmt_type_rename_mcenv_in_cons Γc Γ Δc Δd s (v v':var) τ :
    ~ In v' (nnrs_stmt_free_mcenv_vars s) ->
    ~ In v' (nnrs_stmt_bound_mcenv_vars s) ->
    [ Γc ; Γ , (v',τ)::Δc, Δd  ⊢ nnrs_stmt_rename_mc s v v' ] <->
    [ Γc ; Γ , (v,τ)::Δc, Δd  ⊢ s ].
  Proof.
      intros; split; intros.
      - eapply (nnrs_stmt_type_rename_mcenv_in_inv Γc nil); eauto.
      - eapply (nnrs_stmt_type_rename_mcenv_in Γc nil); eauto.
  Qed.
    
End TNNRSRename.
