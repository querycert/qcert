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
Require Import Peano_dec.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import CommonSystem.
Require Import cNNRC.
Require Import cNNRCShadow.
Require Import TcNNRC.
  
Section TcNNRCShadow.
  Hint Constructors nnrc_core_type.

  Context {m:basic_model}.

  Lemma nnrc_core_type_remove_duplicate_env {τcenv} l v x l' x' l'' e τ:
    nnrc_core_type τcenv (l ++ (v,x)::l' ++ (v,x')::l'') e τ <->
    nnrc_core_type τcenv (l ++ (v,x)::l' ++ l'') e τ.
  Proof.
    apply nnrc_core_type_lookup_equiv_prop; trivial.
    apply lookup_remove_duplicate.
  Qed.

  Lemma nnrc_core_type_remove_free_env {τcenv} l v x l' e τ :
    ~ In v (nnrc_free_vars e) ->
    (nnrc_core_type τcenv (l ++ (v,x)::l') e τ <-> nnrc_core_type τcenv (l ++ l') e τ).
  Proof.
    split; revert l v x l' τ H;
      induction e; simpl; inversion 2; subst; intuition; eauto 3.
    - constructor. erewrite <- lookup_remove_nin; eauto.
    - apply nin_app_or in H. intuition. eauto.
    - apply nin_app_or in H. intuition.
      econstructor; eauto.
      destruct (equiv_dec v v0); unfold Equivalence.equiv in *; subst.
      + apply (nnrc_core_type_remove_duplicate_env nil v0 τ₁ l) in H7; eauto.
      + eapply (IHe2 ((v, τ₁) :: l)); eauto. 
        intro; elim H2; apply remove_in_neq; eauto.
    - apply nin_app_or in H. intuition.
      econstructor; eauto.
      destruct (equiv_dec v v0); unfold Equivalence.equiv in *; subst.
      + apply (nnrc_core_type_remove_duplicate_env nil v0 τ₁ l) in H7; eauto.
      + eapply (IHe2 ((v, τ₁) :: l)); eauto. 
        intro; elim H2; apply remove_in_neq; eauto.
    - apply nin_app_or in H; destruct H as [? HH]; apply nin_app_or in HH.
      intuition. eauto.
    - apply nin_app_or in H. destruct H as [neq1 neq2].
      apply nin_app_or in neq2. destruct neq2 as [neq2 neq3].
      econstructor; eauto.
      + destruct (equiv_dec v v1); unfold Equivalence.equiv in *; subst.
        * apply (nnrc_core_type_remove_duplicate_env nil v1 τl l) in H9; eauto.
        * eapply (IHe2 ((v, τl) :: l)); eauto.
          rewrite <- remove_in_neq in neq2; intuition.
      + destruct (equiv_dec v0 v1); unfold Equivalence.equiv in *; subst.
        * apply (nnrc_core_type_remove_duplicate_env nil v1 τr l) in H10; eauto.
        * eapply (IHe3 ((v0, τr) :: l)); eauto.
          rewrite <- remove_in_neq in neq3; intuition.
    - constructor. erewrite lookup_remove_nin; eauto.
    - apply nin_app_or in H. intuition. eauto.
    - apply nin_app_or in H. intuition.
      econstructor; eauto.
      destruct (equiv_dec v v0); unfold Equivalence.equiv in *; subst.
      + apply (nnrc_core_type_remove_duplicate_env nil v0 τ₁ l); eauto.
      + eapply (IHe2 ((v, τ₁) :: l)); eauto.
        intro; elim H2; apply remove_in_neq; eauto.
    - apply nin_app_or in H. intuition.
      econstructor; eauto.
      destruct (equiv_dec v v0); unfold Equivalence.equiv in *; subst.
      + apply (nnrc_core_type_remove_duplicate_env nil v0 τ₁ l); eauto.
      + eapply (IHe2 ((v, τ₁) :: l)); eauto. 
        intro; elim H2; apply remove_in_neq; eauto.
    - apply nin_app_or in H; destruct H as [? HH]; apply nin_app_or in HH.
      intuition.
    - apply nin_app_or in H. destruct H as [neq1 neq2].
      apply nin_app_or in neq2; destruct neq2  as [neq2 neq3].
      econstructor; eauto.
      + destruct (equiv_dec v v1); unfold Equivalence.equiv in *; subst.
        * apply (nnrc_core_type_remove_duplicate_env nil v1 τl l); simpl; trivial.
        * eapply (IHe2 ((v, τl) :: l)); eauto.
          rewrite <- remove_in_neq in neq2; intuition.
      + destruct (equiv_dec v0 v1); unfold Equivalence.equiv in *; subst.
        * apply (nnrc_core_type_remove_duplicate_env nil v1 τr l); simpl; trivial.
        * eapply (IHe3 ((v0, τr) :: l)); eauto.
          rewrite <- remove_in_neq in neq3; intuition.
  Qed.

  Lemma nnrc_core_type_remove_disjoint_env {τcenv} l1 l2 l3 e τ :
    disjoint (domain l2) (nnrc_free_vars e) ->
    (nnrc_core_type τcenv (l1 ++ l2 ++ l3) e τ <-> nnrc_core_type τcenv (l1 ++ l3) e τ).
  Proof.
    revert l1 l3.
    induction l2; intros l1 l3 disj; simpl.
    - tauto.
    - simpl in disj.
      apply disjoint_cons_inv1 in disj.
      destruct disj as [disj nin].
      destruct a; simpl in *.
      rewrite nnrc_core_type_remove_free_env; trivial.
      eauto.
  Qed.

  Lemma nnrc_core_type_remove_almost_free_env {τcenv} l v x l' e τ :
    (In v (nnrc_free_vars e) -> In v (domain l)) ->
    (nnrc_core_type τcenv (l ++ (v,x)::l') e τ <-> nnrc_core_type τcenv (l ++ l') e τ).
  Proof.
    intros Hinn.
    destruct (in_dec string_dec v (nnrc_free_vars e)) as [inn|inn].
    - apply Hinn in inn.
      apply in_domain_in in inn.
      destruct inn as [? inn].
      destruct (in_split _ _ inn) as [? [? ?]]; subst.
      repeat rewrite app_ass; simpl.
      apply nnrc_core_type_remove_duplicate_env.
    - apply nnrc_core_type_remove_free_env; trivial.
  Qed.

  Lemma nnrc_core_type_remove_almost_disjoint_env {τcenv} l1 l2 l3 e τ :
    (forall x,
        In x (domain l2) -> 
        In x (nnrc_free_vars e) -> In x (domain l1)) ->
    (nnrc_core_type τcenv (l1 ++ l2 ++ l3) e τ <-> nnrc_core_type τcenv (l1 ++ l3) e τ).
  Proof.
    revert l1 l3.
    induction l2; intros l1 l3 disj; simpl.
    - tauto.
    - simpl in disj.
      destruct a; simpl in *.
      rewrite nnrc_core_type_remove_almost_free_env; trivial.
      + eauto.
      + intuition.
  Qed.
  
  Lemma nnrc_core_type_swap_neq {τcenv} l1 v1 x1 v2 x2 l2 e τ :
    v1 <> v2 ->
    (nnrc_core_type τcenv (l1++(v1,x1)::(v2,x2)::l2) e τ <-> 
     nnrc_core_type τcenv (l1++(v2,x2)::(v1,x1)::l2) e τ).
  Proof.
    intros.
    apply nnrc_core_type_lookup_equiv_prop; trivial.
    apply lookup_swap_neq; trivial.
  Qed.

  Lemma nnrc_core_type_cons_subst {τcenv} e Γ v τ₀ v' τ :
    ~ (In v' (nnrc_free_vars e)) ->
    ~ (In v' (nnrc_bound_vars e)) ->
    (nnrc_core_type τcenv ((v',τ₀)::Γ) (nnrc_subst e v (NNRCVar v')) τ <->
     nnrc_core_type τcenv ((v,τ₀)::Γ) e τ).
  Proof.
    split; revert Γ v τ₀ v' τ H H0;
      induction e; simpl in *; unfold equiv_dec, string_eqdec; 
        trivial; intros Γ v₀ τ₀ v' τ nfree nbound.
    - intuition.
      constructor.
      destruct (string_dec v v₀); simpl; subst; intuition; inversion H; subst; simpl in *; repeat dest_eqdec; intuition.
    - intuition.
      constructor.
      destruct (string_dec v v₀); simpl; subst; intuition; inversion H; subst; simpl in *; repeat dest_eqdec; intuition.
    - inversion 1; subst. eauto.
    - inversion 1; subst.
      rewrite nin_app_or in nfree, nbound.
      intuition; eauto.
    - inversion 1; subst. eauto.
    - inversion 1; subst.
      rewrite nin_app_or in nfree. intuition.
      apply nin_app_or in H3. intuition.
      match_destr_in H; subst.
      + econstructor; eauto.
        apply (nnrc_core_type_remove_duplicate_env nil v₀ τ₁ nil); simpl.
        generalize (@nnrc_core_type_remove_free_env τcenv ((v₀,τ₁)::nil)); simpl; intros HH.
        apply HH in H6; eauto.
        intro; elim H1. apply remove_in_neq; eauto.
      + econstructor; eauto.
        apply (nnrc_core_type_swap_neq nil); eauto; simpl.
        eapply IHe2; eauto.
        * intro; elim H1.
          apply remove_in_neq; eauto.
        * apply (nnrc_core_type_swap_neq nil); eauto; simpl.
    - inversion 1; subst.
      rewrite nin_app_or in nfree. intuition.
      apply nin_app_or in H3. intuition.
      match_destr_in H6; subst.
      + econstructor; eauto.
        apply (nnrc_core_type_remove_duplicate_env nil v₀ τ₁ nil); simpl.
        generalize (@nnrc_core_type_remove_free_env τcenv ((v₀,τ₁)::nil)); simpl; intros HH.
        apply HH in H6; eauto.
        intro; elim H1. apply remove_in_neq; eauto.
      + econstructor; eauto.
        apply (nnrc_core_type_swap_neq nil); eauto; simpl.
        eapply IHe2; eauto.
        * intro; elim H1.
          apply remove_in_neq; eauto.
        * apply (nnrc_core_type_swap_neq nil); eauto; simpl.
    - inversion 1; subst.
      apply nin_app_or in nfree; destruct nfree as [? HH]; apply nin_app_or in HH.
      apply nin_app_or in nbound; destruct nbound as [? HHH]; apply nin_app_or in HHH.
      intuition; eauto.
    - intro HH; inversion HH; subst; clear HH.
      apply not_or in nbound; destruct nbound as [nb1 nb2].
      apply not_or in nb2; destruct nb2 as [nb2 nb3].
      repeat rewrite nin_app_or in nb3, nfree.
      rewrite <- (remove_in_neq _ _ v) in nfree by congruence.
      rewrite <- (remove_in_neq _ _ v0) in nfree by congruence.
      econstructor.
      + eapply IHe1; eauto 2; intuition.
      + match_destr_in H7; subst.
        * generalize (@nnrc_core_type_remove_free_env τcenv ((v₀,τl)::nil)); simpl;
            intros re1; rewrite re1 in H7 by intuition.
          generalize (@nnrc_core_type_remove_duplicate_env τcenv nil v₀ τl nil); simpl;
            intros re2; rewrite re2 by intuition.
          trivial.
        * apply (nnrc_core_type_swap_neq nil); eauto 2; simpl.
          apply (nnrc_core_type_swap_neq nil) in H7; eauto 2; simpl in *.
          eapply IHe2; eauto 2; intuition.
      + match_destr_in H8; subst.
        * generalize (@nnrc_core_type_remove_free_env τcenv ((v₀,τr)::nil)); simpl;
            intros re1; rewrite re1 in H8 by intuition.
          generalize (@nnrc_core_type_remove_duplicate_env τcenv nil v₀ τr nil); simpl;
            intros re2; rewrite re2 by intuition.
          trivial.
        * apply (nnrc_core_type_swap_neq nil); eauto 2; simpl.
          apply (nnrc_core_type_swap_neq nil) in H8; eauto 2; simpl in *.
          eapply IHe3; eauto 2; intuition.
    - (* GroupBy Case: always fails for core? *)
      intros.
      inversion H.
    - intuition.
      destruct (string_dec v v₀); simpl; subst; intuition; 
        inversion H; subst; simpl in *; repeat dest_eqdec; intuition;
          inversion H4; subst; constructor; simpl;
            repeat dest_eqdec; intuition.
    - intuition.
      destruct (string_dec v v₀); simpl; subst; intuition; 
        inversion H; subst; simpl in *; repeat dest_eqdec; intuition;
          inversion H4; subst; constructor; simpl;
            repeat dest_eqdec; intuition.
    - inversion 1; subst. eauto.
    - inversion 1; subst.
      rewrite nin_app_or in nfree, nbound.
      intuition; eauto.
    - inversion 1; subst. eauto.
    - inversion 1; subst.
      rewrite nin_app_or in nfree. intuition.
      apply nin_app_or in H3. intuition.
      match_destr; subst.
      + econstructor; eauto.
        apply (nnrc_core_type_remove_duplicate_env nil v₀ τ₁ nil) in H6; 
          simpl in H6.
        generalize (@nnrc_core_type_remove_free_env τcenv ((v₀,τ₁)::nil)); simpl; intros HH.
        apply HH; eauto.
        intro; elim H1. apply remove_in_neq; eauto.
      + econstructor; eauto.
        apply (nnrc_core_type_swap_neq nil); eauto; simpl.
        eapply IHe2; eauto.
        * intro; elim H1.
          apply remove_in_neq; eauto.
        * apply (nnrc_core_type_swap_neq nil); eauto; simpl.
    - inversion 1; subst.
      rewrite nin_app_or in nfree. intuition.
      apply nin_app_or in H3. intuition.
      match_destr; subst.
      + econstructor; eauto.
        apply (nnrc_core_type_remove_duplicate_env nil v₀ τ₁ nil) in H6; 
          simpl in H6.
        generalize (@nnrc_core_type_remove_free_env τcenv ((v₀,τ₁)::nil)); simpl; intros HH.
        apply HH; eauto.
        intro; elim H1. apply remove_in_neq; eauto.
      + econstructor; eauto.
        apply (nnrc_core_type_swap_neq nil); eauto; simpl.
        eapply IHe2; eauto.
        * intro; elim H1.
          apply remove_in_neq; eauto.
        * apply (nnrc_core_type_swap_neq nil); eauto; simpl.
    - inversion 1; subst.
      apply nin_app_or in nfree; destruct nfree as [? HH]; apply nin_app_or in HH.
      apply nin_app_or in nbound; destruct nbound as [? HHH]; apply nin_app_or in HHH.
      intuition; eauto.
    - apply not_or in nbound; destruct nbound as [nb1 nb2].
      apply not_or in nb2; destruct nb2 as [nb2 nb3].
      repeat rewrite nin_app_or in nb3, nfree.
      rewrite <- (remove_in_neq _ _ v) in nfree by congruence.
      rewrite <- (remove_in_neq _ _ v0) in nfree by congruence.    
      intro HH; inversion HH; clear HH; subst.
      econstructor.
      + apply IHe1; eauto 2; intuition.
      + match_destr; subst.
        * generalize (@nnrc_core_type_remove_duplicate_env τcenv nil v₀ τl nil); simpl;
            intros re1; rewrite re1 in H7.
          apply (nnrc_core_type_remove_free_env ((v₀,τl)::nil)); intuition.
        * apply (nnrc_core_type_swap_neq nil); eauto; simpl.
          apply IHe2; eauto 2; intuition.
          apply (nnrc_core_type_swap_neq nil); eauto; simpl.
      + match_destr; subst.
        * generalize (@nnrc_core_type_remove_duplicate_env τcenv nil v₀ τr nil); simpl;
            intros re1; rewrite re1 in H8.
          apply (nnrc_core_type_remove_free_env ((v₀,τr)::nil)); intuition.
        * apply (nnrc_core_type_swap_neq nil); eauto; simpl.
          apply IHe3; eauto 2; intuition.
          apply (nnrc_core_type_swap_neq nil); eauto; simpl.
    - (* GroupBy Case: always fails for core? *)
      intros.
      inversion H.
  Qed.

  Lemma nnrc_core_type_cons_subst_disjoint {τcenv} e e' Γ v τ₀ τ :
    disjoint (nnrc_bound_vars e) (nnrc_free_vars e') ->
    nnrc_core_type τcenv Γ e' τ₀ ->
    nnrc_core_type τcenv ((v,τ₀)::Γ) e τ ->
    nnrc_core_type τcenv Γ (nnrc_subst e v e') τ.
  Proof.
    intros disj typ'.
    revert Γ e' v τ₀ τ disj typ'.
    nnrc_cases (induction e) Case; simpl in *; 
      trivial; intros Γ v₀ τ₀ v' τ nfree nbound; simpl;
        intros typ; inversion typ; clear typ; subst;
          unfold equiv_dec in *; simpl in * .
    - Case "NNRCGetConstant"%string.
      eauto.
    - Case "NNRCVar"%string.
      match_destr.
      + congruence.
      + auto.
    - Case "NNRCConst"%string.
      econstructor; trivial.
    - Case "NNRCBinop"%string.
      apply disjoint_app_l in nfree.
      destruct nfree.
      econstructor; eauto 2.
    - Case "NNRCUnop"%string.
      econstructor; eauto.
    - Case "NNRCLet"%string.
      apply disjoint_cons_inv1 in nfree.
      destruct nfree as [disj nin].
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      econstructor; eauto 2.
      match_destr.
      + red in e; subst.
        generalize (@nnrc_core_type_remove_duplicate_env τcenv nil τ₀ τ₁ nil v' Γ);
          simpl; intros re1; apply re1; eauto.
      + eapply IHe2; eauto 2.
        * generalize (@nnrc_core_type_remove_free_env τcenv nil v τ₁ Γ v₀);
            simpl; intros re1; apply re1; eauto.
        * generalize (@nnrc_core_type_swap_neq τcenv nil τ₀ v' v τ₁ Γ e2 τ);
            simpl; intros re1; apply re1; eauto.
    - Case "NNRCFor"%string.
      apply disjoint_cons_inv1 in nfree.
      destruct nfree as [disj nin].
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      econstructor; eauto 2.
      match_destr.
      + red in e; subst.
        generalize (@nnrc_core_type_remove_duplicate_env τcenv nil τ₀ τ₁ nil v' Γ);
          simpl; intros re1; apply re1; eauto.
      + eapply IHe2; eauto 2.
        * generalize (@nnrc_core_type_remove_free_env τcenv nil v τ₁ Γ v₀);
            simpl; intros re1; apply re1; eauto.
        * generalize (@nnrc_core_type_swap_neq τcenv nil τ₀ v' v τ₁ Γ e2 τ₂);
            simpl; intros re1; apply re1; eauto.
    - Case "NNRCIf"%string.
      apply disjoint_app_l in nfree.
      destruct nfree as [disj1 disj2].
      apply disjoint_app_l in disj2.
      destruct disj2 as [disj2 disj3].
      econstructor; eauto 2.
    - Case "NNRCEither"%string.
      apply disjoint_cons_inv1 in nfree.
      destruct nfree as [disj nin].
      apply disjoint_cons_inv1 in disj.
      destruct disj as [disj nin2].
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      apply disjoint_app_l in disj2.
      destruct disj2 as [disj2 disj3].
      econstructor; eauto 2.
      + {
          match_destr.
          + red in e; subst.
            generalize (@nnrc_core_type_remove_duplicate_env τcenv nil τ₀ τl nil v' Γ);
              simpl; intros re1; apply re1; eauto.
          + eapply IHe2; eauto 2.
            * generalize (@nnrc_core_type_remove_free_env τcenv nil v τl Γ v₀);
                simpl; intros re1; apply re1; eauto.
            * generalize (@nnrc_core_type_swap_neq τcenv nil τ₀ v' v τl Γ e2 τ);
                simpl; intros re1; apply re1; eauto.
        }  
      + {
          match_destr.
          + red in e; subst.
            generalize (@nnrc_core_type_remove_duplicate_env τcenv nil τ₀ τr nil v' Γ);
              simpl; intros re1; apply re1; eauto.
          + eapply IHe3; eauto 2.
            * generalize (@nnrc_core_type_remove_free_env τcenv nil v0 τr Γ v₀);
                simpl; intros re1; apply re1; eauto.
            * generalize (@nnrc_core_type_swap_neq τcenv nil τ₀ v' v0 τr Γ e3 τ);
                simpl; intros re1; apply re1; eauto.
        }
  Qed.

  Lemma nnrc_core_type_rename_pick_subst {τcenv} sep renamer avoid e Γ v τ₀ τ :
    (nnrc_core_type τcenv
                    ((nnrc_pick_name sep renamer avoid v e,τ₀)::Γ)
                    (nnrc_rename_lazy e v (nnrc_pick_name sep renamer avoid v e)) τ
     <->
     nnrc_core_type τcenv ((v,τ₀)::Γ) e τ).
  Proof.
    unfold nnrc_rename_lazy.
    match_destr.
    - rewrite <- e0.
      tauto.
    - rewrite nnrc_core_type_cons_subst; trivial.
      + tauto.
      + apply nnrc_pick_name_neq_nfree; trivial.
      + apply nnrc_pick_name_bound.
  Qed.

  Theorem nnrc_core_unshadow_type {τcenv} sep renamer avoid Γ n τ :
    nnrc_core_type τcenv Γ n τ <-> nnrc_core_type τcenv Γ (unshadow sep renamer avoid n) τ.
  Proof.
    Hint Resolve really_fresh_from_free  really_fresh_from_bound.
    split; revert Γ τ; induction n; simpl in *; inversion 1; subst; eauto; simpl.
    - econstructor; [eauto|..].
      apply nnrc_core_type_rename_pick_subst.
      eauto.
    - econstructor; [eauto|..].
      apply nnrc_core_type_rename_pick_subst.
      eauto.
    - econstructor; [eauto|..].
      apply nnrc_core_type_rename_pick_subst.
      + eauto.
      + apply nnrc_core_type_rename_pick_subst.
        eauto.
    - econstructor; [eauto|..].
      apply nnrc_core_type_rename_pick_subst in H6.
      eauto.
    - econstructor; [eauto|..].
      apply nnrc_core_type_rename_pick_subst in H6.
      eauto.
    - econstructor; [eauto|..].
      + apply nnrc_core_type_rename_pick_subst in H8.
        eauto.
      + apply nnrc_core_type_rename_pick_subst in H9.
        eauto.
  Qed.

End TcNNRCShadow.

