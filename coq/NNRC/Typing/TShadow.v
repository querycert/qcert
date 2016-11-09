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

Section TShadow.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import Peano_dec.
  Require Import EquivDec Decidable.

  Require Import Utils BasicSystem.

  Require Import NNRC NNRCShadow TNRC.
  
  Hint Constructors nrc_type.

  Context {m:basic_model}.

  Lemma nrc_type_remove_duplicate_env  l v x l' x' l'' e τ:
    nrc_type (l ++ (v,x)::l' ++ (v,x')::l'') e τ <->
    nrc_type (l ++ (v,x)::l' ++ l'') e τ.
  Proof.
    apply nrc_type_lookup_equiv_prop; trivial.
    apply lookup_remove_duplicate.
  Qed.
  
 Lemma nrc_type_remove_free_env  l v x l' e τ :
          ~ In v (nrc_free_vars e) ->
          (nrc_type (l ++ (v,x)::l') e τ <-> nrc_type (l ++ l') e τ).
  Proof.
    split; revert l v x l' τ H;
    induction e; simpl; inversion 2; subst; intuition; eauto 3.
    - constructor. erewrite <- lookup_remove_nin; eauto.
    - apply nin_app_or in H. intuition. eauto.
    - apply nin_app_or in H. intuition.
      econstructor; eauto.
      destruct (equiv_dec v v0); unfold Equivalence.equiv in *; subst.
      + apply (nrc_type_remove_duplicate_env nil v0 τ₁ l) in H7; eauto.
      + eapply (IHe2 ((v, τ₁) :: l)); eauto. 
        intro; elim H2; apply remove_in_neq; eauto.
    - apply nin_app_or in H. intuition.
      econstructor; eauto.
      destruct (equiv_dec v v0); unfold Equivalence.equiv in *; subst.
      + apply (nrc_type_remove_duplicate_env nil v0 τ₁ l) in H7; eauto.
      + eapply (IHe2 ((v, τ₁) :: l)); eauto. 
         intro; elim H2; apply remove_in_neq; eauto.
    - apply nin_app_or in H; destruct H as [? HH]; apply nin_app_or in HH.
      intuition. eauto.
    - apply nin_app_or in H. destruct H as [neq1 neq2].
      apply nin_app_or in neq2. destruct neq2 as [neq2 neq3].
      econstructor; eauto.
      + destruct (equiv_dec v v1); unfold Equivalence.equiv in *; subst.
         * apply (nrc_type_remove_duplicate_env nil v1 τl l) in H9; eauto.
         * eapply (IHe2 ((v, τl) :: l)); eauto.
           rewrite <- remove_in_neq in neq2; intuition.
      + destruct (equiv_dec v0 v1); unfold Equivalence.equiv in *; subst.
         * apply (nrc_type_remove_duplicate_env nil v1 τr l) in H10; eauto.
         * eapply (IHe3 ((v0, τr) :: l)); eauto.
           rewrite <- remove_in_neq in neq3; intuition.
    - constructor. erewrite lookup_remove_nin; eauto.
    - apply nin_app_or in H. intuition. eauto.
    - apply nin_app_or in H. intuition.
      econstructor; eauto.
      destruct (equiv_dec v v0); unfold Equivalence.equiv in *; subst.
      + apply (nrc_type_remove_duplicate_env nil v0 τ₁ l); eauto.
      + eapply (IHe2 ((v, τ₁) :: l)); eauto.
        intro; elim H2; apply remove_in_neq; eauto.
    - apply nin_app_or in H. intuition.
      econstructor; eauto.
      destruct (equiv_dec v v0); unfold Equivalence.equiv in *; subst.
      + apply (nrc_type_remove_duplicate_env nil v0 τ₁ l); eauto.
      + eapply (IHe2 ((v, τ₁) :: l)); eauto. 
         intro; elim H2; apply remove_in_neq; eauto.
    - apply nin_app_or in H; destruct H as [? HH]; apply nin_app_or in HH.
      intuition.
    - apply nin_app_or in H. destruct H as [neq1 neq2].
      apply nin_app_or in neq2; destruct neq2  as [neq2 neq3].
            econstructor; eauto.
      + destruct (equiv_dec v v1); unfold Equivalence.equiv in *; subst.
         * apply (nrc_type_remove_duplicate_env nil v1 τl l); simpl; trivial.
         * eapply (IHe2 ((v, τl) :: l)); eauto.
           rewrite <- remove_in_neq in neq2; intuition.
      + destruct (equiv_dec v0 v1); unfold Equivalence.equiv in *; subst.
         * apply (nrc_type_remove_duplicate_env nil v1 τr l); simpl; trivial.
         * eapply (IHe3 ((v0, τr) :: l)); eauto.
           rewrite <- remove_in_neq in neq3; intuition.
  Qed.

  Lemma nrc_type_swap_neq  l1 v1 x1 v2 x2 l2 e τ :
    v1 <> v2 ->
    (nrc_type (l1++(v1,x1)::(v2,x2)::l2) e τ <-> 
     nrc_type (l1++(v2,x2)::(v1,x1)::l2) e τ).
  Proof.
    intros.
    apply nrc_type_lookup_equiv_prop; trivial.
    apply lookup_swap_neq; trivial.
  Qed.

Lemma nrc_type_cons_subst  e Γ v τ₀ v' τ :
         ~ (In v' (nrc_free_vars e)) ->
         ~ (In v' (nrc_bound_vars e)) ->
         (nrc_type ((v',τ₀)::Γ) (nrc_subst e v (NRCVar v')) τ <->
         nrc_type ((v,τ₀)::Γ) e τ).
  Proof.
    split; revert Γ v τ₀ v' τ H H0;
    induction e; simpl in *; unfold equiv_dec, string_eqdec; 
      trivial; intros Γ v₀ τ₀ v' τ nfree nbound.
    -  intuition.
       constructor. destruct (string_dec v v₀); simpl; subst; intuition; inversion H; subst; simpl in *; repeat dest_eqdec; intuition.
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
         apply (nrc_type_remove_duplicate_env nil v₀ τ₁ nil); simpl.
         generalize (nrc_type_remove_free_env ((v₀,τ₁)::nil)); simpl; intros HH.
         apply HH in H6; eauto.
         intro; elim H1. apply remove_in_neq; eauto.
      + econstructor; eauto.
         apply (nrc_type_swap_neq nil); eauto; simpl.
         eapply IHe2; eauto.
         * intro; elim H1.
           apply remove_in_neq; eauto.
         * apply (nrc_type_swap_neq nil); eauto; simpl.
    - inversion 1; subst.
      rewrite nin_app_or in nfree. intuition.
      apply nin_app_or in H3. intuition.
      match_destr_in H6; subst.
      + econstructor; eauto.
         apply (nrc_type_remove_duplicate_env nil v₀ τ₁ nil); simpl.
         generalize (nrc_type_remove_free_env ((v₀,τ₁)::nil)); simpl; intros HH.
         apply HH in H6; eauto.
         intro; elim H1. apply remove_in_neq; eauto.
      + econstructor; eauto.
         apply (nrc_type_swap_neq nil); eauto; simpl.
         eapply IHe2; eauto.
         * intro; elim H1.
           apply remove_in_neq; eauto.
         * apply (nrc_type_swap_neq nil); eauto; simpl.
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
        * generalize (nrc_type_remove_free_env ((v₀,τl)::nil)); simpl;
          intros re1; rewrite re1 in H7 by intuition.
          generalize (nrc_type_remove_duplicate_env nil v₀ τl nil); simpl;
          intros re2; rewrite re2 by intuition.
          trivial.
        * apply (nrc_type_swap_neq nil); eauto 2; simpl.
          apply (nrc_type_swap_neq nil) in H7; eauto 2; simpl in *.
           eapply IHe2; eauto 2; intuition.
      + match_destr_in H8; subst.
        * generalize (nrc_type_remove_free_env ((v₀,τr)::nil)); simpl;
          intros re1; rewrite re1 in H8 by intuition.
          generalize (nrc_type_remove_duplicate_env nil v₀ τr nil); simpl;
          intros re2; rewrite re2 by intuition.
          trivial.
        * apply (nrc_type_swap_neq nil); eauto 2; simpl.
          apply (nrc_type_swap_neq nil) in H8; eauto 2; simpl in *.
           eapply IHe3; eauto 2; intuition.
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
         apply (nrc_type_remove_duplicate_env nil v₀ τ₁ nil) in H6; 
          simpl in H6.
         generalize (nrc_type_remove_free_env ((v₀,τ₁)::nil)); simpl; intros HH.
         apply HH; eauto.
         intro; elim H1. apply remove_in_neq; eauto.
      + econstructor; eauto.
         apply (nrc_type_swap_neq nil); eauto; simpl.
         eapply IHe2; eauto.
         * intro; elim H1.
           apply remove_in_neq; eauto.
         * apply (nrc_type_swap_neq nil); eauto; simpl.
    - inversion 1; subst.
      rewrite nin_app_or in nfree. intuition.
      apply nin_app_or in H3. intuition.
      match_destr; subst.
      + econstructor; eauto.
         apply (nrc_type_remove_duplicate_env nil v₀ τ₁ nil) in H6; 
          simpl in H6.
         generalize (nrc_type_remove_free_env ((v₀,τ₁)::nil)); simpl; intros HH.
         apply HH; eauto.
         intro; elim H1. apply remove_in_neq; eauto.
      + econstructor; eauto.
         apply (nrc_type_swap_neq nil); eauto; simpl.
         eapply IHe2; eauto.
         * intro; elim H1.
           apply remove_in_neq; eauto.
         * apply (nrc_type_swap_neq nil); eauto; simpl.
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
        * generalize (nrc_type_remove_duplicate_env nil v₀ τl nil); simpl;
          intros re1; rewrite re1 in H7.
          apply (nrc_type_remove_free_env ((v₀,τl)::nil)); intuition.
        * apply (nrc_type_swap_neq nil); eauto; simpl.
          apply IHe2; eauto 2; intuition.
          apply (nrc_type_swap_neq nil); eauto; simpl.
      + match_destr; subst.
        * generalize (nrc_type_remove_duplicate_env nil v₀ τr nil); simpl;
          intros re1; rewrite re1 in H8.
          apply (nrc_type_remove_free_env ((v₀,τr)::nil)); intuition.
        * apply (nrc_type_swap_neq nil); eauto; simpl.
          apply IHe3; eauto 2; intuition.
          apply (nrc_type_swap_neq nil); eauto; simpl.
  Qed.

  Lemma nrc_type_cons_subst_disjoint  e e' Γ v τ₀ τ :
    disjoint (nrc_bound_vars e) (nrc_free_vars e') ->
         nrc_type Γ e' τ₀ ->
         nrc_type ((v,τ₀)::Γ) e τ ->
         nrc_type Γ (nrc_subst e v e') τ.
  Proof.
    intros disj typ'.
    revert Γ e' v τ₀ τ disj typ'.
    nrc_cases (induction e) Case; simpl in *; 
      trivial; intros Γ v₀ τ₀ v' τ nfree nbound; simpl;
        intros typ; inversion typ; clear typ; subst;
          unfold equiv_dec in *; simpl in * .
    - Case "NRCVar"%string.
      match_destr.
      + congruence.
      + auto.
    - Case "NRCConst"%string.
      econstructor; trivial.
    - Case "NRCBinop"%string.
      apply disjoint_app_l in nfree.
      destruct nfree.
      econstructor; eauto 2.
    - Case "NRCUnop"%string.
      econstructor; eauto.
    - Case "NRCLet"%string.
      apply disjoint_cons_inv1 in nfree.
      destruct nfree as [disj nin].
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      econstructor; eauto 2.
      match_destr.
      + red in e; subst.
        generalize (nrc_type_remove_duplicate_env nil τ₀ τ₁ nil v' Γ);
          simpl; intros re1; apply re1; eauto.
      + eapply IHe2; eauto 2.
        * generalize (nrc_type_remove_free_env nil v τ₁ Γ v₀);
            simpl; intros re1; apply re1; eauto.
        * generalize (nrc_type_swap_neq nil τ₀ v' v τ₁ Γ e2 τ);
            simpl; intros re1; apply re1; eauto.
    - Case "NRCFor"%string.
      apply disjoint_cons_inv1 in nfree.
      destruct nfree as [disj nin].
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      econstructor; eauto 2.
      match_destr.
      + red in e; subst.
        generalize (nrc_type_remove_duplicate_env nil τ₀ τ₁ nil v' Γ);
          simpl; intros re1; apply re1; eauto.
      + eapply IHe2; eauto 2.
        * generalize (nrc_type_remove_free_env nil v τ₁ Γ v₀);
            simpl; intros re1; apply re1; eauto.
        * generalize (nrc_type_swap_neq nil τ₀ v' v τ₁ Γ e2 τ₂);
            simpl; intros re1; apply re1; eauto.
    - Case "NRCIf"%string.
      apply disjoint_app_l in nfree.
      destruct nfree as [disj1 disj2].
      apply disjoint_app_l in disj2.
      destruct disj2 as [disj2 disj3].
      econstructor; eauto 2.
    - apply disjoint_cons_inv1 in nfree.
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
            generalize (nrc_type_remove_duplicate_env nil τ₀ τl nil v' Γ);
              simpl; intros re1; apply re1; eauto.
          + eapply IHe2; eauto 2.
            * generalize (nrc_type_remove_free_env nil v τl Γ v₀);
                simpl; intros re1; apply re1; eauto.
            * generalize (nrc_type_swap_neq nil τ₀ v' v τl Γ e2 τ);
                simpl; intros re1; apply re1; eauto.
        }  
      + {
          match_destr.
          + red in e; subst.
            generalize (nrc_type_remove_duplicate_env nil τ₀ τr nil v' Γ);
              simpl; intros re1; apply re1; eauto.
          + eapply IHe3; eauto 2.
            * generalize (nrc_type_remove_free_env nil v0 τr Γ v₀);
                simpl; intros re1; apply re1; eauto.
            * generalize (nrc_type_swap_neq nil τ₀ v' v0 τr Γ e3 τ);
                simpl; intros re1; apply re1; eauto.
        }  
  Qed.

  Lemma nrc_type_rename_pick_subst sep renamer avoid e Γ v τ₀ τ :
         (nrc_type ((nrc_pick_name sep renamer avoid v e,τ₀)::Γ) (nrc_rename_lazy e v (nrc_pick_name sep renamer avoid v e)) τ <->
         nrc_type ((v,τ₀)::Γ) e τ).
  Proof.
    unfold nrc_rename_lazy.
    match_destr.
    - rewrite <- e0.
      tauto.
    - rewrite nrc_type_cons_subst; trivial.
      + tauto.
      + apply nrc_pick_name_neq_nfree; trivial.
      + apply nrc_pick_name_bound.
  Qed.

  Theorem unshadow_type  sep renamer avoid Γ n τ :
    nrc_type Γ n τ <-> nrc_type Γ (unshadow sep renamer avoid n) τ.
  Proof.
    Hint Resolve really_fresh_from_free  really_fresh_from_bound.
    split; revert Γ τ; induction n; simpl in *; inversion 1; subst; eauto; simpl.
    - econstructor; [eauto|..].
      apply nrc_type_rename_pick_subst.
      eauto.
    - econstructor; [eauto|..].
      apply nrc_type_rename_pick_subst.
      eauto.
    - econstructor; [eauto|..].
      apply nrc_type_rename_pick_subst.
      + eauto.
      + apply nrc_type_rename_pick_subst.
        eauto.
    - econstructor; [eauto|..].
      apply nrc_type_rename_pick_subst in H6.
      eauto.
    - econstructor; [eauto|..].
      apply nrc_type_rename_pick_subst in H6.
      eauto.
    - econstructor; [eauto|..].
      + apply nrc_type_rename_pick_subst in H8.
        eauto.
      + apply nrc_type_rename_pick_subst in H9.
        eauto.
  Qed.    

End TShadow.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
