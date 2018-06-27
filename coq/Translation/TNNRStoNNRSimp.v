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
Require Import Bool.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Permutation.
Require Import Eqdep_dec.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import NNRSSystem.
Require Import NNRSimpSystem.
Require Import NNRStoNNRSimp.

Section TNNRStoNNRSimp.

  Context {m:basic_model}.
  Context (τconstants:tbindings).

  Definition lift_pdtype (τo:option rtype) : rtype
    := match τo with
       | Some τ => τ
       | None => ⊤
       end.
  
  Definition pd_tbindings_lift (Γ:TNNRS.pd_tbindings) : TNNRSimp.pd_tbindings
    := map_codomain lift_pdtype Γ.

  Lemma lookup_pd_tbindings_lift Γ v :
    lookup equiv_dec (pd_tbindings_lift Γ) v = lift lift_pdtype (lookup equiv_dec Γ v).
  Proof.
    apply lookup_map_codomain.
  Qed.

  Lemma tnnrs_expr_to_nnrs_expr_correct_f:
    forall Γc Γ (e:nnrs_expr) (τ:rtype),
      ([ Γc ; Γ  ⊢ e ▷ τ ])%nnrs_scope -> [ Γc ; pd_tbindings_lift Γ  ⊢ (nnrs_expr_to_nnrs_imp_expr e) ▷ τ ]%nnrs_imp_scope.
  Proof.
    Hint Constructors nnrs_imp_expr_type.
    intros Γc Γ e.
    revert Γ.
    induction e
    ; simpl
    ; intros Γ τ typ
    ; invcs typ
    ; econstructor; eauto.
    - rewrite lookup_pd_tbindings_lift.
      rewrite H1.
      simpl; trivial.
  Qed.

  Lemma tnnrs_expr_to_nnrs_expr_correct_b:
    forall Γc Γ (e:nnrs_expr) (τ:rtype),
      (forall x, In x (nnrs_expr_free_vars e) -> lookup equiv_dec Γ x <> Some None) ->
      [ Γc ; pd_tbindings_lift Γ  ⊢ (nnrs_expr_to_nnrs_imp_expr e) ▷ τ ]%nnrs_imp_scope -> ([ Γc ; Γ  ⊢ e ▷ τ ])%nnrs_scope.
  Proof.
    Hint Constructors nnrs_expr_type.
    intros Γc Γ e.
    revert Γ.
    induction e
    ; simpl
    ; intros Γ τ fns typ
    ; invcs typ
    ; econstructor; eauto.
    - rewrite lookup_pd_tbindings_lift in H1.
      apply some_lift in H1.
      destruct H1 as [???]; subst.
      specialize (fns v); unfold var in *.
      rewrite e in *.
      destruct x; simpl; intuition.
    - eapply IHe1; trivial.
      intros; apply fns.
      rewrite in_app_iff; intuition.
    - eapply IHe2; trivial.
      intros; apply fns.
      rewrite in_app_iff; intuition.
  Qed.
  
  Definition concat_tenvs
             (Γ :TNNRS.pd_tbindings)
             (Δc :TNNRS.mc_tbindings)
             (Δd :TNNRS.md_tbindings)
    : TNNRSimp.pd_tbindings
    := pd_tbindings_lift Γ ++ map_codomain Coll Δc ++ Δd.

  Lemma concat_tenvs_cons (Γ :TNNRS.pd_tbindings)
        (Δc :TNNRS.mc_tbindings)
        (Δd :TNNRS.md_tbindings) s τ :
    (s,lift_pdtype τ)::concat_tenvs Γ Δc Δd = concat_tenvs ((s,τ)::Γ) Δc Δd.
  Proof.
    reflexivity.
  Qed.

  Lemma concat_tenvs_cons_some (Γ :TNNRS.pd_tbindings)
        (Δc :TNNRS.mc_tbindings)
        (Δd :TNNRS.md_tbindings) s τ :
    (s, τ)::concat_tenvs Γ Δc Δd = concat_tenvs ((s,Some τ)::Γ) Δc Δd.
  Proof.
    reflexivity.
  Qed.

  Lemma concat_tenvs_cons_none (Γ :TNNRS.pd_tbindings)
        (Δc :TNNRS.mc_tbindings)
        (Δd :TNNRS.md_tbindings) s  :
    (s, ⊤)::concat_tenvs Γ Δc Δd = concat_tenvs ((s,None)::Γ) Δc Δd.
  Proof.
    reflexivity.
  Qed.

  (* Move this to TNNRS *)
  Lemma nnrs_expr_type_lookup_on_equiv {Γc Γ₁ e τ} :
    ([ Γc ; Γ₁  ⊢ e ▷ τ ])%nnrs_scope ->
    forall Γ₂,
      lookup_equiv_on (nnrs_expr_free_vars e) Γ₁ Γ₂ ->
      ([ Γc ; Γ₂  ⊢ e ▷ τ ])%nnrs_scope.
  Proof.
    revert Γ₁ τ.
    induction e; intros Γ₁ τ typ Γ₂ leo
    ; invcs typ; simpl in *; subst; econstructor; eauto 3.
    - rewrite <- leo; simpl; tauto.
    - eapply IHe1; eauto.
      unfold lookup_equiv_on in *; intuition.
    - eapply IHe2; eauto.
      unfold lookup_equiv_on in *; intuition.
  Qed.

  Lemma nnrs_expr_to_nnrs_imp_expr_free_vars (e:nnrs_expr) :
    nnrs_imp_expr_free_vars (nnrs_expr_to_nnrs_imp_expr e) = nnrs_expr_free_vars e.
  Proof.
    induction e; simpl; congruence.
  Qed.

  Lemma nnrs_stmt_to_nnrs_imp_stmt_not_used_without_assignment s v:
    ~ In v (nnrs_stmt_free_env_vars s) ->
    ~ In v (nnrs_stmt_free_mcenv_vars s) ->
    nnrs_imp_stmt_var_usage (nnrs_stmt_to_nnrs_imp_stmt s) v <> VarMayBeUsedWithoutAssignment.
  Proof.
    nnrs_stmt_cases (induction s) Case
    ; simpl
    ; repeat rewrite in_app_iff
    ; intros nin1 nin2.
    - Case "NNRSSeq"%string.
      match_destr; intuition.
    - Case "NNRSLet"%string.
      match_case; intros eqq.
      + rewrite nnrs_imp_expr_may_use_free_vars in eqq.
        rewrite nnrs_expr_to_nnrs_imp_expr_free_vars in eqq.
        tauto.
      + unfold equiv_decb. destruct (v0 == v); try congruence.
        apply IHs; try tauto.
        rewrite remove_in_neq by eauto.
        tauto.
    - Case "NNRSLetMut"%string.
      unfold equiv_decb.
      destruct (v0 == v); try congruence.
      match_destr; try tauto.
      apply IHs2; try tauto.
      rewrite remove_in_neq by eauto.
      tauto.
    - Case "NNRSLetMutColl"%string.
      unfold equiv_decb.
      destruct (v0 == v); try congruence.
      match_destr; try tauto.
      + elim IHs1; try tauto.
        rewrite remove_in_neq by eauto.
        tauto.      
      + apply IHs2; try tauto.
        rewrite remove_in_neq by eauto.
        tauto.      
    - Case "NNRSAssign"%string.
      match_case; intros eqq.
      + rewrite nnrs_imp_expr_may_use_free_vars in eqq.
        rewrite nnrs_expr_to_nnrs_imp_expr_free_vars in eqq.
        tauto.
      + match_destr.
    - Case "NNRSPush"%string.
      unfold equiv_decb.
      destruct (v == v0); destruct (v0 == v); try congruence; simpl.
      + tauto.
      + match_case; intros eqq.
        rewrite nnrs_imp_expr_may_use_free_vars in eqq.
        rewrite nnrs_expr_to_nnrs_imp_expr_free_vars in eqq.
        tauto.
    - Case "NNRSFor"%string.
      match_case; intros eqq.
      + rewrite nnrs_imp_expr_may_use_free_vars in eqq.
        rewrite nnrs_expr_to_nnrs_imp_expr_free_vars in eqq.
        tauto.
      + unfold equiv_decb. destruct (v0 == v); try congruence.
        match_case; intros eqq2.
        elim IHs; try tauto.
        rewrite remove_in_neq by eauto.
        tauto.
    - Case "NNRSIf"%string.
      match_case; intros eqq.
      + rewrite nnrs_imp_expr_may_use_free_vars in eqq.
        rewrite nnrs_expr_to_nnrs_imp_expr_free_vars in eqq.
        tauto.
      + match_case; intros eqq2
        ; try (match_case; intros eqq3).
        * elim IHs2; try tauto.
        * elim IHs1; try tauto.
        * elim IHs2; try tauto.
    - Case "NNRSEither"%string.
      match_case; intros eqq.
      + rewrite nnrs_imp_expr_may_use_free_vars in eqq.
        rewrite nnrs_expr_to_nnrs_imp_expr_free_vars in eqq.
        tauto.
      + destruct (v0 == v).
        * destruct (v1 == v); try congruence.
          match_case; intros eqq2.
          elim IHs2; try tauto.
          rewrite remove_in_neq by eauto.
          tauto.
        * { match_case; intros eqq2.
            - destruct (v1 == v); try congruence.
              match_case; intros eqq3.
              elim IHs2; try tauto.
              rewrite remove_in_neq by eauto.
              tauto.
            - elim IHs1; try tauto.
              rewrite remove_in_neq by eauto.
              tauto.
            - destruct (v1 == v); try congruence.
              match_case; intros eqq3.
              elim IHs2; try tauto.
              rewrite remove_in_neq by eauto.
              tauto.
          }
  Qed.

  Lemma nnrs_imp_stmt_free_used s x :
    nnrs_imp_stmt_var_usage s x <> VarNotUsedAndNotAssigned ->
    In x (nnrs_imp_stmt_free_vars s).
  Proof.
    nnrs_imp_stmt_cases (induction s) Case
    ; simpl
    ; repeat rewrite in_app_iff
    ; try rewrite nnrs_imp_expr_may_use_free_vars
    ; try rewrite IHs
    ; try rewrite IHs1
    ; try rewrite IHs2.
    - Case "NNRSimpSeq"%string.
      match_case; intuition congruence.
    - Case "NNRSimpAssign"%string.
      match_case; try congruence
      ; try rewrite nnrs_imp_expr_may_use_free_vars
      ; try rewrite nnrs_imp_expr_may_use_free_vars_neg.
      + intuition congruence.
      + unfold equiv_decb; destruct (v == x); intuition congruence.
    - Case "NNRSimpLet"%string.
      destruct o.
      + (match_case; intros eqq)
        ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
        ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq.
        * intuition congruence.
        * { unfold equiv_decb; destruct (v == x); unfold equiv, complement in *.
            - subst.
              intuition.
            - intuition.
              right; apply remove_in_neq; intuition.
          }
      + simpl; intuition.
        unfold equiv_decb in *; destruct (v ==x); try intuition congruence.
        right.
        apply remove_in_neq; intuition.
    - Case "NNRSimpFor"%string.
      (match_case; intros eqq)
      ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
      ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq.
      + intuition congruence.
      +  unfold equiv_decb; destruct (v == x); unfold equiv, complement in *.
         * subst.
           intuition.
         * { match_case; intros eqq2; try congruence.
             rewrite <- remove_in_neq by eauto.
             right; apply IHs.
             intuition; try congruence.
           }
    - Case "NNRSimpIf"%string.
      (match_case; intros eqq)
      ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
      ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq.
      + intuition congruence.
      + match_case; intros eqq1
        ; try (match_case; intros eqq2)
        ; try intuition congruence.
    - Case "NNRSimpEither"%string.
      (match_case; intros eqq)
      ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
      ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq.
      + intuition congruence.
      + destruct (v == x).
        * { destruct (v0 == x)
            ; try intuition congruence.
            match_case; intros eqq1
            ; try (match_case; intros eqq2)
            ; try intuition congruence.
            right; right.
            rewrite <- remove_in_neq by eauto.
            apply IHs2; congruence.
          } 
        * { match_case; intros eqq1.
            -  destruct (v0 == x)
               ; try intuition congruence.
               match_case; intros eqq2
               ; try intuition congruence.
               + right; left.
                 rewrite <- remove_in_neq by eauto.
                 apply IHs1; congruence.
               + right; left.
                 rewrite <- remove_in_neq by eauto.
                 apply IHs1; congruence.
            -  right; left.
               rewrite <- remove_in_neq by eauto.
               apply IHs1; congruence.
            - destruct (v0 == x)
              ; try intuition congruence.
              match_case; intros eqq2
              ; try intuition congruence.
              + right; right.
                rewrite <- remove_in_neq by eauto.
                apply IHs2; congruence.
          }
  Qed.

  Lemma nnrs_stmt_to_nnrs_imp_stmt_must_assign_assigned {s dΓ dΔc dΔd} :
    nnrs_stmt_cross_shadow_free_under s dΓ dΔc dΔd ->
    forall v,
      In v (dΔd) ->
      nnrs_stmt_must_assign s v ->
      nnrs_imp_stmt_var_usage (nnrs_stmt_to_nnrs_imp_stmt s) v = VarMustBeAssigned.
  Proof.
    revert dΓ dΔc dΔd.
    nnrs_stmt_cases (induction s) Case
    ; simpl
    ; repeat rewrite in_app_iff
    ; intros dΓ dΔc dΔd cs vv inn ma.
    - Case "NNRSSeq"%string.
      specialize (IHs1 dΓ dΔc dΔd).
      specialize (IHs2 dΓ dΔc dΔd).
      (match_case; intro); intuition
      ; try solve[(eelim (nnrs_stmt_to_nnrs_imp_stmt_not_used_without_assignment)
                   ; [| | eauto]; eauto)]
      ; try congruence.
      + rewrite H3 in H; intuition.
      + eelim nnrs_stmt_to_nnrs_imp_stmt_not_used_without_assignment; [| | eauto]; eauto.
        * apply nnrs_stmt_cross_shadow_free_under_free_env_mdenv in H0.
          specialize (H0 vv); tauto.
        * apply nnrs_stmt_cross_shadow_free_under_free_mcenv_mdenv in H0.
          specialize (H0 vv); tauto.
      + rewrite H3 in H; congruence.
    - Case "NNRSLet"%string.
      match_case; intros eqq
      ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
      ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq
      ; try rewrite nnrs_expr_to_nnrs_imp_expr_free_vars in eqq
      ; intuition.
      + specialize (H1 vv); intuition.
      + unfold equiv_decb; destruct (v == vv); unfold equiv, complement in *
        ; subst
        ; intuition; eauto.
    - Case "NNRSLetMut"%string.
      unfold equiv_decb; destruct (v == vv); unfold equiv, complement in *
      ; subst
      ; intuition.
      + rewrite (IHs1 _ _ _  H2 vv); simpl; tauto.
      + match_case; intros eqq.
        * { eelim nnrs_stmt_to_nnrs_imp_stmt_not_used_without_assignment; [| | eauto]; eauto.
            - apply nnrs_stmt_cross_shadow_free_under_free_env_mdenv in H2.
              specialize (H2 vv); simpl in H2; tauto.
            - apply nnrs_stmt_cross_shadow_free_under_free_mcenv_mdenv in H2.
              specialize (H2 vv); simpl in H2; tauto.
          }
        * eauto.
    - Case "NNRSLetMutColl"%string.
      unfold equiv_decb; destruct (v == vv); unfold equiv, complement in *
      ; subst
      ; intuition.
      + rewrite (IHs1 _ _ _  H2 vv); simpl; tauto.
      + match_case; intros eqq.
        * { eelim nnrs_stmt_to_nnrs_imp_stmt_not_used_without_assignment; [| | eauto]; eauto.
            - apply nnrs_stmt_cross_shadow_free_under_free_env_mdenv in H2.
              specialize (H2 vv); simpl in H2; tauto.
            - apply nnrs_stmt_cross_shadow_free_under_free_mcenv_mdenv in H2.
              specialize (H2 vv); simpl in H2; tauto.
          }
        * eauto.        
    - Case "NNRSAssign"%string.
      subst.
      match_case; intros eqq.
      + rewrite nnrs_imp_expr_may_use_free_vars in eqq.
        rewrite nnrs_expr_to_nnrs_imp_expr_free_vars in eqq.
        subst; intuition.
        specialize (H1 vv); tauto.
      + unfold equiv_decb; destruct (vv == vv); try congruence.
    - Case "NNRSPush"%string.
      contradiction.
    - Case "NNRSFor"%string.
      match_case; intros eqq
      ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
      ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq
      ; try rewrite nnrs_expr_to_nnrs_imp_expr_free_vars in eqq
      ; intuition.
    - Case "NNRSIf"%string.
      match_case; intros eqq
      ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
      ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq
      ; try rewrite nnrs_expr_to_nnrs_imp_expr_free_vars in eqq
      ; intuition.
      + specialize (H3 vv); tauto.
      + rewrite (IHs1 _ _ _ H0); trivial.
        rewrite (IHs2 _ _ _ H5); trivial.
    - Case "NNRSEither"%string.
      match_case; intros eqq
      ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
      ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq
      ; try rewrite nnrs_expr_to_nnrs_imp_expr_free_vars in eqq
      ; intuition.
      + specialize (H3 vv); tauto.
      + specialize (IHs1 _ _ _ H7 _ inn H1).
        specialize (IHs2 _ _ _ H9 _ inn H2).
        rewrite IHs1, IHs2.
        destruct (v == vv); try congruence.
        destruct (v0 == vv); try congruence.
  Qed.

  Lemma concat_tenvs_lookup_equiv_env_mc_cons Γ Δc Δd v τ :
    ~ In v (domain Γ) ->
    lookup_equiv (concat_tenvs ((v,Some (Coll τ))::Γ) Δc Δd)
                 (concat_tenvs Γ ((v,τ)::Δc) Δd).
  Proof.
    unfold concat_tenvs, lookup_equiv.
    intros nin x.
    repeat rewrite lookup_app; simpl.
    destruct (string_eqdec x v); unfold equiv, complement in *.
    + subst. rewrite lookup_nin_none; trivial.
      unfold pd_tbindings_lift.
      rewrite domain_map_codomain; trivial.
    + trivial.
  Qed.

  Lemma concat_tenvs_lookup_equiv_mc_md  Γ Δc Δd v τ :
    ~ In v (domain Δc) ->
    lookup_equiv (concat_tenvs Γ ((v,τ)::Δc) Δd)
                 (concat_tenvs Γ Δc ((v,Coll τ)::Δd)).
  Proof.
    unfold concat_tenvs, lookup_equiv.
    intros nin x.
    repeat rewrite lookup_app.
    match_destr; simpl.
    destruct (string_eqdec x v); unfold equiv, complement in *.
    + subst.
      rewrite lookup_nin_none; trivial.
      rewrite domain_map_codomain; trivial.
    + match_destr.
  Qed.

  Lemma concat_tenvs_lookup_equiv_env_md Γ Δc Δd v τ :
    ~ In v (domain Γ) ->
    ~ In v (domain Δc) ->
    lookup_equiv (concat_tenvs ((v,τ)::Γ) Δc Δd)
                 (concat_tenvs Γ Δc ((v,lift_pdtype τ)::Δd)).
  Proof.
    intros nin1 nin2 x.
    unfold concat_tenvs, lookup_equiv.
    repeat rewrite lookup_app; simpl.
    destruct (string_eqdec x v); unfold equiv, complement in *.
    + subst.
      repeat rewrite lookup_nin_none; trivial
      ; unfold pd_tbindings_lift; rewrite domain_map_codomain; trivial.
    + trivial.
  Qed.
  
  Lemma nnrs_stmt_unused_tenv_free_env {Γc Γ Δc Δd s} :
    [ Γc ; Γ , Δc , Δd ⊢ s ]%nnrs_scope ->
    forall x, 
      lookup equiv_dec Γ x = Some None ->
      ~ In x (nnrs_stmt_free_env_vars s).
  Proof.
    revert Γ Δc Δd.
    nnrs_stmt_cases (induction s) Case
    ; simpl; intros Γ Δc Δd typ x eqq
    ; invcs typ
    ; repeat rewrite in_app_iff.
    - Case "NNRSSeq"%string.
      intuition eauto.
    - Case "NNRSLet"%string.
      intuition eauto.
      + eapply nnrs_expr_unused_tenv_free_env; eauto.
      + apply remove_inv in H0.
        intuition.
        eapply IHs; eauto; simpl.
        match_destr; congruence.
    - Case "NNRSLetMut"%string.
      intuition.
      + eapply IHs1; eauto.
      + apply remove_inv in H0; intuition.
        eapply IHs2; eauto.
        simpl; match_destr; congruence.
    - Case "NNRSLetMut"%string.
      intuition.
      + eapply IHs1; eauto.
      + apply remove_inv in H0; intuition.
        eapply IHs2; eauto.
        simpl; match_destr; congruence.
    - Case "NNRSLetMutColl"%string.
      intuition.
      + eapply IHs1; eauto.
      + apply remove_inv in H0; intuition.
        eapply IHs2; eauto.
        simpl; match_destr; congruence.
    - Case "NNRSAssign"%string.
      eapply nnrs_expr_unused_tenv_free_env; eauto.
    - Case "NNRSPush"%string.
      eapply nnrs_expr_unused_tenv_free_env; eauto.
    - Case "NNRSFor"%string.
      intuition eauto.
      + apply (nnrs_expr_unused_tenv_free_env H4) in eqq; tauto.
      + apply remove_inv in H0.
        intuition.
        eapply IHs; eauto; simpl.
        match_destr; congruence.
    - Case "NNRSIf"%string.
      intuition eauto.
      eapply nnrs_expr_unused_tenv_free_env; eauto.
    - Case "NNRSEither"%string.
      intuition eauto.
      + eapply nnrs_expr_unused_tenv_free_env; eauto.
      + apply remove_inv in H.
        intuition.
        eapply IHs1; eauto; simpl.
        match_destr; congruence.
      + apply remove_inv in H.
        intuition.
        eapply IHs2; eauto; simpl.
        match_destr; congruence.
  Qed.

  Lemma tnnrs_stmt_to_nnrs_imp_correct_f
        {Γc:tbindings} {Γ:TNNRS.pd_tbindings}
        (Δc:TNNRS.mc_tbindings) (Δd:TNNRS.md_tbindings) s :
    [ Γc ; Γ , Δc , Δd ⊢ s ]%nnrs_scope ->
    nnrs_stmt_cross_shadow_free_under s (domain Γ) (domain Δc) (domain Δd)->
    [ Γc ; concat_tenvs Γ Δc Δd ⊢  nnrs_stmt_to_nnrs_imp_stmt s ]%nnrs_imp_scope.
  Proof.

    Ltac prove_expr_f_t
         := match goal with
            | [H: [ _ ; _ ⊢ ?e ▷ _ ]%nnrs_scope |-
               [ _ ; _ ⊢ nnrs_expr_to_nnrs_imp_expr ?e ▷ _ ] %nnrs_imp_scope ] =>
              apply tnnrs_expr_to_nnrs_expr_correct_f in H
              ; apply (nnrs_imp_expr_type_lookup_on_equiv H)
              ; rewrite nnrs_expr_to_nnrs_imp_expr_free_vars
              ; unfold lookup_equiv_on; intros ? inn
              ; unfold concat_tenvs; repeat rewrite lookup_app
              ; match_destr
              ; repeat rewrite lookup_nin_none; trivial
              ; try rewrite domain_map_codomain; trivial
              ; match goal with
                | [H1:disjoint ?l1 ?l2,
                      H2: In ?x ?l1 |- ~ In ?x ?l2 ] =>
                  exact (H1 x inn)
                end
            end.
    
    Hint Constructors nnrs_imp_stmt_type.
    revert Γ Δc Δd.
    nnrs_stmt_cases (induction s) Case
    ; simpl; intros Γ Δc Δd typ sf
    ; invcs typ.
    - Case "NNRSSeq"%string.
      econstructor; intuition eauto.
    - Case "NNRSLet"%string.
      destruct sf as [disj1 [disj2 [nin1 [nin2 sf]]]].
      econstructor.
      + prove_expr_f_t.
      + specialize (IHs ((v, Some τ) :: Γ)); unfold concat_tenvs in *.
        simpl in IHs; eauto.
    - Case "NNRSLetMut"%string.
      destruct sf as [ninΓ [ninΔc [ninΔd [sf1 sf2]]]].
      apply (nnrs_stmt_to_nnrs_imp_stmt_must_assign_assigned sf1) in H5
      ; simpl; try tauto.
      eapply (type_NNRSimpLetNone _ _ τ); simpl.
      + rewrite H5; congruence.
      + specialize (IHs1 _ _ _ H6 sf1).
        specialize (IHs2 _ _ _ H7 sf2).
        econstructor.
        * eapply nnrs_imp_stmt_type_lookup_equiv_prop; eauto.
          rewrite concat_tenvs_cons_some.
          apply concat_tenvs_lookup_equiv_env_md; eauto.
        * eauto.
    - Case "NNRSLetMut"%string.
      destruct sf as [ninΓ [ninΔc [ninΔd [sf1 sf2]]]].
      eapply (type_NNRSimpLetNone _ _ ⊤); simpl.
      + match_case; intros eqq; try congruence.
        * { apply nnrs_stmt_to_nnrs_imp_stmt_not_used_without_assignment in eqq.
            - contradiction.
            - apply nnrs_stmt_cross_shadow_free_under_free_env_mdenv in sf1.
              specialize (sf1 v); simpl in sf1; tauto.
            - apply nnrs_stmt_cross_shadow_free_under_free_mcenv_mdenv in sf1.
              specialize (sf1 v); simpl in sf1; tauto.
          }
        * { apply nnrs_stmt_to_nnrs_imp_stmt_not_used_without_assignment.
            - apply (nnrs_stmt_unused_tenv_free_env H6 v); simpl.
              match_destr; try congruence.
            - apply nnrs_stmt_cross_shadow_free_under_free_mcenv_env in sf2.
              eapply disjoint_cons_inv2 in sf2; tauto.
          }
      + rewrite concat_tenvs_cons_none.
        econstructor; eauto.
        eapply nnrs_imp_stmt_type_lookup_equiv_prop; eauto.
        apply concat_tenvs_lookup_equiv_env_md; eauto.
    - Case "NNRSLetMutColl"%string.
      destruct sf as [ninΓ [ninΔc [ninΔd [sf1 sf2]]]].
      eapply (type_NNRSimpLetDef _ _ (Coll τ)); simpl.
      + repeat (econstructor; simpl).
      + rewrite concat_tenvs_cons_some.
        econstructor; eauto.
        eapply nnrs_imp_stmt_type_lookup_equiv_prop; eauto.
        apply concat_tenvs_lookup_equiv_env_mc_cons; eauto.
    - Case "NNRSAssign"%string.
      destruct sf as [disjc [disjd [ninΓ ninΔc]]].
      econstructor; eauto.
      + prove_expr_f_t. 
      + unfold concat_tenvs; repeat rewrite lookup_app.
        rewrite H5.
        repeat rewrite lookup_nin_none; trivial
        ; unfold pd_tbindings_lift
        ; try rewrite domain_map_codomain; trivial.
      + reflexivity.
    - Case "NNRSPush"%string.
      destruct sf as [disjc [disjd [ninΓ ninΔc]]].
      assert (lo:lookup equiv_dec (concat_tenvs Γ Δc Δd) v = Some (Coll τ)).
      {
        unfold concat_tenvs; repeat rewrite lookup_app.
        rewrite lookup_map_codomain.
        unfold equiv_dec, string_eqdec.
        rewrite H5.
        repeat rewrite lookup_nin_none; trivial
        ; unfold pd_tbindings_lift
        ; try rewrite domain_map_codomain; trivial.
      } 
      econstructor; eauto; [| eapply SColl; eauto; reflexivity].
      econstructor; eauto; [econstructor | ].
      econstructor; [econstructor | ].
      prove_expr_f_t.
    - Case "NNRSFor"%string.
      destruct sf as [disjc [disjd [ninΔc [ninΔd sf]]]].
      econstructor.
      + prove_expr_f_t.
      + specialize (IHs ((v, Some τ) :: Γ)); unfold concat_tenvs in *.
         simpl in IHs; eauto.
    - Case "NNRSIf"%string.
      destruct sf as [disjc [disjd [sf1 sf2]]].
      econstructor; eauto.
      prove_expr_f_t.
    - Case "NNRSEither"%string.
      destruct sf as [disjc [disjd [nin1Δc [nin1Δd [nin2Δc [nin2Δd [sf1 sf2]]]]]]].
      econstructor.
      + prove_expr_f_t.
      + specialize (IHs1 ((v, Some τl) :: Γ)); unfold concat_tenvs in *.
         simpl in IHs1; eauto.
      + specialize (IHs2 ((v0, Some τr) :: Γ)); unfold concat_tenvs in *.
         simpl in IHs2; eauto.
  Qed.

  Theorem tnnrs_to_nnrs_imp_correct_f {Γc} {si:nnrs} {τ} :
    [ Γc ⊢ si ▷ τ ]%nnrs_scope ->
    nnrs_cross_shadow_free si ->
    [ Γc ⊢ nnrs_to_nnrs_imp si ▷ τ ]%nnrs_imp_scope.
  Proof.
    destruct si; simpl.
    intros typ sf.
    apply tnnrs_stmt_to_nnrs_imp_correct_f in typ; eauto.
    split.
    - unfold nnrs_cross_shadow_free in sf; simpl in sf.
      apply nnrs_stmt_to_nnrs_imp_stmt_not_used_without_assignment.
      + apply nnrs_stmt_cross_shadow_free_under_free_env_mdenv in sf.
         apply disjoint_cons_inv2 in sf; tauto.
      + apply nnrs_stmt_cross_shadow_free_under_free_mcenv_mdenv in sf.
        apply disjoint_cons_inv2 in sf; tauto.
    - unfold concat_tenvs in typ; simpl in typ; trivial.
  Qed.
  
  Theorem tnnrs_to_nnrs_imp_top_correct_f {Γc} {si:nnrs} {τ} :
    [ Γc ⊢ si ▷ τ ]%nnrs_scope ->
    forall sep,
      [ Γc ⊢ nnrs_to_nnrs_imp_top sep si ▷ τ ]%nnrs_imp_scope.
  Proof.
    intros typ sep.
    apply tnnrs_to_nnrs_imp_correct_f.
    - apply nnrs_uncross_shadow_type; trivial.
    - apply nnrs_uncross_shadow_free.
  Qed.

  Lemma nnrs_stmt_to_nnrs_imp_stmt_assigned_must_assign {s v} :
    nnrs_imp_stmt_var_usage (nnrs_stmt_to_nnrs_imp_stmt s) v = VarMustBeAssigned ->
    nnrs_stmt_must_assign s v.
  Proof.
    nnrs_stmt_cases (induction s) Case
    ; simpl; intros eqq
    ; try solve [repeat match_destr_in eqq; try tauto].
    - Case "NNRSLetMut"%string.
      unfold equiv_decb in *.
      destruct (v0 == v); try discriminate.
      match_destr_in eqq; tauto.
    - Case "NNRSAssign"%string.
      unfold equiv_decb in *.
      destruct (v0 == v); try discriminate.
      match_destr_in eqq; tauto.
      match_destr_in eqq; tauto.
    - Case "NNRSPush"%string.
      unfold equiv_decb in eqq.
      destruct (v0 == v)
      ; destruct (v == v0)
      ; simpl in eqq
      ; try congruence.
      match_destr_in eqq.
  Qed.
    
  Section core.

    Program Theorem tnnrs_core_to_nnrs_imp_core_top_correct_f {Γc} {si:nnrs_core} {τ} :
      [ Γc ⊢ si ▷ τ ]%nnrs_scope ->
      forall sep,
        [ Γc ⊢ nnrs_core_to_nnrs_imp_core_top sep si ▷ τ ]%nnrs_imp_scope.
    Proof.
      intros typ sep.
      apply tnnrs_to_nnrs_imp_top_correct_f; trivial.
    Qed.
      
  End core.

End TNNRStoNNRSimp.
