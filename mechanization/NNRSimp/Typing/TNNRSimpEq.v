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

Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import List.
Require Import String.
Require Import Utils.
Require Import CommonSystem.
Require Import NNRSimp.
Require Import NNRSimpNorm.
Require Import NNRSimpVars.
Require Import NNRSimpUsage.
Require Import NNRSimpEval.
Require Import NNRSimpEq.
Require Import TNNRSimp.

Section TNNRSimpEq.
  Local Open Scope nnrs_imp.

  Context {m:basic_model}.

  Definition tnnrs_imp_expr_rewrites_to (e₁ e₂:nnrs_imp_expr) : Prop :=
    forall (Γc:tbindings) (Γ : pd_tbindings) (τ:rtype),
      [ Γc ; Γ  ⊢ e₁ ▷ τ ] ->
      [ Γc ; Γ  ⊢ e₂ ▷ τ ] 
      /\ (forall (σc:bindings),
             bindings_type σc Γc ->
             forall (σ:pd_bindings),
               pd_bindings_type σ Γ ->
               has_some_parts (nnrs_imp_expr_free_vars e₁) σ ->
               nnrs_imp_expr_eval brand_relation_brands  σc σ e₁
               = nnrs_imp_expr_eval brand_relation_brands  σc σ e₂).


  Definition tnnrs_imp_stmt_rewrites_to (s₁ s₂:nnrs_imp_stmt) : Prop :=
    forall (Γc:tbindings) (Γ : pd_tbindings) ,
      [ Γc ; Γ  ⊢ s₁ ] ->
      [ Γc ; Γ  ⊢ s₂ ] 
      /\ (forall (σc:bindings),
             bindings_type σc Γc ->
             forall (σ:pd_bindings),
               pd_bindings_type σ Γ ->
               forall alreadydefined,
                 has_some_parts alreadydefined σ ->
                 (forall x, nnrs_imp_stmt_var_usage s₁ x = VarMayBeUsedWithoutAssignment ->
                            In x alreadydefined) ->
                 nnrs_imp_stmt_eval brand_relation_brands  σc s₁ σ
                 = nnrs_imp_stmt_eval brand_relation_brands  σc s₂ σ)
      /\ (stmt_var_usage_sub s₁ s₂).

  Definition tnnrs_imp_rewrites_to (si₁ si₂:nnrs_imp) : Prop :=
    forall (Γc:tbindings) (τ:rtype) ,
      [ Γc ⊢ si₁ ▷ τ  ] ->
      [ Γc ⊢ si₂ ▷ τ  ] 
      /\ (forall (σc:bindings),
             bindings_type σc Γc ->
             nnrs_imp_eval brand_relation_brands  σc si₁
             = nnrs_imp_eval brand_relation_brands  σc si₂).

  Notation "e1 ⇒ᵉ e2" := (tnnrs_imp_expr_rewrites_to e1 e2) (at level 80) : nnrs_imp.
  Notation "s1 ⇒ˢ s2" := (tnnrs_imp_stmt_rewrites_to s1 s2) (at level 80) : nnrs_imp.
  Notation "si1 ⇒ˢⁱ si2" := (tnnrs_imp_rewrites_to si1 si2) (at level 80) : nnrs_imp.

  (* They are all preorders *)
  Global Instance tnnrs_imp_expr_rewrites_to_pre : PreOrder tnnrs_imp_expr_rewrites_to.
  Proof.
    unfold tnnrs_imp_expr_rewrites_to.
    constructor; red.
    - intuition.
    - intros x y z Hx Hy; intros ? ? ? typx.
      destruct (Hx Γc Γ τ typx) as [typy Hx'].
      specialize (Hy Γc Γ τ typy).
      destruct Hy as [typz Hy].
      split; trivial.
      intros.
      rewrite (Hx' _ H _ H0 H1).
      apply (Hy _ H _ H0).
      rewrite nnrs_imp_expr_type_impl_free_vars_incl; eauto.
      intros ? typ.
      destruct (Hx _ _ _ typ); trivial.
  Qed.

  Global Instance tnnrs_imp_stmt_rewrites_to_pre : PreOrder tnnrs_imp_stmt_rewrites_to.
  Proof.
    unfold tnnrs_imp_stmt_rewrites_to.
    constructor; red.
    - intuition.
    - intros x y z Hx Hy; intros ? ? typx.
      destruct (Hx _ _ typx) as [typy [Hx' subxy]].
      specialize (Hy _ _ typy).
      destruct Hy as [typz [Hy subyz]].
      split; trivial.
      split; [ | etransitivity; eauto].
      intros.
      erewrite Hx'; eauto.
      erewrite Hy; eauto.
      intros.
      apply H2.
      eapply stmt_var_usage_sub_to_maybe_used; eauto.
  Qed.
  
  Global Instance tnnrs_imp_rewrites_to_pre : PreOrder tnnrs_imp_rewrites_to.
  Proof.
    unfold tnnrs_imp_rewrites_to.
    constructor; red.
    - intuition.
    - intros x y z Hx Hy; intros ? ? typx.
      specialize (Hx _ _ typx).
      destruct Hx as [typy Hx].
      specialize (Hy _ _ typy).
      destruct Hy as [typz Hy].
      split; trivial; intros.
      rewrite Hx, Hy; trivial.
  Qed.

  (* An untyped equivalence + type preservation -> typed rewrite *)
  Lemma nnrs_imp_expr_eq_rewrites_to (e₁ e₂:nnrs_imp_expr) :
    e₁ ≡ᵉ e₂ ->
    (forall {Γc:tbindings} {Γ:tbindings} {τ:rtype},
        [ Γc ; Γ  ⊢ e₁ ▷ τ ] ->
        [ Γc ; Γ  ⊢ e₂ ▷ τ ]) ->
    e₁ ⇒ᵉ e₂.
  Proof.
    red; intros eqq; intros; split; eauto; intros ??? typ2 ?.
    apply eqq.
    - apply Forall_map.
      eapply bindings_type_Forall_normalized; eauto.
    - intros ? inn.
      eapply pd_bindings_type_in_normalized in typ2; eauto.
  Qed.
  
  Lemma nnrs_imp_stmt_eq_rewrites_to (s₁ s₂:nnrs_imp_stmt) :
    s₁ ≡ˢ s₂ ->
    stmt_var_usage_sub s₁ s₂ ->
    (forall {Γc:tbindings} {Γ:tbindings},
        [ Γc ; Γ ⊢ s₁ ] ->
        [ Γc ; Γ ⊢ s₂ ]) ->
    s₁ ⇒ˢ s₂.
  Proof.
    red; intros eqq; intros; split; eauto.
    split; trivial.
    intros.
    apply eqq.
    - apply Forall_map.
      eapply bindings_type_Forall_normalized; eauto.
    -  intros ? inn.
       eapply pd_bindings_type_in_normalized; eauto.
  Qed.
  
  Lemma nnrs_imp_eq_rewrites_to (si₁ si₂:nnrs_imp) :
    si₁ ≡ˢⁱ si₂ ->
    (forall {Γc:tbindings} {τ:rtype},
        [ Γc ⊢ si₁ ▷ τ  ] ->
        [ Γc ⊢ si₂ ▷ τ  ]) ->
    si₁ ⇒ˢⁱ si₂.
  Proof.
    red; intros eqq; intros; split; eauto; intros.
    apply eqq.
    apply Forall_map.
    eapply bindings_type_Forall_normalized; eauto.
  Qed.

  Lemma tnnrs_imp_expr_rewrites_to_free_vars_incl {Γc Γ e τ} :
      [Γc; Γ ⊢ e ▷ τ] ->
      forall {e'},
        e ⇒ᵉ e' ->
        incl (nnrs_imp_expr_free_vars e') (nnrs_imp_expr_free_vars e).
    Proof.
      intros.
      eapply nnrs_imp_expr_type_impl_free_vars_incl; eauto.
      intros.
      apply H0; trivial.
    Qed.
    
  Section proper.

    Global Instance NNRSimpGetConstant_tproper v :
      Proper tnnrs_imp_expr_rewrites_to (NNRSimpGetConstant v).
    Proof.
      unfold Proper, respectful, tnnrs_imp_expr_rewrites_to; intuition.
    Qed.

    Global Instance NNRSimpVar_tproper v :
      Proper tnnrs_imp_expr_rewrites_to (NNRSimpVar v).
    Proof.
      unfold Proper, respectful, tnnrs_imp_expr_rewrites_to; intuition.
    Qed.

    Global Instance NNRSimpConst_tproper d :
      Proper tnnrs_imp_expr_rewrites_to (NNRSimpConst d).
    Proof.
      unfold Proper, respectful, tnnrs_imp_expr_rewrites_to; intuition.
    Qed.

    Global Instance NNRSimpBinop_tproper :
      Proper (tbinary_op_rewrites_to ==> tnnrs_imp_expr_rewrites_to ==> tnnrs_imp_expr_rewrites_to ==> tnnrs_imp_expr_rewrites_to) NNRSimpBinop.
    Proof.
      unfold Proper, respectful, tnnrs_imp_expr_rewrites_to.
      intros op op' eqop e1 e1' He1 e2 e2' He2 Γc Γ τ typ.
      invcs typ.
      specialize (He1 _ _ _ H5).
      destruct He1 as [typ1 He1].
      specialize (He2 _ _ _ H6).
      destruct He2 as [typ2 He2].
      destruct (eqop _ _ _ H3) as [typop Hop].
      split; [econstructor; eauto | ].
      simpl; intros.
      apply has_some_parts_app in H1.
      rewrite He1, He2 by tauto.
      apply olift2_ext; intros.
      apply Hop.
      - eapply nnrs_imp_expr_eval_preserves_types; eauto.
        rewrite He1; tauto.
      - eapply nnrs_imp_expr_eval_preserves_types; eauto.
        rewrite He2; tauto.
    Qed.

    Global Instance NNRSimpUnop_tproper :
      Proper (tunary_op_rewrites_to ==> tnnrs_imp_expr_rewrites_to ==> tnnrs_imp_expr_rewrites_to) NNRSimpUnop.
    Proof.
      unfold Proper, respectful, tnnrs_imp_expr_rewrites_to; simpl.
      intros op op' eqop e1 e1' He1 Γc Γ τ typ.
      invcs typ.
      specialize (He1 _ _ _ H4).
      destruct He1 as [typ1 He1].
      destruct (eqop _ _ H2) as [typop Hop].
      split; [econstructor; eauto | ].
      simpl; intros.
      rewrite He1 by trivial.
      apply olift_ext; intros.
      apply Hop.
      eapply nnrs_imp_expr_eval_preserves_types; eauto.
      rewrite He1; trivial.
    Qed.

    Global Instance NNRSimpGroupBy_tproper s ls :
      Proper (tnnrs_imp_expr_rewrites_to ==> tnnrs_imp_expr_rewrites_to) (NNRSimpGroupBy s ls).
    Proof.
      unfold Proper, respectful, tnnrs_imp_expr_rewrites_to; simpl.
      intros e1 e1' He1 Γc Γ τ typ.
      invcs typ.
      specialize (He1 _ _ _ H5).
      destruct He1 as [typ1 He1].
      split; [econstructor; eauto | ].
      intros.
      rewrite He1; trivial.
    Qed.

    Global Instance NNRSimpSeq_tproper :
      Proper (tnnrs_imp_stmt_rewrites_to ==> tnnrs_imp_stmt_rewrites_to ==> tnnrs_imp_stmt_rewrites_to) NNRSimpSeq.
    Proof.
      unfold Proper, respectful, tnnrs_imp_stmt_rewrites_to; simpl.
      intros s1 s1' Hs1 s2 s2' Hs2 Γc Γ typ.
      invcs typ.
      destruct (Hs1 _ _ H2)
        as [typ1 [Hs1' subs1]].
      specialize (Hs2 _ _ H3).
      destruct Hs2 as [typ2 [Hs2 subs2]].
      split; [econstructor; eauto | ].
      split.
      - intros σc σc_bt σ σ_bt alreadydefined hasp inn.
        erewrite Hs1'; eauto.
        + apply olift_ext; intros σ' eqq1.
          generalize (nnrs_imp_stmt_eval_preserves_types _ σc_bt σ_bt typ1 _ eqq1)
          ; intros σ'_bt.
          eapply (Hs2 _ σc_bt _ σ'_bt
                      (alreadydefined ++
                      filter (fun x =>
                                nnrs_imp_stmt_var_usage s1' x ==b VarMustBeAssigned)
                      (nnrs_imp_stmt_free_vars s1))).
          * rewrite has_some_parts_app.
            { split.
              - eapply nnrs_imp_stmt_preserves_has_some_parts; eauto.
              - eapply nnrs_imp_stmt_assigns_has_some_parts; eauto.
            }             
          * intros ? eqq2.
            specialize (inn x).
            rewrite in_app_iff, filter_In.
            rewrite eqq2 in inn.
            match_case_in inn
            ; intros eqq3; rewrite eqq3 in inn
            ; try tauto.
            right.
            specialize (subs1 x).
            rewrite eqq3 in subs1.
            simpl in subs1.
            match_case_in subs1
            ; intros eqq4; rewrite eqq4 in subs1
            ; try contradiction.
            split; [ | reflexivity ].
            apply nnrs_imp_stmt_free_used.
            congruence.
        + intros ? eqq1; apply inn; rewrite eqq1; trivial.
      - rewrite subs1, subs2; reflexivity.
    Qed.

    Global Instance NNRSimpAssign_tproper v :
      Proper (tnnrs_imp_expr_rewrites_to ==> tnnrs_imp_stmt_rewrites_to) (NNRSimpAssign v).
    Proof.
      unfold Proper, respectful, tnnrs_imp_stmt_rewrites_to; simpl.
      intros e1 e1' He1 Γc Γ typ.
      invcs typ.
      generalize (tnnrs_imp_expr_rewrites_to_free_vars_incl H2 He1)
      ; intros inclfv.
      apply He1 in H2.
      destruct H2 as [typ1 He1'].
      split; [econstructor; eauto | ].
      split.
      - intros; rewrite He1'; trivial.
        eapply has_some_parts_incl_proper; try eapply H1; try reflexivity.
        intros x inn.
        specialize (H2 x).
        apply nnrs_imp_expr_may_use_free_vars in inn.
        rewrite inn in H2.
        auto.
      - apply stmt_var_usage_sub_assign_proper; trivial.
    Qed.

    Lemma NNRSimpLet_some_tproper v : 
      forall (e₁ e₂: nnrs_imp_expr),
        e₁ ⇒ᵉ e₂ ->
        forall (s₁ s₂:nnrs_imp_stmt),
          s₁ ⇒ˢ s₂ ->
          NNRSimpLet v (Some e₁) s₁ ⇒ˢ NNRSimpLet v (Some e₂) s₂.
    Proof.
      intros e1 e1' He1 s2 s2' Hs2 Γc Γ typ.
      invcs typ.
      generalize (tnnrs_imp_expr_rewrites_to_free_vars_incl H2 He1)
      ; intros inclfv.
      apply He1 in H2.
      destruct H2 as [typ1 He1'].
      specialize (Hs2 _ _ H4).
      destruct Hs2 as [typ2 Hs2].
      edestruct Hs2; eauto.
      split; [econstructor; eauto | ].
      split.
      - simpl; intros.
        rewrite He1'; eauto.
        + apply olift_ext; intros.
          apply some_lift in H6.
          destruct H6 as [? eqq1 ?]; subst.
          rewrite H with (alreadydefined:=v::alreadydefined); eauto.
          * simpl.
            econstructor; eauto.
            simpl; split; trivial; intros ? eqq2; subst.
            invcs eqq2.
            eapply nnrs_imp_expr_eval_preserves_types; eauto.
          * apply has_some_parts_cons_some; trivial.
          * simpl; intros a eqq3.
            specialize (H5 a).
            match_destr_in H5; [eauto | ].
            unfold equiv_decb in *.
            destruct (v == a); eauto.
        + eapply has_some_parts_incl_proper; try eapply H3; try reflexivity.
          intros a inn; apply H5.
          apply nnrs_imp_expr_may_use_free_vars in inn.
          rewrite inn; trivial.
      - apply stmt_var_usage_sub_let_some_proper; trivial. 
    Qed.

    Lemma NNRSimpLet_none_tproper v : 
      forall (s₁ s₂:nnrs_imp_stmt),
        s₁ ⇒ˢ s₂ ->
        (nnrs_imp_stmt_var_usage s₁ v <> VarMayBeUsedWithoutAssignment ->
        nnrs_imp_stmt_var_usage s₂ v <> VarMayBeUsedWithoutAssignment) ->
        NNRSimpLet v None s₁ ⇒ˢ NNRSimpLet v None s₂.
    Proof.
      intros s2 s2' Hs2 Γc Γ vu typ.
      invcs typ.
      specialize (Hs2 _ _ H3).
      destruct Hs2 as [typ2 Hs2].
      split; [econstructor; eauto | ].
      edestruct Hs2; eauto.
      split.
      - simpl; intros.
        rewrite H with (alreadydefined:=remove equiv_dec v alreadydefined); eauto.
        + constructor; simpl; trivial.
          split; trivial.
          intros ? eqq2; invcs eqq2.
        + apply has_some_parts_cons_none; trivial.
        + simpl; intros a eqq3.
          specialize (H6 a).
          unfold equiv_decb in *.
          destruct (v == a).
          * congruence.
          * apply remove_in_neq; eauto.
      - apply stmt_var_usage_sub_let_none_proper; trivial. 
    Qed.
    
    Global Instance NNRSimpFor_tproper v :
      Proper (tnnrs_imp_expr_rewrites_to ==> tnnrs_imp_stmt_rewrites_to ==> tnnrs_imp_stmt_rewrites_to) (NNRSimpFor v).
    Proof.
      unfold Proper, respectful, tnnrs_imp_stmt_rewrites_to; simpl.
      intros e1 e1' He1 s2 s2' Hs2 Γc Γ typ.
      invcs typ.
      generalize (tnnrs_imp_expr_rewrites_to_free_vars_incl H2 He1)
      ; intros inclfv.
      apply He1 in H2.
      destruct H2 as [typ1 He1'].
      specialize (Hs2 _ _ H4).
      destruct Hs2 as [typ2 [Hs2 sub2]].
      split; [econstructor; eauto | ].
      split.
      - simpl; intros.
        erewrite He1'; eauto.
        + apply olift_ext; intros.
          destruct a; trivial.
          eapply nnrs_imp_expr_eval_preserves_types in H3; eauto.
          invcs H3; rtype_equalizer; subst.
          revert σ H0 H1.
          induction l; simpl; trivial.
          intros σ bt hsp.
          invcs H7.
          rewrite Hs2 with (alreadydefined:=v::alreadydefined); eauto.
          * match_option.
            destruct p; trivial.
            { eapply IHl; eauto.
              - eapply nnrs_imp_stmt_eval_preserves_types in eqq; eauto.
                + invcs eqq; trivial.
                + econstructor; simpl; eauto.
                  split; trivial; intros ? eqq2; invcs eqq2; trivial.
              - apply (nnrs_imp_stmt_preserves_has_some_parts_skip alreadydefined _ _
                                                                   ((v, Some a)::nil) _ (p::nil) _ eqq)
                ; trivial.
                destruct p; simpl.
                f_equal.
                apply nnrs_imp_stmt_eval_domain_stack in eqq; simpl in eqq.
                congruence.
            } 
          * econstructor; simpl; eauto.
            split; trivial; intros ? eqq2; invcs eqq2; trivial.
          * apply has_some_parts_cons_some; trivial.
          * intros aa eqq1.
            simpl.
            specialize (H2 aa).
            unfold equiv_decb in *.
            rewrite eqq1 in H2.
            destruct (v == aa); [eauto | ].
            match_destr_in H2; eauto.
        + eapply has_some_parts_incl_proper; try eapply H1; try reflexivity.
          intros a inn; apply H2.
          apply nnrs_imp_expr_may_use_free_vars in inn.
          rewrite inn; trivial.
      - apply stmt_var_usage_sub_for_proper; trivial. 
    Qed.
    
    Global Instance NNRSimpIf_tproper :
      Proper (tnnrs_imp_expr_rewrites_to ==> tnnrs_imp_stmt_rewrites_to ==> tnnrs_imp_stmt_rewrites_to ==> tnnrs_imp_stmt_rewrites_to) NNRSimpIf.
    Proof.
      unfold Proper, respectful, tnnrs_imp_stmt_rewrites_to; simpl.
      intros e1 e1' He1 s1 s1' Hs1 s2 s2' Hs2 Γc Γ typ.
      invcs typ.
      generalize (tnnrs_imp_expr_rewrites_to_free_vars_incl H3 He1)
      ; intros inclfv.
      apply He1 in H3.
      destruct H3 as [type He1'].
      specialize (Hs1 _ _ H4).
      destruct Hs1 as [typ1 [Hs1 sub1]].
      specialize (Hs2 _ _ H5).
      destruct Hs2 as [typ2 [Hs2 sub2]].
      split; [econstructor; eauto | ].
      split.
      - intros.
        rewrite He1'; eauto.
        + match_option.
          destruct d; trivial.
          destruct b; trivial.
          * eapply Hs1; eauto.
            intros ? eqq1; apply H2; rewrite eqq1.
            match_destr.
          * eapply Hs2; eauto.
            intros ? eqq1; apply H2; rewrite eqq1.
            repeat match_destr.
        + eapply has_some_parts_incl_proper; try eapply H1; try reflexivity.
          intros a inn; apply H2.
          apply nnrs_imp_expr_may_use_free_vars in inn.
          rewrite inn; trivial.
      - apply stmt_var_usage_sub_if_proper; trivial. 
    Qed.

    Global Instance NNRSimpEither_tproper :
      Proper (tnnrs_imp_expr_rewrites_to ==> eq ==> tnnrs_imp_stmt_rewrites_to ==> eq ==> tnnrs_imp_stmt_rewrites_to ==> tnnrs_imp_stmt_rewrites_to) NNRSimpEither.
    Proof.
      unfold Proper, respectful, tnnrs_imp_stmt_rewrites_to; simpl.
      intros e1 e1' He1 ? ? ? s1 s1' Hs1 ? ? ? s2 s2' Hs2 Γc Γ typ.
      subst.
      invcs typ.
      generalize (tnnrs_imp_expr_rewrites_to_free_vars_incl H3 He1)
      ; intros inclfv.
      apply He1 in H3.
      destruct H3 as [type He1'].
      specialize (Hs1 _ _ H6).
      destruct Hs1 as [typ1 [Hs1 sub1]].
      specialize (Hs2 _ _ H7).
      destruct Hs2 as [typ2 [Hs2 sub2]].
      split; [econstructor; eauto | ].
      split.
      - intros.
        rewrite He1'; eauto.
        + match_option.
          eapply nnrs_imp_expr_eval_preserves_types in eqq; eauto.
          invcs eqq; rtype_equalizer; subst.
          * { rewrite Hs1 with (alreadydefined:=y::alreadydefined); eauto.
              - constructor; trivial.
                simpl; split; trivial.
                intros ? eqq1; invcs eqq1; trivial.
              - apply has_some_parts_cons_some; trivial.
              - intros aa eqq1.
                simpl.
                specialize (H2 aa).
                unfold equiv_decb in *.
                rewrite eqq1 in H2.
                destruct (y == aa); [eauto | ].
                match_destr_in H2; eauto.
            }
          * { rewrite Hs2 with (alreadydefined:=y0::alreadydefined); eauto.
              - constructor; trivial.
                simpl; split; trivial.
                intros ? eqq1; invcs eqq1; trivial.
              - apply has_some_parts_cons_some; trivial.
              - intros aa eqq1.
                simpl.
                specialize (H2 aa).
                unfold equiv_decb in *.
                rewrite eqq1 in H2.
                destruct (y0 == aa); [eauto | ].
                repeat (match_destr_in H2; eauto).
            } 
        + eapply has_some_parts_incl_proper; try eapply H1; try reflexivity.
          intros a inn; apply H2.
          apply nnrs_imp_expr_may_use_free_vars in inn.
          rewrite inn; trivial.
      - apply stmt_var_usage_sub_either_proper; trivial. 
    Qed.

    Lemma NNRSImp_tproper {s₁ s₂} : tnnrs_imp_stmt_rewrites_to s₁ s₂ ->
                                    forall v,
                                      (nnrs_imp_stmt_var_usage s₁ v <> VarMayBeUsedWithoutAssignment ->
                                       nnrs_imp_stmt_var_usage s₂ v <> VarMayBeUsedWithoutAssignment) ->
                                   tnnrs_imp_rewrites_to (s₁, v) (s₂, v).
    Proof.
      unfold tnnrs_imp_rewrites_to; intros eqq v neimpl Γc τ [ne typ].
      generalize (typed_nnrs_imp_stmt_vars_in_ctxt typ)
      ; simpl; intros inn.
      eapply eqq in typ.
      destruct typ as [typ [IHs sub1]].
      split.
      - split; eauto.
      - intros; simpl.
        rewrite IHs with (alreadydefined:=nil); simpl; eauto.
        + repeat econstructor; simpl.
          intros ? eqq1; invcs eqq1.
        + econstructor.
        + intros ? eqq1.
          destruct (inn x); congruence.
    Qed.
    
  End proper.

End TNNRSimpEq.

Notation "e1 ⇒ᵉ e2" := (tnnrs_imp_expr_rewrites_to e1 e2) (at level 80) : nnrs_imp.
Notation "s1 ⇒ˢ s2" := (tnnrs_imp_stmt_rewrites_to s1 s2) (at level 80) : nnrs_imp.
Notation "si1 ⇒ˢⁱ si2" := (tnnrs_imp_rewrites_to si1 si2) (at level 80) : nnrs_imp.

