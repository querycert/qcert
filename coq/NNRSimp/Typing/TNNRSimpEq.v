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
               nnrs_imp_stmt_eval brand_relation_brands  σc s₁ σ
               = nnrs_imp_stmt_eval brand_relation_brands  σc s₂ σ).

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
      specialize (Hx _ _ _ typx).
      destruct Hx as [typy Hx].
      specialize (Hy _ _ _ typy).
      destruct Hy as [typz Hy].
      split; trivial; intros.
      rewrite Hx, Hy; trivial.
  Qed.

  Global Instance tnnrs_imp_stmt_rewrites_to_pre : PreOrder tnnrs_imp_stmt_rewrites_to.
  Proof.
    unfold tnnrs_imp_stmt_rewrites_to.
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
    red; intros eqq; intros; split; eauto; intros ??? typ2.
    apply eqq.
    - apply Forall_map.
      eapply bindings_type_Forall_normalized; eauto.
    - intros ? inn.
      eapply pd_bindings_type_in_normalized in typ2; eauto.
  Qed.
  
  Lemma nnrs_imp_stmt_eq_rewrites_to (s₁ s₂:nnrs_imp_stmt) :
    s₁ ≡ˢ s₂ ->
    (forall {Γc:tbindings} {Γ:tbindings},
        [ Γc ; Γ ⊢ s₁ ] ->
        [ Γc ; Γ ⊢ s₂ ]) ->
    s₁ ⇒ˢ s₂.
  Proof.
    red; intros eqq; intros; split; eauto; intros ??? typ2.
    apply eqq.
    - apply Forall_map.
      eapply bindings_type_Forall_normalized; eauto.
    - intros ? inn.
      eapply pd_bindings_type_in_normalized in typ2; eauto.
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
      rewrite He1, He2 by trivial.
      apply olift2_ext; intros.
      apply Hop.
      - eapply nnrs_imp_expr_eval_preserves_types; eauto.
        rewrite He1; trivial.
      -  eapply nnrs_imp_expr_eval_preserves_types; eauto.
         rewrite He2; trivial.
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
      specialize (Hs1 _ _ H2).
      destruct Hs1 as [typ1 Hs1].
      specialize (Hs2 _ _ H3).
      destruct Hs2 as [typ2 Hs2].
      split; [econstructor; eauto | ].
      intros.
      rewrite Hs1 by trivial.
      apply olift_ext; intros.
      apply Hs2; trivial.
      eapply nnrs_imp_stmt_eval_preserves_types in H1; eauto.
    Qed.

    Global Instance NNRSimpAssign_tproper v :
      Proper (tnnrs_imp_expr_rewrites_to ==> tnnrs_imp_stmt_rewrites_to) (NNRSimpAssign v).
    Proof.
      unfold Proper, respectful, tnnrs_imp_stmt_rewrites_to; simpl.
      intros e1 e1' He1 Γc Γ typ.
      invcs typ.
      apply He1 in H2.
      destruct H2 as [typ1 He1'].
      split; [econstructor; eauto | ].
      intros.
      rewrite He1'; trivial.
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
      apply He1 in H2.
      destruct H2 as [typ1 He1'].
      specialize (Hs2 _ _ H4).
      destruct Hs2 as [typ2 Hs2].
      split; [econstructor; eauto | ].
      simpl; intros.
      rewrite He1' by trivial.
      apply olift_ext; intros.
      rewrite Hs2; trivial.
      apply some_lift in H1.
      destruct H1 as [? eqq1 ?]; subst.
      eapply nnrs_imp_expr_eval_preserves_types in eqq1; eauto.
      econstructor; simpl; eauto.
      split; trivial; intros ? eqq2; invcs eqq2; trivial.
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
      simpl; intros.
      rewrite Hs2; trivial.
      econstructor; simpl; eauto.
      split; trivial; intros ? eqq2; invcs eqq2; trivial.
    Qed.
    
    Global Instance NNRSimpFor_tproper v :
      Proper (tnnrs_imp_expr_rewrites_to ==> tnnrs_imp_stmt_rewrites_to ==> tnnrs_imp_stmt_rewrites_to) (NNRSimpFor v).
    Proof.
      unfold Proper, respectful, tnnrs_imp_stmt_rewrites_to; simpl.
      intros e1 e1' He1 s2 s2' Hs2 Γc Γ typ.
      invcs typ.
      apply He1 in H2.
      destruct H2 as [typ1 He1'].
      specialize (Hs2 _ _ H4).
      destruct Hs2 as [typ2 Hs2].
      split; [econstructor; eauto | ].
      simpl; intros.
      rewrite He1' by trivial.
      apply olift_ext; intros.
      destruct a; trivial.
      eapply nnrs_imp_expr_eval_preserves_types in H1; eauto.
      invcs H1; rtype_equalizer; subst.
      clear e1 e1' typ1 He1 He1'.
      revert σ H0.
      induction l; simpl; trivial.
      intros σ bt.
      invcs H5.
      rewrite Hs2; eauto.
      - match_option.
        destruct p; trivial.
        eapply IHl; eauto.
        eapply nnrs_imp_stmt_eval_preserves_types in eqq; eauto.
        + invcs eqq; trivial.
        + econstructor; simpl; eauto.
          split; trivial; intros ? eqq2; invcs eqq2; trivial.
      - econstructor; simpl; eauto.
        split; trivial; intros ? eqq2; invcs eqq2; trivial.
    Qed.
    
    Global Instance NNRSimpIf_tproper :
      Proper (tnnrs_imp_expr_rewrites_to ==> tnnrs_imp_stmt_rewrites_to ==> tnnrs_imp_stmt_rewrites_to ==> tnnrs_imp_stmt_rewrites_to) NNRSimpIf.
    Proof.
      unfold Proper, respectful, tnnrs_imp_stmt_rewrites_to; simpl.
      intros e1 e1' He1 s1 s1' Hs1 s2 s2' Hs2 Γc Γ typ.
      invcs typ.
      apply He1 in H3.
      destruct H3 as [type He1'].
      specialize (Hs1 _ _ H4).
      destruct Hs1 as [typ1 Hs1].
      specialize (Hs2 _ _ H5).
      destruct Hs2 as [typ2 Hs2].
      split; [econstructor; eauto | ].
      intros.
      rewrite He1' by trivial.
      match_option.
      destruct d; trivial.
      destruct b; eauto.
    Qed.

    Global Instance NNRSimpEither_tproper :
      Proper (tnnrs_imp_expr_rewrites_to ==> eq ==> tnnrs_imp_stmt_rewrites_to ==> eq ==> tnnrs_imp_stmt_rewrites_to ==> tnnrs_imp_stmt_rewrites_to) NNRSimpEither.
    Proof.
      unfold Proper, respectful, tnnrs_imp_stmt_rewrites_to; simpl.
      intros e1 e1' He1 ? ? ? s1 s1' Hs1 ? ? ? s2 s2' Hs2 Γc Γ typ.
      subst.
      invcs typ.
      apply He1 in H3.
      destruct H3 as [type He1'].
      specialize (Hs1 _ _ H6).
      destruct Hs1 as [typ1 Hs1].
      specialize (Hs2 _ _ H7).
      destruct Hs2 as [typ2 Hs2].
      split; [econstructor; eauto | ].
      intros.
      rewrite He1' by trivial.
      match_option.
      eapply nnrs_imp_expr_eval_preserves_types in eqq; eauto.
      invcs eqq; rtype_equalizer; subst.
      - rewrite Hs1; trivial.
        econstructor; simpl; eauto.
        split; trivial; intros ? eqq2; invcs eqq2; trivial.
      - rewrite Hs2; trivial.
        econstructor; simpl; eauto.
        split; trivial; intros ? eqq2; invcs eqq2; trivial.
    Qed.      

    Lemma NNRSImp_tproper {s₁ s₂} : tnnrs_imp_stmt_rewrites_to s₁ s₂ ->
                                    forall v,
                                      (nnrs_imp_stmt_var_usage s₁ v <> VarMayBeUsedWithoutAssignment ->
                                       nnrs_imp_stmt_var_usage s₂ v <> VarMayBeUsedWithoutAssignment) ->
                                   tnnrs_imp_rewrites_to (s₁, v) (s₂, v).
    Proof.
      unfold tnnrs_imp_rewrites_to; intros eqq v neimpl Γc τ [ne typ].
      eapply eqq in typ.
      destruct typ as [typ IHs].
      split.
      - split; eauto.
      - intros; simpl.
        rewrite IHs; trivial.
        econstructor; simpl; eauto.
        intuition; discriminate.
    Qed.
    
  End proper.

End TNNRSimpEq.

Notation "e1 ⇒ᵉ e2" := (tnnrs_imp_expr_rewrites_to e1 e2) (at level 80) : nnrs_imp.
Notation "s1 ⇒ˢ s2" := (tnnrs_imp_stmt_rewrites_to s1 s2) (at level 80) : nnrs_imp.
Notation "si1 ⇒ˢⁱ si2" := (tnnrs_imp_rewrites_to si1 si2) (at level 80) : nnrs_imp.

