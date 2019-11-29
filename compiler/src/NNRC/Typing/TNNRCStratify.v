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

(* NNRC is an expression oriented language.  
   We want to be able to compile it to statement oriented languages like
   nnrs.  As an inbetween step, we can stratify the language, 
   separating expressions and statements.

This transformation, called stratify, is in NNRCStratify.
This module shows that the transformation preserves types.
 *)

Require Import String.
Require Import List.
Require Import Bool.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Permutation.
Require Import Eqdep_dec.
Require Import Utils.
Require Import CommonSystem.
Require Import cNNRCSystem.
Require Import NNRCRuntime.
Require Import cNNRCTypes. (* Always include core support *)
Require Import TNNRC.

Section TNNRCStratify.
  Context {m:basic_model}.
  
  Fixpoint type_substs Γc (Γ:tbindings) (sdefs:list (var*nnrc)) (τdefs:tbindings) : Prop
    := match sdefs, τdefs with
       | nil, nil => True
       | (v₁, n)::sdefs', (v₂, τ)::τdefs' =>
         v₁ = v₂ /\
         nnrc_type Γc Γ n τ
         /\ type_substs Γc ((v₂,τ)::Γ) sdefs' τdefs'
       | _, _ => False
       end.

  Lemma type_substs_domain_eq {Γc} {Γ:tbindings} {sdefs:list (var*nnrc)} {τdefs:tbindings} :
    type_substs Γc Γ sdefs τdefs ->
    domain sdefs = domain τdefs.
  Proof.
    revert τdefs Γ .
    induction sdefs; destruct τdefs; simpl; trivial; intros Γ typ
    ; try contradiction; destruct a; try contradiction.
    destruct p; simpl in *.
    intuition; subst.
    f_equal.
    eauto.
  Qed.

  Lemma type_substs_app Γc Γ sdefs1 τdefs1 sdefs2 τdefs2 :
    type_substs Γc Γ sdefs1 τdefs1 ->
    type_substs Γc (rev τdefs1++Γ) sdefs2 τdefs2 ->
    type_substs Γc Γ (sdefs1++sdefs2) (τdefs1++τdefs2).
  Proof.
    revert Γ sdefs2 τdefs1 τdefs2.
    induction sdefs1; simpl; intros Γ sdefs2 τdefs1 τdefs2 ts1 ts2.
    - match_destr_in ts1; try contradiction.
    - destruct a.
      match_destr_in ts1; try contradiction.
      destruct p.
      destruct ts1 as [? [ts11 ts12]]; subst; simpl.
      repeat (split; trivial).
      apply IHsdefs1; trivial.
      simpl in ts2.
      repeat rewrite app_ass in ts2; simpl in ts2.
      trivial.
  Qed.

  (*** Forwards type preservation ***)
  Lemma stratify1_aux_preserves_types_fw
        {e: nnrc} {required_kind:nnrcKind} {bound_vars:list var} {sdefs1 n sdefs2} :
    stratify1_aux e required_kind bound_vars sdefs1 = (n,sdefs2) ->
    forall τdefs1 Γc Γ  τ,
      type_substs Γc Γ sdefs1 τdefs1 ->
      nnrc_type Γc (rev τdefs1 ++ Γ) e τ ->
      exists τdefs2,
        type_substs Γc Γ sdefs2 τdefs2
        /\ nnrc_type Γc (rev τdefs2 ++ Γ) n τ.
  Proof.
    Opaque fresh_var.
    destruct required_kind; simpl; intros eqq; invcs eqq; intros.
    - exists (τdefs1++((fresh_var "stratify" bound_vars, τ)::nil)); simpl.
      split.
      + apply type_substs_app; trivial.
        simpl; intuition.
      + constructor.
        rewrite rev_app_distr.
        rewrite lookup_app; simpl.
        destruct (
            equiv_dec
              (fresh_var "stratify" bound_vars)
              (fresh_var "stratify" bound_vars))
        ; try congruence. 
    - exists τdefs1; simpl; eauto.
  Qed.

  Lemma mk_expr_from_vars_preserves_types_fw
        {n: nnrc} {sdefs τdefs}
        { Γc Γ τ} :
    type_substs Γc Γ sdefs τdefs ->
    nnrc_type Γc (rev τdefs ++ Γ) n τ ->
    nnrc_type Γc Γ (mk_expr_from_vars (n,sdefs)) τ.
  Proof.
    unfold mk_expr_from_vars.
    revert τdefs n Γ.
    induction sdefs; intros τdefs Γ; destruct τdefs; simpl; intros n typs typn
    ; try destruct a as [? n2]; try contradiction; trivial.
    destruct p as [? τ2].
    destruct typs as [? [typn1 typs]]; subst.
    simpl.
    unfold nnrc_type in *; simpl.
    rewrite app_ass in typn.
    simpl in typn.
    simpl in *.
    econstructor; eauto.
  Qed.

  Lemma stratify_aux_preserves_types_fw
        (e: nnrc) (required_kind:nnrcKind) (bound_vars:list var) n sdefs :
    incl (nnrc_free_vars e) bound_vars ->
    stratify_aux e required_kind bound_vars = (n,sdefs) ->
    forall Γc Γ τ,
      nnrc_type Γc Γ e τ ->
      exists τdefs,
        type_substs Γc Γ sdefs τdefs
        /\ nnrc_type Γc (rev τdefs ++ Γ) n τ.
  Proof.
    Hint Constructors nnrc_core_type.
    unfold nnrc_type.
    revert required_kind bound_vars n sdefs.
    induction e; simpl; intros required_kind bound_vars n sdefs inclb eqq Γc Γ τ typ.
    - invcs eqq.
      (* add this case to the nnrc_core_inverter Ltac *)
      invcs typ.
      simpl; exists nil; simpl; eauto.
    - invcs eqq.
      nnrc_core_inverter.
      simpl; exists nil; simpl; eauto.
    - invcs eqq.
      nnrc_core_inverter.
      simpl; exists nil; simpl; eauto.
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      match_case_in eqq; intros ? ? eqq2; rewrite eqq2 in eqq.
      invcs eqq.
      apply incl_app_iff in inclb; destruct inclb as [inclb1 inclb2].
      nnrc_core_inverter.
      destruct (IHe1 _ _ _ _ inclb1 eqq1 _ _ _ H5)
        as [τdefs1 [typdefs1 typn1]].
      assert (inclb2':incl (nnrc_free_vars e2) (domain l ++ bound_vars))
        by (unfold incl in *; intros; rewrite in_app_iff; eauto).
      assert (type2':nnrc_core_type Γc (rev τdefs1 ++ Γ) (nnrc_to_nnrc_base e2) τ₂).
      {
        apply (nnrc_core_type_remove_disjoint_env nil (rev τdefs1) Γ); simpl; trivial.
        rewrite domain_rev.
        rewrite disjoint_rev_l.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typdefs1).
        eapply disjoint_incl.
        - rewrite <- nnrc_to_nnrc_base_free_vars_same.
          apply inclb2.
        - apply (stratify_aux_nbound_vars eqq1).
      }
      specialize (IHe2 _ _ _ _ inclb2' eqq2 _ _ _ type2')
        as [τdefs2 [typdefs2 typn2]].
      exists (τdefs1 ++ τdefs2).
      split.
      + apply type_substs_app; trivial.
      + rewrite rev_app_distr.
        rewrite app_ass.
        econstructor; eauto.
        apply (nnrc_core_type_remove_disjoint_env nil (rev τdefs2 )(rev τdefs1 ++ Γ)); simpl; trivial.
        rewrite domain_rev.
        rewrite disjoint_rev_l.
        rewrite <- nnrc_to_nnrc_base_free_vars_same.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typdefs2).
        eapply disjoint_incl;
          [ | apply (stratify_aux_nbound_vars eqq2)].
        intros x inn.
        destruct (stratify_aux_free_vars eqq1 inclb1 x) as [eqf _].
        repeat rewrite in_app_iff in *.
        intuition.
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      invcs eqq.
      nnrc_core_inverter.
      destruct (IHe _ _ _ _ inclb eqq1 _ _ _ H4)
        as [τdefs1 [typdefs1 typn1]].
      exists τdefs1.
      eauto.
    - apply incl_app_iff in inclb; destruct inclb as [inclb1 inclb2].
      apply incl_remove in inclb2.
      nnrc_core_inverter.
      apply (stratify1_aux_preserves_types_fw eqq nil); simpl; trivial.
      unfold nnrc_type in *; simpl.
      econstructor.
      + case_eq (stratify_aux e1 nnrcStmt bound_vars); intros ? ? eqq1; rewrite eqq1 in eqq.
        destruct (IHe1 _ _ _ _ inclb1 eqq1 _ _ _ H4)
          as [τdefs1 [typdefs1 typn1]].
        apply (mk_expr_from_vars_preserves_types_fw typdefs1 typn1).
      + case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2; rewrite eqq2 in eqq.
        destruct (IHe2 _ _ _ _ inclb2 eqq2 _ _ _ H5)
          as [τdefs2 [typdefs2 typn2]].
        apply (mk_expr_from_vars_preserves_types_fw typdefs2 typn2).
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      apply incl_app_iff in inclb; destruct inclb as [inclb1 inclb2].
      apply incl_remove in inclb2.
      nnrc_core_inverter.
      destruct (IHe1 _ _ _ _ inclb1 eqq1 _ _ _ H4)
        as [τdefs1 [typdefs1 typn1]].
      apply (stratify1_aux_preserves_types_fw eqq τdefs1); simpl; trivial.
      unfold nnrc_type in *; simpl.
      econstructor; eauto.
      case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2; rewrite eqq2 in eqq.
      destruct (IHe2 _ _ _ _ inclb2 eqq2 _ _ _ H5)
        as [τdefs2 [typdefs2 typn2]].
      apply (nnrc_core_type_remove_almost_disjoint_env ((v, τ₁)::nil) (rev τdefs1 ) Γ); simpl; trivial
      ; [ | apply (mk_expr_from_vars_preserves_types_fw typdefs2 typn2)].
      + intros x inn1 inn2.
        rewrite domain_rev, <- in_rev in inn1.
        rewrite <- nnrc_to_nnrc_base_free_vars_same in inn2.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typdefs1) in inn1.
        destruct (mk_expr_stratify_aux_free_vars e2 nnrcStmt (v::bound_vars) inclb2 x)
          as [eqf _].
        rewrite eqq2 in eqf.
        apply eqf in inn2.
        generalize (stratify_aux_nbound_vars eqq1 _ inn1); intros nbound.
        specialize (inclb2 _ inn2).
        simpl in inclb2.
        intuition.
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      apply incl_app_iff in inclb; destruct inclb as [inclb1 inclb2].
      apply incl_app_iff in inclb2; destruct inclb2 as [inclb2 inclb3].
      nnrc_core_inverter.
      destruct (IHe1 _ _ _ _ inclb1 eqq1 _ _ _ H3)
        as [τdefs1 [typdefs1 typn1]].
      apply (stratify1_aux_preserves_types_fw eqq τdefs1); simpl; trivial.
      unfold nnrc_type in *; simpl.
      econstructor; eauto.
      + case_eq (stratify_aux e2 nnrcStmt bound_vars); intros ? ? eqq2; rewrite eqq2 in eqq.
        destruct (IHe2 _ _ _ _ inclb2 eqq2 _ _ _ H5)
          as [τdefs2 [typdefs2 typn2]].
        apply (nnrc_core_type_remove_disjoint_env nil (rev τdefs1 ) Γ); simpl; trivial
        ; [ | apply (mk_expr_from_vars_preserves_types_fw typdefs2 typn2)].
        intros x inn1 inn2.
        rewrite domain_rev, <- in_rev in inn1.
        rewrite <- nnrc_to_nnrc_base_free_vars_same in inn2.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typdefs1) in inn1.
        destruct (mk_expr_stratify_aux_free_vars e2 nnrcStmt (bound_vars) inclb2 x)
          as [eqf _].
        rewrite eqq2 in eqf.
        apply eqf in inn2.
        generalize (stratify_aux_nbound_vars eqq1 _ inn1); intros nbound.
        specialize (inclb2 _ inn2).
        simpl in inclb2.
        intuition.
      + case_eq (stratify_aux e3 nnrcStmt bound_vars); intros ? ? eqq3; rewrite eqq3 in eqq.
        destruct (IHe3 _ _ _ _ inclb3 eqq3 _ _ _ H6)
          as [τdefs3 [typdefs3 typn3]].
        apply (nnrc_core_type_remove_disjoint_env nil (rev τdefs1 ) Γ); simpl; trivial
        ; [ | apply (mk_expr_from_vars_preserves_types_fw typdefs3 typn3)].
        intros x inn1 inn3.
        rewrite domain_rev, <- in_rev in inn1.
        rewrite <- nnrc_to_nnrc_base_free_vars_same in inn3.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typdefs1) in inn1.
        destruct (mk_expr_stratify_aux_free_vars e3 nnrcStmt (bound_vars) inclb3 x)
          as [eqf _].
        rewrite eqq3 in eqf.
        apply eqf in inn3.
        generalize (stratify_aux_nbound_vars eqq1 _ inn1); intros nbound.
        specialize (inclb3 _ inn3).
        simpl in inclb3.
        intuition.
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      apply incl_app_iff in inclb; destruct inclb as [inclb1 inclb2].
      apply incl_app_iff in inclb2; destruct inclb2 as [inclb2 inclb3].
      apply incl_remove in inclb2.
      apply incl_remove in inclb3.
      nnrc_core_inverter.
      destruct (IHe1 _ _ _ _ inclb1 eqq1 _ _ _ H6)
        as [τdefs1 [typdefs1 typn1]].
      apply (stratify1_aux_preserves_types_fw eqq τdefs1); simpl; trivial.
      unfold nnrc_type in *; simpl.
      econstructor; eauto.
      + case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2; rewrite eqq2 in eqq.
        destruct (IHe2 _ _ _ _ inclb2 eqq2 _ _ _ H7)
          as [τdefs2 [typdefs2 typn2]].
        apply (nnrc_core_type_remove_almost_disjoint_env ((v,τl)::nil) (rev τdefs1 ) Γ); simpl; trivial
        ; [ | apply (mk_expr_from_vars_preserves_types_fw typdefs2 typn2)].
        intros x inn1 inn2.
        rewrite domain_rev, <- in_rev in inn1.
        rewrite <- nnrc_to_nnrc_base_free_vars_same in inn2.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typdefs1) in inn1.
        destruct (mk_expr_stratify_aux_free_vars e2 nnrcStmt (v::bound_vars) inclb2 x)
          as [eqf _].
        rewrite eqq2 in eqf.
        apply eqf in inn2.
        generalize (stratify_aux_nbound_vars eqq1 _ inn1); intros nbound.
        specialize (inclb2 _ inn2).
        simpl in inclb2.
        intuition.
      + case_eq (stratify_aux e3 nnrcStmt (v0::bound_vars)); intros ? ? eqq3; rewrite eqq3 in eqq.
        destruct (IHe3 _ _ _ _ inclb3 eqq3 _ _ _ H8)
          as [τdefs3 [typdefs3 typn3]].
        apply (nnrc_core_type_remove_almost_disjoint_env ((v0,τr)::nil) (rev τdefs1 ) Γ); simpl; trivial
        ; [ | apply (mk_expr_from_vars_preserves_types_fw typdefs3 typn3)].
        intros x inn1 inn3.
        rewrite domain_rev, <- in_rev in inn1.
        rewrite <- nnrc_to_nnrc_base_free_vars_same in inn3.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typdefs1) in inn1.
        destruct (mk_expr_stratify_aux_free_vars e3 nnrcStmt (v0::bound_vars) inclb3 x)
          as [eqf _].
        rewrite eqq3 in eqf.
        apply eqf in inn3.
        generalize (stratify_aux_nbound_vars eqq1 _ inn1); intros nbound.
        specialize (inclb3 _ inn3).
        simpl in inclb3.
        intuition.
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      assert (typ':nnrc_type Γc Γ (NNRCGroupBy s l e) τ)
        by apply typ.
      apply type_NNRCGroupBy_inv in typ'.
      destruct typ' as [? [? [? [? [subl type]]]]]; subst.
      destruct (IHe _ _ _ _ inclb eqq1 _ _ _ type)
        as [τdefs1 [typdefs1 typn1]].
      apply (stratify1_aux_preserves_types_fw eqq τdefs1); simpl; trivial.
      apply type_NNRCGroupBy; trivial.
  Qed.

  Lemma mk_expr_from_vars_stratify_aux_preserves_types_fw
        {Γc Γ} (e: nnrc) {τ} :
    nnrc_type Γc Γ e τ ->
    forall  (required_kind:nnrcKind) (bound_vars:list var),
      incl (nnrc_free_vars e) bound_vars ->
      nnrc_type Γc Γ (mk_expr_from_vars (stratify_aux e required_kind bound_vars)) τ.
  Proof.
    intros typ required_kind bound_vars inclb.
    case_eq (stratify_aux e required_kind bound_vars); intros ? ? eqq.
    destruct (stratify_aux_preserves_types_fw _ _ _ _ _ inclb eqq _ _ _ typ)
      as [? [typs typn]].
    eapply mk_expr_from_vars_preserves_types_fw; eauto.
  Qed.

  Theorem stratify_preserves_types_fw
          {Γc Γ} (e: nnrc) {τ} :
    nnrc_type Γc Γ e τ ->
    nnrc_type Γc Γ (stratify e) τ.
  Proof.
    intros typ.
    apply mk_expr_from_vars_stratify_aux_preserves_types_fw; trivial.
    reflexivity.
  Qed.

  Lemma type_substs_app_inv Γc Γ sdefs1 τdefs1 sdefs2 τdefs2 :
    type_substs Γc Γ (sdefs1++sdefs2) (τdefs1++τdefs2) ->
    length sdefs1 = length τdefs1 ->
    type_substs Γc Γ sdefs1 τdefs1 /\
    type_substs Γc (rev τdefs1++Γ) sdefs2 τdefs2.
  Proof.
    revert Γ sdefs2 τdefs1 τdefs2.
    induction sdefs1; simpl; intros Γ sdefs2 τdefs1 τdefs2 ts1 ts2.
    - match_destr; simpl in *; eauto.
    - destruct a.
      match_destr; simpl in *; try discriminate.
      destruct p.
      destruct ts1 as [? [ts11 ts12]]; subst; simpl.
      invcs ts2.
      destruct (IHsdefs1 _ _ _ _ ts12 H0).
      repeat (split; trivial).
      repeat rewrite app_ass; simpl.
      trivial.
  Qed.
  
  Lemma type_substs_app_inv_ex {Γc Γ sdefs1 sdefs2 τdefs} :
    type_substs Γc Γ (sdefs1++sdefs2) τdefs ->
    exists τdefs1 τdefs2,
      τdefs = τdefs1 ++ τdefs2 /\
      type_substs Γc Γ sdefs1 τdefs1 /\
      type_substs Γc (rev τdefs1++Γ) sdefs2 τdefs2.
  Proof.
    revert Γ sdefs2 τdefs.
    induction sdefs1; simpl; intros Γ sdefs2 τdefs ts.
    - exists nil, τdefs; simpl; tauto.
    - destruct a.
      match_destr_in ts; simpl in *; try contradiction.
      destruct p.
      destruct ts as [? [ts11 ts12]]; subst; simpl.
      destruct (IHsdefs1 _ _ _ ts12) as [τdefs1 [τdefs2 [? [typs1 typs2]]]]; subst.
      exists ((s,r)::τdefs1), τdefs2; simpl; intuition.
      repeat rewrite app_ass; simpl.
      trivial.
  Qed.
  
  (*** Backwards type preservation ***)    
  Lemma stratify1_aux_preserves_types_bk
        {e: nnrc} {required_kind:nnrcKind} {bound_vars:list var} {sdefs1 n sdefs2} :
    stratify1_aux e required_kind bound_vars sdefs1 = (n,sdefs2) ->
    forall τdefs2 Γc Γ  τ,
      type_substs Γc Γ sdefs2 τdefs2 ->
      nnrc_type Γc (rev τdefs2 ++ Γ) n τ ->
      exists τdefs1,
        type_substs Γc Γ sdefs1 τdefs1
        /\ nnrc_type Γc (rev τdefs1 ++ Γ) e τ.
  Proof.
    Opaque fresh_var.
    destruct required_kind; simpl; intros eqq; invcs eqq; intros.
    - generalize (type_substs_domain_eq H); intros deq.
      rewrite domain_app in deq; simpl in deq.
      assert (nnil:τdefs2 <> nil).
      { destruct τdefs2; simpl in deq; try discriminate.
        symmetry in deq; apply app_cons_not_nil in deq; tauto.
      } 
      destruct (exists_last nnil) as [τdefs2' [[x τ2] ?]]; subst.
      rewrite domain_app in deq; simpl in deq.
      apply app_inj_tail in deq.
      destruct deq as [deq ?]; subst.
      apply type_substs_app_inv in H.
      + destruct H as [typs1 typs2].
        exists τdefs2'; split; trivial.
        simpl in typs2.
        invcs H0.
        rewrite rev_app_distr in H2.
        simpl in H2.
        match_destr_in H2; try congruence.
        invcs H2.
        intuition.
      + rewrite <- domain_length, deq, domain_length; trivial.
    - eauto.
  Qed.

  Lemma mk_expr_from_vars_preserves_types_bk
        {n: nnrc} {sdefs}
        { Γc Γ τ} :
    nnrc_type Γc Γ (mk_expr_from_vars (n,sdefs)) τ ->
    exists τdefs,
      type_substs Γc Γ sdefs τdefs /\
      nnrc_type Γc (rev τdefs ++ Γ) n τ.
  Proof.
    unfold mk_expr_from_vars.
    revert n Γ.
    induction sdefs; simpl; intros n Γ typ.
    - exists nil; simpl; eauto.
    - destruct a; unfold nnrc_type in *; simpl in *.
      invcs typ.
      specialize (IHsdefs _ _ H5).
      destruct IHsdefs as [τdefs [typs typn]].
      exists ((v,τ₁)::τdefs); intuition.
      simpl.
      rewrite app_ass; simpl.
      trivial.
  Qed.

  Lemma stratify_aux_preserves_types_bk
        (e: nnrc) (required_kind:nnrcKind) (bound_vars:list var) n sdefs :
    incl (nnrc_free_vars e) bound_vars ->
    stratify_aux e required_kind bound_vars = (n,sdefs) ->
    forall Γc Γ τdefs,
      type_substs Γc Γ sdefs τdefs ->
      forall τ,
        nnrc_type Γc (rev τdefs ++ Γ) n τ ->
        nnrc_type Γc Γ e τ.
  Proof.
    Hint Constructors nnrc_core_type.
    unfold nnrc_type.
    revert required_kind bound_vars n sdefs.
    induction e; simpl; intros required_kind bound_vars n sdefs inclb eqq Γc Γ τdefs typs τ typn.
    - invcs eqq.
      destruct τdefs; simpl in *; try contradiction.
      eauto.
    - invcs eqq.
      destruct τdefs; simpl in *; try contradiction.
      eauto.
    - invcs eqq.
      destruct τdefs; simpl in *; try contradiction.
      eauto.
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      match_case_in eqq; intros ? ? eqq2; rewrite eqq2 in eqq.
      invcs eqq.
      apply incl_app_iff in inclb; destruct inclb as [inclb1 inclb2].
      simpl in typn.
      nnrc_core_inverter.
      apply type_substs_app_inv_ex in typs.
      destruct typs as [τdefs1 [τdefs2 [? [typs1 typs2]]]]; subst.
      repeat rewrite rev_app_distr in *.
      repeat rewrite app_ass in *.
      econstructor; eauto.
      + apply (IHe1 _ _ _ _ inclb1 eqq1 _ _ _ typs1 τ₁).
        apply (nnrc_core_type_remove_disjoint_env nil (rev τdefs2) (rev τdefs1 ++ Γ)); simpl; trivial.
        rewrite domain_rev.
        rewrite disjoint_rev_l.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typs2).
        eapply disjoint_incl;
          [ | apply (stratify_aux_nbound_vars eqq2)].
        intros x inn.
        destruct (stratify_aux_free_vars eqq1 inclb1 x) as [eqf _].
        repeat rewrite in_app_iff in *.
        specialize (inclb2 x).
        rewrite <- nnrc_to_nnrc_base_free_vars_same in inn.
        intuition.
      + assert (inclb2':incl (nnrc_free_vars e2) (domain l ++ bound_vars)).
        { apply incl_appr; trivial. }
        specialize (IHe2 _ _ _ _ inclb2' eqq2 _ _ _ typs2 τ₂ H6).
        apply (nnrc_core_type_remove_disjoint_env nil (rev τdefs1) Γ); simpl; trivial.
        rewrite domain_rev.
        rewrite disjoint_rev_l.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typs1).
        eapply disjoint_incl;
          [ | apply (stratify_aux_nbound_vars eqq1)].
        rewrite <- nnrc_to_nnrc_base_free_vars_same; trivial.
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      invcs eqq.
      simpl in *.
      nnrc_core_inverter.
      econstructor; eauto.
    - apply incl_app_iff in inclb; destruct inclb as [inclb1 inclb2].
      apply incl_remove in inclb2.
      destruct (stratify1_aux_preserves_types_bk eqq _ _ _ _ typs typn)
        as [? [typs' typn']]; simpl; trivial.
      simpl in typs'.
      destruct x; try contradiction.
      simpl in typn'.
      unfold nnrc_type in *; simpl in *.
      invcs typn'.
      destruct (mk_expr_from_vars_preserves_types_bk H4)
        as [τdefs1 [ts1 tp1]].
      destruct (mk_expr_from_vars_preserves_types_bk H5)
        as [τdefs2 [ts2 tp2]].
      case_eq (stratify_aux e1 nnrcStmt bound_vars); intros ? ? eqq1
      ; rewrite eqq1 in *.
      case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2
      ; rewrite eqq2 in *.
      simpl in *.
      eauto.
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      apply incl_app_iff in inclb; destruct inclb as [inclb1 inclb2].
      apply incl_remove in inclb2.
      destruct (stratify1_aux_preserves_types_bk eqq _ _ _ _ typs typn)
        as [τdefs2 [typs' typn']]; simpl; trivial.
      unfold nnrc_type in *; simpl in *.
      invcs typn'.
      econstructor; [eauto | ].
      destruct (mk_expr_from_vars_preserves_types_bk H5)
        as [τdefs1 [ts1 tp1]].
      case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2
      ; rewrite eqq2 in *.
      simpl in *.
      apply (nnrc_core_type_remove_almost_disjoint_env ((v, τ₁)::nil) (rev τdefs2) Γ); simpl; eauto.
      intros x inn1 inn2.
      rewrite domain_rev, <- in_rev in inn1.
      rewrite <- nnrc_to_nnrc_base_free_vars_same in inn2.
      unfold var in *.
      rewrite <- (type_substs_domain_eq typs') in inn1.
      generalize (stratify_aux_nbound_vars eqq1 _ inn1); intros nbound.
      specialize (inclb2 _ inn2).
      simpl in inclb2.
      tauto.
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      apply incl_app_iff in inclb; destruct inclb as [inclb1 inclb2].
      apply incl_app_iff in inclb2; destruct inclb2 as [inclb2 inclb3].
      destruct (stratify1_aux_preserves_types_bk eqq _ _ _ _ typs typn)
        as [τdefs2 [typs' typn']]; simpl; trivial.
      unfold nnrc_type in *; simpl in *.
      invcs typn'.
      econstructor; [eauto | | ].
      + destruct (mk_expr_from_vars_preserves_types_bk H5)
          as [τdefs1 [ts1 tp1]].
        case_eq (stratify_aux e2 nnrcStmt bound_vars); intros ? ? eqq2
        ; rewrite eqq2 in *.
        simpl in *.
        apply (nnrc_core_type_remove_almost_disjoint_env nil (rev τdefs2) Γ); simpl; eauto.
        intros x inn1 inn2.
        rewrite domain_rev, <- in_rev in inn1.
        rewrite <- nnrc_to_nnrc_base_free_vars_same in inn2.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typs') in inn1.
        generalize (stratify_aux_nbound_vars eqq1 _ inn1); intros nbound.
        specialize (inclb2 _ inn2).
        simpl in inclb2.
        tauto.
      + destruct (mk_expr_from_vars_preserves_types_bk H6)
          as [τdefs1 [ts1 tp1]].
        case_eq (stratify_aux e3 nnrcStmt bound_vars); intros ? ? eqq3
        ; rewrite eqq3 in *.
        simpl in *.
        apply (nnrc_core_type_remove_almost_disjoint_env nil (rev τdefs2) Γ); simpl; eauto.
        intros x inn1 inn2.
        rewrite domain_rev, <- in_rev in inn1.
        rewrite <- nnrc_to_nnrc_base_free_vars_same in inn2.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typs') in inn1.
        generalize (stratify_aux_nbound_vars eqq1 _ inn1); intros nbound.
        specialize (inclb3 _ inn2).
        simpl in inclb3.
        tauto.
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      apply incl_app_iff in inclb; destruct inclb as [inclb1 inclb2].
      apply incl_app_iff in inclb2; destruct inclb2 as [inclb2 inclb3].
      apply incl_remove in inclb2.
      apply incl_remove in inclb3.
      destruct (stratify1_aux_preserves_types_bk eqq _ _ _ _ typs typn)
        as [τdefs2 [typs' typn']]; simpl; trivial.
      unfold nnrc_type in *; simpl in *.
      invcs typn'.
      econstructor; [eauto | | ].
      + destruct (mk_expr_from_vars_preserves_types_bk H7)
          as [τdefs1 [ts1 tp1]].
        case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2
        ; rewrite eqq2 in *.
        simpl in *.
        apply (nnrc_core_type_remove_almost_disjoint_env ((v, τl)::nil) (rev τdefs2) Γ); simpl; eauto.
        intros x inn1 inn2.
        rewrite domain_rev, <- in_rev in inn1.
        rewrite <- nnrc_to_nnrc_base_free_vars_same in inn2.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typs') in inn1.
        generalize (stratify_aux_nbound_vars eqq1 _ inn1); intros nbound.
        specialize (inclb2 _ inn2).
        simpl in inclb2.
        tauto.
      + destruct (mk_expr_from_vars_preserves_types_bk H8)
          as [τdefs1 [ts1 tp1]].
        case_eq (stratify_aux e3 nnrcStmt (v0::bound_vars)); intros ? ? eqq3
        ; rewrite eqq3 in *.
        simpl in *.
        apply (nnrc_core_type_remove_almost_disjoint_env ((v0,τr)::nil) (rev τdefs2) Γ); simpl; eauto.
        intros x inn1 inn2.
        rewrite domain_rev, <- in_rev in inn1.
        rewrite <- nnrc_to_nnrc_base_free_vars_same in inn2.
        unfold var in *.
        rewrite <- (type_substs_domain_eq typs') in inn1.
        generalize (stratify_aux_nbound_vars eqq1 _ inn1); intros nbound.
        specialize (inclb3 _ inn2).
        simpl in inclb3.
        tauto.
    - match_case_in eqq; intros ? ? eqq1; rewrite eqq1 in eqq.
      destruct (stratify1_aux_preserves_types_bk eqq _ _ _ _ typs typn)
        as [τdefs2 [typs' typn']]; simpl; trivial.
      apply type_NNRCGroupBy_inv in typn'.
      destruct typn' as [? [? [? [? [subl type]]]]]; subst.
      cut (nnrc_type Γc Γ (NNRCGroupBy s l e) (GroupBy_type s l x x0 x1)); trivial.
      apply type_NNRCGroupBy; trivial.
      unfold nnrc_type; eauto.
  Qed.

  Lemma mk_expr_from_vars_stratify_aux_preserves_types_bk
        {Γc Γ} (e: nnrc) {τ} :
    forall  (required_kind:nnrcKind) (bound_vars:list var),
      incl (nnrc_free_vars e) bound_vars ->
      nnrc_type Γc Γ (mk_expr_from_vars (stratify_aux e required_kind bound_vars)) τ ->
      nnrc_type Γc Γ e τ.
  Proof.
    intros required_kind bound_vars inclb typ.
    destruct (mk_expr_from_vars_preserves_types_bk typ)
      as [τdefs1 [ts1 tp1]].
    case_eq (stratify_aux e required_kind bound_vars); intros ? ? eqq; rewrite eqq in *.
    eapply stratify_aux_preserves_types_bk; eauto.
  Qed.

  Theorem stratify_preserves_types_bk
          {Γc Γ} (e: nnrc) {τ} :
    nnrc_type Γc Γ (stratify e) τ ->
    nnrc_type Γc Γ e τ.
  Proof.
    unfold stratify.
    intros typ.
    eapply mk_expr_from_vars_stratify_aux_preserves_types_bk; eauto.
    reflexivity.
  Qed.

  (*** Stratify does not affect typing ***)
  
  Theorem stratify_preserves_types
          Γc Γ (e: nnrc) τ :
    nnrc_type Γc Γ e τ <-> nnrc_type Γc Γ (stratify e) τ.
  Proof.
    split; intros.
    - apply stratify_preserves_types_fw; trivial.
    - eapply stratify_preserves_types_bk; eauto.
  Qed.
  
End TNNRCStratify.

(* 
 *** Local Variables: ***
 *** coq-load-path: (("../../../coq" "Qcert")) ***
 *** End: ***
 *)

