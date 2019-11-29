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
Require Import cNNRCSystem.
Require Import NNRCSystem.
Require Import NNRSSystem.
Require Import NNRCtoNNRS.
Require Import TNNRCStratify.

Section TNNRCtoNNRS.
  Local Open Scope nnrs.

  Context {m:basic_model}.
  Context (τconstants:tbindings).

  Section from_stratified.

    Definition pd_tbindings_lift (σ:tbindings) : pd_tbindings
      := map_codomain Some σ.

    Lemma lookup_pd_tbindings_lift Γ v :
      lookup equiv_dec (pd_tbindings_lift Γ) v = lift Some (lookup equiv_dec Γ v).
    Proof.
      apply lookup_map_codomain.
    Qed.

    Lemma rproject_eq_preserves_sublist_full
          {A} {odt:ODT}
          (l1 l2 : list (string * A)) (sl : list string) :
      is_list_sorted ODT_lt_dec (domain l1) = true ->
      is_list_sorted ODT_lt_dec (domain l2) = true ->
      sublist sl (domain l1) ->
      rproject l1 sl = rproject l2 sl ->
      sublist sl (domain l2).
    Proof.
      intros.
      apply Sorted_incl_sublist.
      - eapply is_list_sorted_Sorted_iff.
        eapply is_list_sorted_sublist; try eapply H1.
        eapply H.
      - eapply is_list_sorted_Sorted_iff; eauto.
      - intros.
        assert (inn:In x (domain (rproject l1 sl))).
        { apply rproject_domain_in; split; trivial.
          eapply sublist_In; eauto.
        }
        rewrite H2 in inn.
        apply rproject_domain_in in inn; tauto.
    Qed.
    
    Lemma tnnrc_expr_to_nnrs_expr_some_correct {e ei} :
      nnrc_expr_to_nnrs_expr e = Some ei ->
      forall (Γc Γ:tbindings) (τ:rtype),
        nnrc_type Γc Γ e τ <-> [ Γc ; pd_tbindings_lift Γ  ⊢ ei ▷ τ ].
    Proof.
      unfold nnrc_type.
      Hint Constructors nnrc_core_type.
      Hint Constructors nnrs_expr_type.
      
      revert ei.
      induction e; simpl; intros ei eqq Γc Γ τ; try discriminate.
      - invcs eqq.
        split; intros typ; invcs typ; eauto.
      - invcs eqq.
        split; intros typ; invcs typ; eauto.
        + constructor.
          rewrite lookup_pd_tbindings_lift.
          rewrite H1; simpl; trivial.
        + rewrite lookup_pd_tbindings_lift in H1.
          apply some_lift in H1.
          destruct H1 as [? ? eqq1]; invcs eqq1.
          eauto.
      - invcs eqq; split; intros typ; invcs typ; eauto.
      - apply some_lift2 in eqq.
        destruct eqq as [? [??[??]]]; subst.
        split; intros typ; invcs typ
        ; (econstructor; eauto 2
           ; [eapply IHe1 | eapply IHe2]; eauto).        
      - apply some_lift in eqq.
        destruct eqq as [? ? ?]; subst.
        split; intros typ; invcs typ
        ; (econstructor; eauto 2
           ; eapply IHe; eauto).        
      - apply some_lift in eqq.
        destruct eqq as [? ? ?]; subst.
        split; intros typ.
        + change (nnrc_type Γc Γ (NNRCGroupBy s l e) τ) in typ.
          apply type_NNRCGroupBy_inv in typ.
          destruct typ as [? [? [? [eqq1 [subl typ]]]]]; subst.
          constructor; trivial.
          apply IHe; eauto.
        +  invcs typ.
           change (nnrc_type Γc Γ (NNRCGroupBy s l e) (GroupBy_type s l k τl pf)).
           apply type_NNRCGroupBy; trivial.
           eapply IHe; eauto.
    Qed.

    Definition add_term_mc (term:terminator) τ (Δc:mc_tbindings)
      := match term with
         | Term_push x => (x,τ)::Δc
         | Term_assign x => Δc
         end.

    Definition add_term_md (term:terminator) τ (Δd:md_tbindings)
      := match term with
         | Term_push x => Δd
         | Term_assign x => (x,τ)::Δd
         end.

    Lemma terminate_type  {Γc:tbindings} {Γ:pd_tbindings} {e τ} :
      [ Γc ; Γ  ⊢ e ▷ τ ] -> forall term Δc Δd  ,
        [ Γc ; Γ , (add_term_mc term τ Δc) , (add_term_md term τ Δd) ⊢ terminate term e ].
    Proof.
      intros typ term Δc Δd.
      destruct term; simpl
      ; econstructor; simpl; try reflexivity; eauto
      ; match_destr
      ; congruence.
    Qed.

    Lemma nnrc_stmt_to_nnrs_stmt_aux_must_assign
          {fvs x s si} :
      nnrc_stmt_to_nnrs_stmt_aux fvs (Term_assign x) s = Some si ->
      nnrs_stmt_must_assign si x.
    Proof.
      revert x si.
      induction s; simpl; intros x si eqq
      ; repeat match_option_in eqq; invcs eqq; simpl; eauto.
    Qed.
    
    Lemma tnnrc_stmt_to_nnrs_stmt_aux_some_correct_fw {fvs term s si} :
      nnrc_stmt_to_nnrs_stmt_aux fvs term s = Some si ->
      forall {Γc:tbindings} {Γ:tbindings} {τ:rtype},
        nnrc_type Γc Γ s τ ->
        forall Δc Δd,
          [ Γc ; pd_tbindings_lift Γ , (add_term_mc term τ Δc) , (add_term_md term τ Δd) ⊢ si ].
    Proof.
      unfold nnrc_type.
      Hint Resolve terminate_type.
      Hint Constructors nnrc_core_type.
      Hint Constructors nnrs_expr_type.
      intros eqq Γc.
      revert fvs term si eqq.
      induction s; simpl; intros fvs term si eqq Γ τ typ Δc Δd
      ; repeat match_option_in eqq; invcs eqq; try solve [invcs typ; eauto 3].
      - invcs typ.
        apply terminate_type.
        econstructor.
        rewrite lookup_pd_tbindings_lift, H1; simpl; trivial.
      - apply terminate_type.
        apply (tnnrc_expr_to_nnrs_expr_some_correct (e:=NNRCBinop b s1 s2))
        ; simpl; eauto.
      - apply terminate_type.
        apply (tnnrc_expr_to_nnrs_expr_some_correct (e:=NNRCUnop u s))
        ; simpl; eauto.
      - invcs typ.
        econstructor.
        + eapply nnrc_stmt_to_nnrs_stmt_aux_must_assign; eauto.
        + specialize (IHs1 _ _ _ eqq0 _ _ H4
                           (add_term_mc term τ Δc)
                           (add_term_md term τ Δd)); simpl in IHs1; eauto.
        + specialize (IHs2 _ _ _ eqq1 _ _ H5); simpl in IHs2; eauto.
      - invcs typ.
        econstructor.
        + econstructor.
          * eapply tnnrc_expr_to_nnrs_expr_some_correct; eauto.
          * specialize (IHs2 _ _ _ eqq1 _ _ H5); simpl in IHs2; eauto.
        + apply terminate_type.
          econstructor; simpl.
          match_destr; congruence.
      - invcs typ.
        econstructor; eauto.
        apply (tnnrc_expr_to_nnrs_expr_some_correct eqq0); trivial.
      - invcs typ.
        econstructor; eauto.
        + apply (tnnrc_expr_to_nnrs_expr_some_correct eqq0); eauto.
        + specialize (IHs2 _ _ _ eqq1 _ _ H7); simpl in IHs2; eauto.
        + specialize (IHs3 _ _ _ eqq2 _ _ H8); simpl in IHs3; eauto.
      - apply terminate_type.
        eapply (tnnrc_expr_to_nnrs_expr_some_correct (e:= (NNRCGroupBy s l s0))); simpl; eauto.
    Qed.


    Theorem tnnrc_stmt_to_nnrs_some_correct_fw {Γc:tbindings} {globals s si} :
      nnrc_stmt_to_nnrs globals s = Some si ->
      forall {τ:rtype},
        nnrc_type Γc nil s τ ->
        [ Γc ⊢ si ▷ τ ].
    Proof.
      unfold nnrc_stmt_to_nnrs, nnrs_type; match_option
      ; intros eqq1; invcs eqq1.
      intros τ typ.
      unfold nnrc_type in *.
      apply (tnnrc_stmt_to_nnrs_stmt_aux_some_correct_fw eqq typ).
    Qed.

    Definition get_terminator_type
               (term:terminator)
               (mc:mc_tbindings)
               (md:md_tbindings) : option rtype :=
      match term with
      | Term_assign v => lookup equiv_dec md v
      | Term_push v => lookup equiv_dec mc v
      end.

    Lemma terminate_type_inv  {Γc:tbindings} {Γ:pd_tbindings} {e} { term Δc Δd }:
      [ Γc ; Γ , Δc , Δd ⊢ terminate term e ] ->
      forall τ,
        get_terminator_type term Δc Δd = Some τ ->
        [ Γc ; Γ  ⊢ e ▷ τ].
    Proof.
      destruct term; simpl; intros typ τ eqq; invcs typ; simpl in *
      ; unfold equiv_dec, string_eqdec in *
      ; rewrite H5 in eqq; invcs eqq
      ; eauto.
    Qed.

    Lemma get_terminator_type_add_term 
          (term:terminator)
          τ
          (Δc:mc_tbindings)
          (Δd:md_tbindings) :
      get_terminator_type term (add_term_mc term τ Δc) (add_term_md term τ Δd)
      = Some τ.
    Proof.
      destruct term; simpl; match_destr; try congruence.
    Qed.        

    Lemma terminate_type_add_term_inv {Γc:tbindings} {Γ:pd_tbindings} {e} { term} {τ} {Δc Δd } :
      [Γc; Γ, add_term_mc term τ Δc, add_term_md term τ Δd
                                                 ⊢ terminate term e] ->
      [ Γc ; Γ  ⊢ e ▷ τ].
    Proof.
      intros typ.
      generalize (terminate_type_inv typ); simpl.
      rewrite get_terminator_type_add_term.
      intuition.
    Qed.

    Lemma tnnrc_stmt_to_nnrs_stmt_aux_some_correct_bk {fvs term s si} :
      nnrc_stmt_to_nnrs_stmt_aux fvs term s = Some si ->
      forall (Γc:tbindings) (Γ:tbindings) (τ:rtype) Δc Δd,
        [ Γc ; pd_tbindings_lift Γ , (add_term_mc term τ Δc) , (add_term_md term τ Δd) ⊢ si ] ->
        nnrc_type Γc Γ s τ.
    Proof.
      unfold nnrc_type.
      Hint Resolve terminate_type.
      Hint Constructors nnrc_core_type.
      Hint Constructors nnrs_expr_type.
      intros eqq Γc.
      revert fvs term si eqq.
      nnrc_cases (induction s) Case
      ; simpl; intros fvs term si eqq Γ τ Δc Δd typ
      ; repeat match_option_in eqq; invcs eqq
      ; try apply terminate_type_add_term_inv in typ
      ; try solve [invcs typ; eauto 3].
      - Case "NNRCVar"%string.
        invcs typ.
        rewrite lookup_pd_tbindings_lift in H1; simpl in H1.
        apply some_lift in H1.
        destruct H1 as [? ? eqq].
        invcs eqq.
        eauto.
      - Case "NNRCBinop"%string.
        apply some_lift2 in eqq0.
        destruct eqq0 as [? [? eqq1 [eqq2 ?]]]; subst.
        invcs typ.
        econstructor; eauto 2.
        + eapply tnnrc_expr_to_nnrs_expr_some_correct; eauto.
        + eapply tnnrc_expr_to_nnrs_expr_some_correct; eauto.
      - Case "NNRCUnop"%string.
        apply some_lift in eqq0.
        destruct eqq0 as [? eqq ?]; subst.
        invcs typ.
        econstructor; eauto 2.
        eapply tnnrc_expr_to_nnrs_expr_some_correct; eauto.
      - Case "NNRCLet"%string.
        invcs typ.
        + econstructor; eauto.
        + econstructor; eauto.
          eapply IHs2; eauto.
          simpl.
          apply  nnrs_stmt_type_env_cons_none_some; eauto.
      - Case "NNRCFor"%string.
        invcs typ.
        apply terminate_type_add_term_inv in H6.
        invcs H6.
        simpl in H1.
        match_destr_in H1; try congruence.
        invcs H1.
        invcs H4.
        econstructor.
        + eapply tnnrc_expr_to_nnrs_expr_some_correct; eauto.
        + eauto.
      - Case "NNRCIf"%string.
        invcs typ.
        econstructor; eauto.
        eapply tnnrc_expr_to_nnrs_expr_some_correct; eauto.
      - Case "NNRCEither"%string.
        invcs typ.
        econstructor.
        + eapply tnnrc_expr_to_nnrs_expr_some_correct; eauto.
        + eauto.
        + eauto.
      - Case "NNRCGroupBy"%string.
        apply some_lift in eqq0.
        destruct eqq0 as [? eqq ?]; subst.
        invcs typ.
        generalize type_NNRCGroupBy; unfold nnrc_type; simpl; intros HH.
        apply HH; trivial.
        eapply tnnrc_expr_to_nnrs_expr_some_correct; eauto.
    Qed.

    Theorem tnnrc_stmt_to_nnrs_some_correct_bk {Γc:tbindings} {globals s si} :
      nnrc_stmt_to_nnrs globals s = Some si ->
      forall {τ:rtype},
        [ Γc ⊢ si ▷ τ ] ->
        nnrc_type Γc nil s τ.
    Proof.
      unfold nnrc_stmt_to_nnrs, nnrs_type; match_option
      ; intros eqq1; invcs eqq1.
      intros τ typ.
      eapply (tnnrc_stmt_to_nnrs_stmt_aux_some_correct_bk eqq).
      simpl; eauto.
    Qed.

    Theorem tnnrc_stmt_to_nnrs_some_correct {Γc:tbindings} {globals s si} :
      nnrc_stmt_to_nnrs globals s = Some si ->
      forall {τ:rtype},
        nnrc_type Γc nil s τ <-> [ Γc ⊢ si ▷ τ ].
    Proof.
      intros; split; intros.
      - eapply tnnrc_stmt_to_nnrs_some_correct_fw; eauto.
      - eapply tnnrc_stmt_to_nnrs_some_correct_bk; eauto.
    Qed.

  End from_stratified.

  Lemma tnnrc_stmt_to_nnrs_stmt_stratified_some_correct_fw {Γc:tbindings} {globals s τ} :
    nnrc_type Γc nil s τ ->
    forall pf,
      [ Γc ⊢ ` (nnrc_stmt_to_nnrs_stmt_stratified_some globals s pf) ▷ τ ].
  Proof.
    intros typ pf.
    destruct (nnrc_stmt_to_nnrs_stmt_stratified_some globals s pf); simpl.
    eapply tnnrc_stmt_to_nnrs_some_correct_fw; eauto.
  Qed.
  
  Theorem tnnrc_to_nnrs_correct_fw {Γc:tbindings} {globals s τ} :
    nnrc_type Γc nil s τ ->
    [ Γc ⊢ (nnrc_to_nnrs_top globals s) ▷ τ ].
  Proof.
    intros typ.
    unfold nnrc_to_nnrs_top.
    apply tnnrc_stmt_to_nnrs_stmt_stratified_some_correct_fw.
    apply -> stratify_preserves_types.
    trivial.
  Qed.

  Lemma tnnrc_stmt_to_nnrs_stmt_stratified_some_correct_bk {Γc:tbindings} {globals s τ} {pf} :
    [ Γc ⊢ ` (nnrc_stmt_to_nnrs_stmt_stratified_some globals s pf) ▷ τ ] ->
    nnrc_type Γc nil s τ.
  Proof.
    intros typ.
    destruct (nnrc_stmt_to_nnrs_stmt_stratified_some globals s pf); simpl.
    eapply tnnrc_stmt_to_nnrs_some_correct_bk; eauto.
  Qed.
  
  Theorem tnnrc_to_nnrs_correct_bk {Γc:tbindings} {globals s τ} :
    [ Γc ⊢ (nnrc_to_nnrs_top globals s) ▷ τ ] ->
    nnrc_type Γc nil s τ.
  Proof.
    unfold nnrc_to_nnrs_top.
    intros typ.
    apply stratify_preserves_types.
    eapply tnnrc_stmt_to_nnrs_stmt_stratified_some_correct_bk; eauto.
  Qed.

  Theorem tnnrc_to_nnrs_correct (Γc:tbindings) globals s τ :
    nnrc_type Γc nil s τ <-> [ Γc ⊢ (nnrc_to_nnrs_top globals s) ▷ τ ].
  Proof.
    split; intros.
    - eapply tnnrc_to_nnrs_correct_fw; eauto.
    - eapply tnnrc_to_nnrs_correct_bk; eauto.
  Qed.

End TNNRCtoNNRS.
