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
Require Import NNRCimpishSystem.
Require Import NNRCtoNNRCimpish.
Require Import TNNRCStratify.

Section TNNRCtoNNRCimpish.
  Local Open Scope nnrc_impish.

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
    
    Lemma tnnrc_expr_to_nnrc_impish_expr_some_correct {e ei} :
      nnrc_expr_to_nnrc_impish_expr e = Some ei ->
      forall (Γc Γ:tbindings) (τ:rtype),
        nnrc_type Γc Γ e τ <-> [ Γc ; pd_tbindings_lift Γ  ⊢ ei ▷ τ ].
    Proof.
      unfold nnrc_type.
      Hint Constructors nnrc_core_type.
      Hint Constructors nnrc_impish_expr_type.
      
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

    Lemma nnrc_stmt_to_nnrc_impish_stmt_aux_must_assign
          {fvs x s si} :
      nnrc_stmt_to_nnrc_impish_stmt_aux fvs (Term_assign x) s = Some si ->
      nnrc_impish_stmt_must_assign si x.
    Proof.
      revert x si.
      induction s; simpl; intros x si eqq
      ; repeat match_option_in eqq; invcs eqq; simpl; eauto.
    Qed.
    
    Lemma tnnrc_stmt_to_nnrc_impish_stmt_aux_some_correct_fw {fvs term s si} :
      nnrc_stmt_to_nnrc_impish_stmt_aux fvs term s = Some si ->
      forall {Γc:tbindings} {Γ:tbindings} {τ:rtype},
        nnrc_type Γc Γ s τ ->
        forall Δc Δd,
          [ Γc ; pd_tbindings_lift Γ , (add_term_mc term τ Δc) , (add_term_md term τ Δd) ⊢ si ].
    Proof.
      unfold nnrc_type.
      Hint Resolve terminate_type.
      Hint Constructors nnrc_core_type.
      Hint Constructors nnrc_impish_expr_type.
      intros eqq Γc.
      revert fvs term si eqq.
      induction s; simpl; intros fvs term si eqq Γ τ typ Δc Δd
      ; repeat match_option_in eqq; invcs eqq; try solve [invcs typ; eauto 3].
      - invcs typ.
        apply terminate_type.
        econstructor.
        rewrite lookup_pd_tbindings_lift, H1; simpl; trivial.
      - apply terminate_type.
        apply (tnnrc_expr_to_nnrc_impish_expr_some_correct (e:=NNRCBinop b s1 s2))
        ; simpl; eauto.
      - apply terminate_type.
        apply (tnnrc_expr_to_nnrc_impish_expr_some_correct (e:=NNRCUnop u s))
        ; simpl; eauto.
      - invcs typ.
        econstructor.
        + eapply nnrc_stmt_to_nnrc_impish_stmt_aux_must_assign; eauto.
        + specialize (IHs1 _ _ _ eqq0 _ _ H4
                           (add_term_mc term τ Δc)
                           (add_term_md term τ Δd)); simpl in IHs1; eauto.
        + specialize (IHs2 _ _ _ eqq1 _ _ H5); simpl in IHs2; eauto.
      - invcs typ.
        econstructor.
        + econstructor.
          * eapply tnnrc_expr_to_nnrc_impish_expr_some_correct; eauto.
          * specialize (IHs2 _ _ _ eqq1 _ _ H5); simpl in IHs2; eauto.
        + apply terminate_type.
          econstructor; simpl.
          match_destr; congruence.
      - invcs typ.
        econstructor; eauto.
        apply (tnnrc_expr_to_nnrc_impish_expr_some_correct eqq0); trivial.
      - invcs typ.
        econstructor; eauto.
        + apply (tnnrc_expr_to_nnrc_impish_expr_some_correct eqq0); eauto.
        + specialize (IHs2 _ _ _ eqq1 _ _ H7); simpl in IHs2; eauto.
        + specialize (IHs3 _ _ _ eqq2 _ _ H8); simpl in IHs3; eauto.
      - apply terminate_type.
        eapply (tnnrc_expr_to_nnrc_impish_expr_some_correct (e:= (NNRCGroupBy s l s0))); simpl; eauto.
    Qed.


    Theorem tnnrc_stmt_to_nnrc_impish_some_correct_fw {Γc:tbindings} {globals s si} :
      nnrc_stmt_to_nnrc_impish globals s = Some si ->
      forall {τ:rtype},
        nnrc_type Γc nil s τ ->
        [ h, Γc ⊢ si ▷ τ ].
    Proof.
      unfold nnrc_stmt_to_nnrc_impish, nnrc_impish_type; match_option
      ; intros eqq1; invcs eqq1.
      intros τ typ.
      unfold nnrc_type in *.
      apply (tnnrc_stmt_to_nnrc_impish_stmt_aux_some_correct_fw eqq typ).
    Qed.

    Definition get_terminator_type
               (term:terminator)
               (mc:mc_tbindings)
               (md:md_tbindings) : option rtype :=
      match term with
      | Term_assign v => lookup equiv_dec md v
      | Term_push v => lookup equiv_dec mc v
      end.

    Lemma terminate_type_inv  {Γc:tbindings} {Γ:pd_tbindings} {e τ} { term Δc Δd }:
      [ Γc ; Γ , Δc , Δd ⊢ terminate term e ] ->
      get_terminator_type term Δc Δd = Some τ ->
      exists τ', [ Γc ; Γ  ⊢ e ▷ τ' ] /\ τ' ≤ τ.
    Proof.
      destruct term; simpl; intros typ eqq; invcs typ; simpl in *
      ; unfold equiv_dec, string_eqdec in *
      ; rewrite H5 in eqq; invcs eqq
      ; eauto.
    Qed.

    Section counterexample.
      Local Open Scope string.
      
      Example nnrc_stmt_with_weaker_nnrc_impish_type_example : nnrc 
        := NNRCBinop (OpNatBinary NatPlus)
                     (NNRCConst (dnat 1))
                     (NNRCConst (dnat 2)).

      Example nnrc_impish_of_nnrc_stmt_with_weaker_nnrc_impish_type_example
        :=     (NNRCimpishPush "x"
                            (NNRCimpishBinop (OpNatBinary NatPlus) (NNRCimpishConst (dnat 1))
                                          (NNRCimpishConst (dnat 2)))).

      Example nnrc_impish_of_nnrc_stmt_with_weaker_nnrc_impish_type_example_correct
        : nnrc_stmt_to_nnrc_impish_stmt_aux nil (Term_push "x") nnrc_stmt_with_weaker_nnrc_impish_type_example = Some nnrc_impish_of_nnrc_stmt_with_weaker_nnrc_impish_type_example.
      Proof.
        vm_compute; reflexivity.
      Qed.

      Example nnrc_impish_typing_for_nnrc_with_weaker_nnrc_impish_type_example 
        : [ nil ; pd_tbindings_lift nil , (add_term_mc (Term_push "x") ⊤ nil) , (add_term_md (Term_push "x") ⊤ nil) ⊢ nnrc_impish_of_nnrc_stmt_with_weaker_nnrc_impish_type_example ].
      Proof.
        unfold nnrc_impish_of_nnrc_stmt_with_weaker_nnrc_impish_type_example.
        simpl.
        econstructor; simpl.
        - repeat econstructor.
        - reflexivity.
        - apply STop.
      Qed.

      Example nnrc_typing_for_nnrc_with_weaker_nnrc_impish_type_example 
        : nnrc_type nil nil nnrc_stmt_with_weaker_nnrc_impish_type_example Nat.
      Proof.
        unfold nnrc_type, nnrc_stmt_with_weaker_nnrc_impish_type_example.
        simpl.
        econstructor; simpl
        ; repeat econstructor.
      Qed.

      Example not_nnrc_typing_for_nnrc_with_weaker_nnrc_impish_type_example 
        : ~ nnrc_type nil nil nnrc_stmt_with_weaker_nnrc_impish_type_example ⊤.
      Proof.
        unfold nnrc_type, nnrc_stmt_with_weaker_nnrc_impish_type_example
        ; simpl; intros typ.
        invcs typ.
        invcs H3.
      Qed.

      Example nnrc_typing_weaker_nnrc_impish_translated_typing :
        nnrc_stmt_to_nnrc_impish_stmt_aux nil (Term_push "x")
                                       nnrc_stmt_with_weaker_nnrc_impish_type_example =
        Some nnrc_impish_of_nnrc_stmt_with_weaker_nnrc_impish_type_example
        /\ 
        [ nil ; pd_tbindings_lift nil , (add_term_mc (Term_push "x") ⊤ nil) , (add_term_md (Term_push "x") ⊤ nil)
                                                                                ⊢ nnrc_impish_of_nnrc_stmt_with_weaker_nnrc_impish_type_example ]
        /\ ~ nnrc_type nil nil nnrc_stmt_with_weaker_nnrc_impish_type_example ⊤.
      Proof.
        split; [ | split].
        - apply nnrc_impish_of_nnrc_stmt_with_weaker_nnrc_impish_type_example_correct.
        - apply nnrc_impish_typing_for_nnrc_with_weaker_nnrc_impish_type_example.
        - apply not_nnrc_typing_for_nnrc_with_weaker_nnrc_impish_type_example.
      Qed.

    (*
    Example nnrc_with_weaker_nnrc_impish_type_example : nnrc 
      := NNRCFor "x"%string (NNRCConst (dcoll (dnat 3:: dnat 4::dnat 5::nil)))
                 nnrc_stmt_with_weaker_nnrc_impish_type_example.
     *)

    (* Backwards is more problematic, since the type system for nnrc_impish allows for 
       free upcasts in a NNRCimpishPush, whereas NNRC typing does not have
       such a mechanism (and NNRC is not Proper with respect to subtyping, since
       operators (such as (OpNatBinary NatPlus) are not.
       For example, 
       nnrc_typing_weaker_nnrc_impish_translated_typing witnesses a counter example.      *)
    End counterexample.

  End from_stratified.

  Lemma tnnrc_stmt_to_nnrc_impish_stmt_stratified_some_correct_fw {Γc:tbindings} {globals s τ} :
    nnrc_type Γc nil s τ ->
    forall pf,
      [ h, Γc ⊢ ` (nnrc_stmt_to_nnrc_impish_stmt_stratified_some globals s pf) ▷ τ ].
  Proof.
    intros typ pf.
    destruct (nnrc_stmt_to_nnrc_impish_stmt_stratified_some globals s pf); simpl.
    eapply tnnrc_stmt_to_nnrc_impish_some_correct_fw; eauto.
  Qed.
  
  Theorem tnnrc_to_nnrc_impish_correct_fw {Γc:tbindings} {globals s τ} :
    nnrc_type Γc nil s τ ->
    [ h, Γc ⊢ (nnrc_to_nnrc_impish_top globals s) ▷ τ ].
  Proof.
    intros typ.
    unfold nnrc_to_nnrc_impish_top.
    apply tnnrc_stmt_to_nnrc_impish_stmt_stratified_some_correct_fw.
    apply -> stratify_preserves_types.
    trivial.
  Qed.

End TNNRCtoNNRCimpish.
