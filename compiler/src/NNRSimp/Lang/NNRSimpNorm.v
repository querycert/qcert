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
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRSimp.
Require Import NNRSimpEval.
  
Section NNRSimpNorm.

  Context {fruntime:foreign_runtime}. 
  Context (h:brand_relation_t).
  
  (** NNRSimp evaluation preserves data normalization. *)

  Lemma nnrs_imp_expr_eval_normalized
        {σc:bindings} {σ:pd_bindings} {e:nnrs_imp_expr} {o} :
    nnrs_imp_expr_eval h σc σ e = Some o ->
    Forall (data_normalized h) (map snd σc) ->
    (forall x, In (Some x) (map snd σ) -> data_normalized h x)  ->
    data_normalized h o.
  Proof.
    intros eqq Fσc.
    revert σ o eqq.
    induction e; intros σ o eqq Fσ; simpl in *.
    - unfold edot in *.
      apply assoc_lookupr_in in eqq.
      rewrite Forall_forall in *.
      apply Fσc.
      apply in_map_iff; exists (v, o); simpl; auto.
    - apply some_olift in eqq.
      unfold id in eqq.
      destruct eqq as [???]; subst.
      apply lookup_in in e.
      eapply Fσ.
      apply in_map_iff; exists (v, Some o); simpl; auto.
    - invcs eqq.
      apply normalize_normalizes.
    - apply some_olift2 in eqq.
      destruct eqq as [?[??[? HH]]].
      apply (binary_op_eval_normalized _ (symmetry HH)); eauto.
    - apply some_olift in eqq.
      destruct eqq as [? ? HH].
      apply (unary_op_eval_normalized _ (symmetry HH)); eauto.
    - match_case_in eqq; [intros ? eqq2 | intros eqq2]; rewrite eqq2 in eqq
      ; try discriminate.
      destruct d; try discriminate.
      apply some_lift in eqq.
      destruct eqq as [???]; subst.
      eapply group_by_nested_eval_table_normalized; eauto.
      apply data_normalized_dcoll_Forall.
      eauto.
  Qed.

  Local Open Scope string.

  Lemma nnrs_imp_stmt_eval_normalized
        {σc:bindings}
        {σ:pd_bindings}
        {s:nnrs_imp_stmt}
        {σ':pd_bindings} :
    nnrs_imp_stmt_eval h σc s σ = Some σ' ->
    Forall (data_normalized h) (map snd σc) ->
    (forall x, In (Some x) (map snd σ) -> data_normalized h x)  ->
    (forall x, In (Some x) (map snd σ') -> data_normalized h x).
  Proof.
    intros eqq Fσc.
    revert σ σ' eqq.
    nnrs_imp_stmt_cases (induction s) Case; intros  σ σ' eqq Fσ; simpl in *.
    - Case "NNRSimpSkip".
      invcs eqq; trivial.
    - Case "NNRSimpSeq".
      apply some_olift in eqq.
      destruct eqq as [???]; eauto.
    - Case "NNRSimpAssign".
      match_case_in eqq; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in eqq; try discriminate.
      match_case_in eqq; [intros ? eqq2 | intros eqq2]
      ; rewrite eqq2 in eqq; try discriminate.
      invcs eqq.
      intuition.
      rewrite in_map_iff in H.
      destruct H as [[??][? inn]].
      simpl in *; subst.
      apply update_first_in_or in inn.
      destruct inn.
      + eapply Fσ.
        apply in_map_iff; eexists; split; eauto; simpl; eauto.
      + invcs H.
        eapply nnrs_imp_expr_eval_normalized; eauto.
    -  Case "NNRSimpLet".
       destruct o; simpl in *.
       + apply some_olift in eqq.
         destruct eqq as [? eqq1 eqq2].
         apply some_lift in eqq1.
         destruct eqq1 as [? eqq1 ?]; subst.
         match_option_in eqq2.
         destruct p; try discriminate.
         invcs eqq2.
         apply nnrs_imp_expr_eval_normalized in eqq1; eauto.
         intros.
         apply (IHs _ _ eqq); simpl; eauto.
         intuition.
         invcs H1; eauto.
       + match_option_in eqq.
         destruct p; try discriminate.
         invcs eqq.
         intros.
         apply (IHs _ _ eqq0); simpl; eauto.
         intuition.
         invcs H1; eauto.
    - Case "NNRSimpFor".
      match_case_in eqq; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in eqq; try discriminate.
      destruct d; try discriminate.
      apply nnrs_imp_expr_eval_normalized in eqq1; eauto 2.
      revert σ σ' eqq Fσ eqq1.
      induction l; intros σ σ' eqq Fσ eqq1; simpl.
      + invcs eqq; intuition.
      + match_case_in eqq; [intros ? eqq2 | intros eqq2]
        ; rewrite eqq2 in eqq; try discriminate.
        destruct p; try discriminate.
        apply data_normalized_dcoll in eqq1.
        specialize (IHl _ _ eqq).
        specialize (IHs _ _ eqq2); simpl in *.
        apply IHl; [ | tauto].
        intros; apply IHs; [ | tauto].
        intuition.
        invcs H3.
        eauto.
    - Case "NNRSimpIf".
      match_case_in eqq; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in eqq; try discriminate.
      generalize (nnrs_imp_expr_eval_normalized eqq1); intros Fd.
      cut_to Fd; eauto 2.
      destruct d; try discriminate.
      destruct b; try discriminate; eauto.
    - Case "NNRSimpEither".
      match_case_in eqq; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in eqq; try discriminate.
      generalize (nnrs_imp_expr_eval_normalized eqq1); intros Fd.
      cut_to Fd; eauto 2.
      destruct d; try discriminate;
        (match_case_in eqq; [intros ? eqq2 | intros eqq2]
         ; rewrite eqq2 in eqq; try discriminate
         ; destruct p; try discriminate; invcs eqq)
        ; invcs Fd.
      + specialize (IHs1 _ _ eqq2).
        cut_to IHs1; simpl in *; intuition.
        invcs H1; intuition.
      + specialize (IHs2 _ _ eqq2).
        cut_to IHs2; simpl in *; intuition.
        invcs H1; intuition.
  Qed.
  
  Lemma nnrs_imp_eval_normalized  {σc:bindings} {q:nnrs_imp} {d} :
    nnrs_imp_eval h σc q = Some d ->
    Forall (data_normalized h) (map snd σc) ->
    forall x, d = Some x -> data_normalized h x.
  Proof.
    unfold nnrs_imp_eval; intros ev Fσc.
    destruct q.
    match_case_in ev; [intros ? eqq | intros eqq]
    ; rewrite eqq in ev; try discriminate.
    destruct p; try discriminate.
    destruct p.
    invcs ev.
    destruct d; try discriminate.
    intros ? eqq2; invcs eqq2.
    eapply nnrs_imp_stmt_eval_normalized in eqq; simpl in *; intuition; try discriminate; trivial.
  Qed.

    Lemma nnrs_imp_eval_top_normalized  {σc:bindings} {q:nnrs_imp} {d} :
    nnrs_imp_eval_top h σc q = Some d ->
    Forall (data_normalized h) (map snd σc) ->
    data_normalized h d.
  Proof.
    unfold nnrs_imp_eval_top; intros ev Fσc.
    unfold olift, id in ev.
    match_option_in ev.
    eapply nnrs_imp_eval_normalized; eauto.
    rewrite Forall_map in *.
    apply dnrec_sort_content; trivial.
  Qed.
  
End NNRSimpNorm.

Hint Resolve nnrs_imp_expr_eval_normalized.
Hint Resolve nnrs_imp_stmt_eval_normalized.

Arguments nnrs_imp_expr_eval_normalized {fruntime h σc σ e o}.
Arguments nnrs_imp_stmt_eval_normalized {fruntime h σc σ s σ'}.

