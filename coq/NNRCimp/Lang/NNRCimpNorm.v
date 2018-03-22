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

Section NNRCimpNorm.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Morphisms.
  Require Import Utils.
  Require Import CommonRuntime.
  Require Import NNRCimp.
  Require Import NNRCimpEval.

  Context {fruntime:foreign_runtime}. 
  Context (h:brand_relation_t).
  
  (** NNRCimp evaluation preserves data normalization. *)

  Lemma nnrc_imp_expr_eval_normalized
        {σc:bindings} {σ:pd_bindings} {e:nnrc_imp_expr} {o} :
    nnrc_imp_expr_eval h σc σ e = Some o ->
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

  Lemma nnrc_imp_stmt_eval_normalized
        {σc:bindings}
        {σ:pd_bindings} {ψc:mc_bindings} {ψd:md_bindings}
        {s:nnrc_imp_stmt}
        {σ':pd_bindings} {ψc':mc_bindings} {ψd':md_bindings} :
    nnrc_imp_stmt_eval h σc σ ψc ψd s = Some (σ', ψc', ψd') ->
    Forall (data_normalized h) (map snd σc) ->
    (forall x, In (Some x) (map snd σ) -> data_normalized h x)  ->
    Forall (Forall (data_normalized h)) (map snd ψc) ->
    (forall x, In (Some x) (map snd ψd) -> data_normalized h x)  ->
    (forall x, In (Some x) (map snd σ') -> data_normalized h x)  /\
    Forall (Forall (data_normalized h)) (map snd ψc') /\
    (forall x, In (Some x) (map snd ψd') -> data_normalized h x).
  Proof.
    intros eqq Fσc.
    revert σ ψc ψd σ' ψc' ψd' eqq.
    nnrc_imp_stmt_cases (induction s) Case; intros  σ ψc ψd σ' ψc' ψd' eqq Fσ Fψc' Fψd'; simpl in *.
    - Case "NNRCimpSeq".
      match_case_in eqq; [intros [[??]?] eqq1 | intros eqq1]
      ; rewrite eqq1 in eqq; try discriminate.
      destruct (IHs1 _ _ _ _ _ _  eqq1) as [?[??]]; eauto.
    -  Case "NNRCimpLet".
       match_case_in eqq; [intros ? eqq1 | intros eqq1]
       ; rewrite eqq1 in eqq; try discriminate.
       match_case_in eqq; [intros ? eqq2 | intros eqq2]
       ; rewrite eqq2 in eqq; try discriminate.
       destruct p as [[??]?].
       destruct p; try discriminate.
       invcs eqq.
       apply nnrc_imp_expr_eval_normalized in eqq1; eauto.
       specialize (IHs _ _ _ _ _ _ eqq2).
       cut_to IHs.
       * intuition.
         apply H; simpl; eauto.
       * simpl; intuition.
         invcs H0; auto.
       * eauto.
       * eauto.
    - Case "NNRCimpLetMut".
      match_case_in eqq; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in eqq; try discriminate.
      destruct p as [[??]?].
      destruct m0; try discriminate.
      destruct p0.
      match_case_in eqq; [intros ? eqq2 | intros eqq2]
      ; rewrite eqq2 in eqq; try discriminate.
      destruct p0 as [[??]?].
      destruct p0; try discriminate.
      invcs eqq.
      specialize (IHs1 _ _ _ _ _ _ eqq1).
      specialize (IHs2 _ _ _ _ _ _ eqq2).
      simpl in *.
      cut_to IHs1.
      + cut_to IHs2; intuition.
      + intuition.
      + intuition.
      + intuition; try discriminate.
    - Case "NNRCimpLetMutColl".
      match_case_in eqq; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in eqq; try discriminate.
      destruct p as [[??]?].
      destruct m; try discriminate.
      destruct p0.
      match_case_in eqq; [intros ? eqq2 | intros eqq2]
      ; rewrite eqq2 in eqq; try discriminate.
      destruct p0 as [[??]?].
      destruct p0; try discriminate.
      invcs eqq.
      specialize (IHs1 _ _ _ _ _ _ eqq1).
      specialize (IHs2 _ _ _ _ _ _ eqq2).
      simpl in *.
      cut_to IHs1.
      + cut_to IHs2; simpl; intuition.
        * invcs H3.
          invcs H1.
          constructor; trivial.
        * invcs H1; trivial.
      + intuition.
      + intuition.
      + intuition; try discriminate.
    - Case "NNRCimpAssign".
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
      + eapply Fψd'.
        apply in_map_iff; eexists; split; eauto; simpl; eauto.
      + invcs H.
        eapply nnrc_imp_expr_eval_normalized; eauto.
    - Case "NNRCimpPush".
      match_case_in eqq; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in eqq; try discriminate.
      match_case_in eqq; [intros ? eqq2 | intros eqq2]
      ; rewrite eqq2 in eqq; try discriminate.
      invcs eqq.
      intuition.
      rewrite Forall_map in *.
      apply Forall_update_first; simpl; trivial.
      apply Forall_app.
      +  apply lookup_in in eqq2.
         rewrite Forall_forall in Fψc'.
         apply (Fψc' _ eqq2).
      + constructor; trivial.
        eapply nnrc_imp_expr_eval_normalized; eauto.
    - Case "NNRCimpFor".
      match_case_in eqq; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in eqq; try discriminate.
      destruct d; try discriminate.
      apply nnrc_imp_expr_eval_normalized in eqq1; eauto 2.
      revert σ ψc ψd σ' ψc' ψd' eqq Fσ Fψc' Fψd' eqq1.
      induction l; intros σ ψc ψd σ' ψc' ψd' eqq Fσ Fψc' Fψd' eqq1; simpl.
      + invcs eqq; intuition.
      + match_case_in eqq; [intros ? eqq2 | intros eqq2]
        ; rewrite eqq2 in eqq; try discriminate.
        destruct p as [[??]?]; destruct p; try discriminate.
        apply data_normalized_dcoll in eqq1.
        apply IHs in eqq2; simpl in *.
        * apply (IHl _ _ _ _ _ _ eqq); intuition.
        * intuition.
          invcs H2; intuition.
        * intuition.
        * intuition.
    - Case "NNRCimpIf".
      match_case_in eqq; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in eqq; try discriminate.
      generalize (nnrc_imp_expr_eval_normalized eqq1); intros Fd.
      cut_to Fd; eauto 2.
      destruct d; try discriminate.
      destruct b; try discriminate; eauto.
    - Case "NNRCimpEither".
      match_case_in eqq; [intros ? eqq1 | intros eqq1]
      ; rewrite eqq1 in eqq; try discriminate.
      generalize (nnrc_imp_expr_eval_normalized eqq1); intros Fd.
      cut_to Fd; eauto 2.
      destruct d; try discriminate;
        (match_case_in eqq; [intros ? eqq2 | intros eqq2]
         ; rewrite eqq2 in eqq; try discriminate
         ; destruct p as [[??]?]; destruct p; try discriminate; invcs eqq)
        ; invcs Fd.
      + specialize (IHs1 _ _ _ _ _ _ eqq2).
        cut_to IHs1; simpl in *; intuition.
        invcs H1; intuition.
      + specialize (IHs2 _ _ _ _ _ _ eqq2).
        cut_to IHs2; simpl in *; intuition.
        invcs H1; intuition.
  Qed.
  
  Lemma nnrc_imp_eval_normalized  {σc:bindings} {q:nnrc_imp} {d} :
    nnrc_imp_eval h σc q = Some d ->
    Forall (data_normalized h) (map snd σc) ->
    forall x, d = Some x -> data_normalized h x.
  Proof.
    unfold nnrc_imp_eval; intros ev Fσc.
    destruct q.
    match_case_in ev; [intros [[??]?] eqq | intros eqq]
    ; rewrite eqq in ev; try discriminate.
    destruct m0; try discriminate.
    destruct p0.
    invcs ev.
    destruct d; try discriminate.
    intros ? eqq2; invcs eqq2.
    apply nnrc_imp_stmt_eval_normalized in eqq; simpl in *; intuition; try discriminate.
    rewrite Forall_map in *.
    apply dnrec_sort_content; trivial.
  Qed.

    Lemma nnrc_imp_eval_top_normalized  {σc:bindings} {q:nnrc_imp} {d} :
    nnrc_imp_eval_top h σc q = Some d ->
    Forall (data_normalized h) (map snd σc) ->
    data_normalized h d.
  Proof.
    unfold nnrc_imp_eval_top; intros ev Fσc.
    unfold olift, id in ev.
    match_option_in ev.
    eapply nnrc_imp_eval_normalized; eauto.
  Qed.
  
End NNRCimpNorm.

Hint Resolve nnrc_imp_expr_eval_normalized.
Hint Resolve nnrc_imp_stmt_eval_normalized.

Arguments nnrc_imp_expr_eval_normalized {fruntime h σc σ e o}.
Arguments nnrc_imp_stmt_eval_normalized {fruntime h σc σ ψc ψd s σ' ψc' ψd'}.

