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
Require Import Arith.
Require Import Max.
Require Import Bool.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRCimpish.
Require Import NNRCimpishVars.
Require Import NNRCimpishEval.

Section NNRCimpishRename.
  Context {fruntime:foreign_runtime}. 
  Context (h:brand_relation_t).

  Section renames.
    
    Fixpoint nnrc_impish_stmt_rename_mc
             (s:nnrc_impish_stmt) (oldvar newvar:var) : nnrc_impish_stmt
      := match s with
         | NNRCimpishSeq s₁ s₂ =>
           NNRCimpishSeq
             (nnrc_impish_stmt_rename_mc s₁ oldvar newvar)
             (nnrc_impish_stmt_rename_mc s₂ oldvar newvar)
         | NNRCimpishLet v e s₀ =>
           NNRCimpishLet
             v e
             (nnrc_impish_stmt_rename_mc s₀ oldvar newvar)         
         | NNRCimpishLetMut v s₁ s₂ =>
           NNRCimpishLetMut
             v
             (nnrc_impish_stmt_rename_mc s₁ oldvar newvar)         
             (nnrc_impish_stmt_rename_mc s₂ oldvar newvar)         
         | NNRCimpishLetMutColl v s₁ s₂ =>
           NNRCimpishLetMutColl
             v
             (if v == oldvar
              then s₁
              else nnrc_impish_stmt_rename_mc s₁ oldvar newvar)
             (nnrc_impish_stmt_rename_mc s₂ oldvar newvar)
         | NNRCimpishAssign v e =>
           NNRCimpishAssign v e
         | NNRCimpishPush v e =>
           NNRCimpishPush
             (if v == oldvar then newvar else v)
             e
         | NNRCimpishFor v e s₀ =>
           NNRCimpishFor
             v e
             (nnrc_impish_stmt_rename_mc s₀ oldvar newvar)         
         | NNRCimpishIf e s₁ s₂ =>
           NNRCimpishIf
             e
             (nnrc_impish_stmt_rename_mc s₁ oldvar newvar)
             (nnrc_impish_stmt_rename_mc s₂ oldvar newvar)         
         | NNRCimpishEither e x₁ s₁ x₂ s₂ =>
           NNRCimpishEither
             e
             x₁ (nnrc_impish_stmt_rename_mc s₁ oldvar newvar)
             x₂ (nnrc_impish_stmt_rename_mc s₂ oldvar newvar)         
         end.

    Fixpoint nnrc_impish_stmt_rename_md
             (s:nnrc_impish_stmt) (oldvar newvar:var) : nnrc_impish_stmt
      := match s with
         | NNRCimpishSeq s₁ s₂ =>
           NNRCimpishSeq
             (nnrc_impish_stmt_rename_md s₁ oldvar newvar)
             (nnrc_impish_stmt_rename_md s₂ oldvar newvar)
         | NNRCimpishLet v e s₀ =>
           NNRCimpishLet
             v e
             (nnrc_impish_stmt_rename_md s₀ oldvar newvar)         
         | NNRCimpishLetMut v s₁ s₂ =>
           NNRCimpishLetMut
             v
             (if v == oldvar
              then s₁
              else nnrc_impish_stmt_rename_md s₁ oldvar newvar)
             (nnrc_impish_stmt_rename_md s₂ oldvar newvar)
         | NNRCimpishLetMutColl v s₁ s₂ =>
           NNRCimpishLetMutColl
             v
             (nnrc_impish_stmt_rename_md s₁ oldvar newvar)         
             (nnrc_impish_stmt_rename_md s₂ oldvar newvar)
         | NNRCimpishAssign v e =>
           NNRCimpishAssign
             (if v == oldvar then newvar else v)
             e
         | NNRCimpishPush v e =>
           NNRCimpishPush v e

         | NNRCimpishFor v e s₀ =>
           NNRCimpishFor
             v e
             (nnrc_impish_stmt_rename_md s₀ oldvar newvar)         
         | NNRCimpishIf e s₁ s₂ =>
           NNRCimpishIf
             e
             (nnrc_impish_stmt_rename_md s₁ oldvar newvar)
             (nnrc_impish_stmt_rename_md s₂ oldvar newvar)         
         | NNRCimpishEither e x₁ s₁ x₂ s₂ =>
           NNRCimpishEither
             e
             x₁ (nnrc_impish_stmt_rename_md s₁ oldvar newvar)
             x₂ (nnrc_impish_stmt_rename_md s₂ oldvar newvar)         
         end.

    Fixpoint nnrc_impish_expr_rename_env
             (e:nnrc_impish_expr) (oldvar newvar:var) : nnrc_impish_expr
      := match e with
         |  NNRCimpishGetConstant v =>
            NNRCimpishGetConstant v
         | NNRCimpishVar v =>
           NNRCimpishVar
             (if v == oldvar then newvar else v)
         | NNRCimpishConst d =>
           NNRCimpishConst d
         | NNRCimpishBinop b e₁ e₂ =>
           NNRCimpishBinop
             b
             (nnrc_impish_expr_rename_env e₁ oldvar newvar)
             (nnrc_impish_expr_rename_env e₂ oldvar newvar)
         | NNRCimpishUnop u e₀ =>
           NNRCimpishUnop
             u
             (nnrc_impish_expr_rename_env e₀ oldvar newvar)
         | NNRCimpishGroupBy g ls e₀ =>
           NNRCimpishGroupBy
             g ls
             (nnrc_impish_expr_rename_env e₀ oldvar newvar)
         end.

    Fixpoint nnrc_impish_stmt_rename_env
             (s:nnrc_impish_stmt) (oldvar newvar:var) : nnrc_impish_stmt
      := match s with
         | NNRCimpishSeq s₁ s₂ =>
           NNRCimpishSeq
             (nnrc_impish_stmt_rename_env s₁ oldvar newvar)
             (nnrc_impish_stmt_rename_env s₂ oldvar newvar)
         | NNRCimpishLet v e s₀ =>
           NNRCimpishLet
             v
             (nnrc_impish_expr_rename_env e oldvar newvar)
             (if v == oldvar
              then s₀
              else nnrc_impish_stmt_rename_env s₀ oldvar newvar)
         | NNRCimpishLetMut v s₁ s₂ =>
           NNRCimpishLetMut
             v
             (nnrc_impish_stmt_rename_env s₁ oldvar newvar)
             (if v == oldvar
              then s₂
              else nnrc_impish_stmt_rename_env s₂ oldvar newvar)
         | NNRCimpishLetMutColl v s₁ s₂ =>
           NNRCimpishLetMutColl
             v
             (nnrc_impish_stmt_rename_env s₁ oldvar newvar)         
             (if v == oldvar
              then s₂
              else nnrc_impish_stmt_rename_env s₂ oldvar newvar)
         | NNRCimpishAssign v e =>
           NNRCimpishAssign
             v
             (nnrc_impish_expr_rename_env e oldvar newvar)
         | NNRCimpishPush v e =>
           NNRCimpishPush
             v
             (nnrc_impish_expr_rename_env e oldvar newvar)
         | NNRCimpishFor v e s₀ =>
           NNRCimpishFor
             v
             (nnrc_impish_expr_rename_env e oldvar newvar)
             (if v == oldvar
              then s₀
              else nnrc_impish_stmt_rename_env s₀ oldvar newvar)
         | NNRCimpishIf e s₁ s₂ =>
           NNRCimpishIf
             (nnrc_impish_expr_rename_env e oldvar newvar)
             (nnrc_impish_stmt_rename_env s₁ oldvar newvar)
             (nnrc_impish_stmt_rename_env s₂ oldvar newvar)         
         | NNRCimpishEither e x₁ s₁ x₂ s₂ =>
           NNRCimpishEither
             (nnrc_impish_expr_rename_env e oldvar newvar)
             x₁
             (if x₁ == oldvar
              then s₁
              else nnrc_impish_stmt_rename_env s₁ oldvar newvar)
             x₂
             (if x₂ == oldvar
              then s₂
              else nnrc_impish_stmt_rename_env s₂ oldvar newvar)
         end.

  End renames.

  Section rename_vars.
    
    Lemma nnrc_impish_expr_free_vars_rename_env e v v' :
      nnrc_impish_expr_free_vars (nnrc_impish_expr_rename_env e v v')
      = replace_all (nnrc_impish_expr_free_vars e) v v'.
    Proof.
      unfold replace_all.
      induction e; simpl; trivial.
      rewrite IHe1, IHe2, map_app; trivial.
    Qed.

    Lemma nnrc_impish_stmt_free_env_vars_rename_env s v v' :
      ~ In v' (nnrc_impish_stmt_bound_env_vars s) ->
      nnrc_impish_stmt_free_env_vars (nnrc_impish_stmt_rename_env s v v')
      = replace_all (nnrc_impish_stmt_free_env_vars s) v v'.
    Proof.
      nnrc_impish_stmt_cases (induction s) Case
      ; simpl
      ; intros
      ; repeat rewrite nnrc_impish_expr_free_vars_rename_env
      ; repeat rewrite IHs
      ; repeat rewrite IHs1
      ; repeat rewrite IHs2
      ; repeat rewrite IHs3
      ; repeat rewrite replace_all_app
      ; repeat rewrite in_app_iff in *
      ; intuition.
      - Case "NNRCimpishLet"%string.
        match_destr.
        + rewrite e in *; clear e v0.
          rewrite replace_all_remove_eq.
          trivial.
        + rewrite H.
          rewrite remove_replace_all_comm by congruence.
          trivial.
      - Case "NNRCimpishLetMut"%string.
        match_destr.
        + rewrite e in *; clear e v0.
          rewrite replace_all_remove_eq.
          trivial.
        + rewrite H3.
          rewrite remove_replace_all_comm by congruence.
          trivial.
      - Case "NNRCimpishLetMutColl"%string.
        match_destr.
        + rewrite e in *; clear e v0.
          rewrite replace_all_remove_eq.
          trivial.
        + rewrite H3.
          rewrite remove_replace_all_comm by congruence.
          trivial.
      - Case "NNRCimpishFor"%string.
        match_destr.
        + rewrite e in *; clear e v0.
          rewrite replace_all_remove_eq.
          trivial.
        + rewrite H.
          rewrite remove_replace_all_comm by congruence.
          trivial.
      - Case "NNRCimpishEither"%string.
        repeat match_destr; unfold equiv, complement in *; subst
        ; repeat rewrite replace_all_remove_eq; trivial.
        + rewrite H4.
          rewrite remove_replace_all_comm by congruence.
          trivial.
        + rewrite H2.
          rewrite remove_replace_all_comm by congruence.
          trivial.
        + rewrite H2, H4.
          repeat rewrite remove_replace_all_comm by congruence.
          trivial.
    Qed.

    Lemma nnrc_impish_stmt_free_env_vars_rename_env_in s v0 v v' :
      In v0 (nnrc_impish_stmt_free_env_vars (nnrc_impish_stmt_rename_env s v v')) ->
      v0 = v' \/ (v0 <> v /\ In v0 (nnrc_impish_stmt_free_env_vars s)).
    Proof.
      destruct (v0 == v')
      ; [left; trivial | ].
      intros inn; right.
      nnrc_impish_stmt_cases (induction s) Case
      ; simpl in *
      ; repeat rewrite in_app_iff in *
      ;  repeat rewrite nnrc_impish_expr_free_vars_rename_env in *.
      - intuition.
      - Case "NNRCimpishLet"%string.
        destruct inn as [inn|inn].
        + apply in_replace_all in inn.
          intuition.
        + apply remove_inv in inn.
          match_destr_in inn; unfold equiv, complement in *; subst
          ; intuition
          ; right
          ; apply remove_in_neq; tauto.
      - Case "NNRCimpishLetMut"%string.
        destruct inn as [inn|inn].
        + intuition.
        + apply remove_inv in inn.
          match_destr_in inn; unfold equiv, complement in *; subst
          ; intuition
          ; right
          ; apply remove_in_neq; tauto.
      - Case "NNRCimpishLetMutColl"%string.
        destruct inn as [inn|inn].
        + intuition.
        + apply remove_inv in inn.
          match_destr_in inn; unfold equiv, complement in *; subst
          ; intuition
          ; right
          ; apply remove_in_neq; tauto.
      - Case "NNRCimpishAssign"%string.
        apply in_replace_all in inn.
        intuition.
      - Case "NNRCimpishPush"%string.
        apply in_replace_all in inn.
        intuition.
      - Case "NNRCimpishFor"%string.
        destruct inn as [inn|inn].
        + apply in_replace_all in inn.
          intuition.
        + apply remove_inv in inn.
          match_destr_in inn; unfold equiv, complement in *; subst
          ; intuition
          ; right
          ; apply remove_in_neq; tauto.
      - Case "NNRCimpishIf"%string.
        destruct inn as [inn|[inn|inn]].
        + apply in_replace_all in inn.
          intuition.
        + intuition.
        + intuition.
      - Case "NNRCimpishEither"%string.
        destruct inn as [inn|[inn|inn]].
        + apply in_replace_all in inn.
          intuition.
        + apply remove_inv in inn.
          match_destr_in inn; unfold equiv, complement in *; subst
          ; intuition
          ; right; left
          ; apply remove_in_neq; tauto.
        + apply remove_inv in inn.
          match_destr_in inn; unfold equiv, complement in *; subst
          ; intuition
          ; right; right
          ; apply remove_in_neq; tauto.
    Qed.

    Lemma nnrc_impish_stmt_bound_env_vars_rename_env s v v' :
      nnrc_impish_stmt_bound_env_vars (nnrc_impish_stmt_rename_env s v v')
      = nnrc_impish_stmt_bound_env_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_free_mcenv_vars_rename_env s v v' :
      nnrc_impish_stmt_free_mcenv_vars (nnrc_impish_stmt_rename_env s v v')
      = nnrc_impish_stmt_free_mcenv_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_bound_mcenv_vars_rename_env s v v' :
      nnrc_impish_stmt_bound_mcenv_vars (nnrc_impish_stmt_rename_env s v v')
      = nnrc_impish_stmt_bound_mcenv_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_free_mdenv_vars_rename_env s v v' :
      nnrc_impish_stmt_free_mdenv_vars (nnrc_impish_stmt_rename_env s v v')
      = nnrc_impish_stmt_free_mdenv_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_bound_mdenv_vars_rename_env s v v' :
      nnrc_impish_stmt_bound_mdenv_vars (nnrc_impish_stmt_rename_env s v v')
      = nnrc_impish_stmt_bound_mdenv_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.  

    Lemma nnrc_impish_stmt_free_env_vars_rename_mcenv s v v' :
      nnrc_impish_stmt_free_env_vars (nnrc_impish_stmt_rename_mc s v v')
      = nnrc_impish_stmt_free_env_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_bound_env_vars_rename_mcenv s v v' :
      nnrc_impish_stmt_bound_env_vars (nnrc_impish_stmt_rename_mc s v v')
      = nnrc_impish_stmt_bound_env_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_free_mcenv_vars_rename_mcenv_in s v0 v v' :
      In v0 (nnrc_impish_stmt_free_mcenv_vars (nnrc_impish_stmt_rename_mc s v v')) ->
      v0 = v' \/ (v0 <> v /\ In v0 (nnrc_impish_stmt_free_mcenv_vars s)).
    Proof.
      destruct (v0 == v')
      ; [left; trivial | ].
      intros inn; right.
      nnrc_impish_stmt_cases (induction s) Case
      ; simpl in *
      ; repeat rewrite in_app_iff in *
      ; try solve [intuition].
      - Case "NNRCimpishLetMutColl"%string.
        destruct inn as [inn|inn].
        + apply remove_inv in inn.
          match_destr_in inn; unfold equiv, complement in *; subst
          ; intuition; left
          ; apply remove_in_neq; tauto.
        + intuition.
      - Case "NNRCimpishPush"%string.
        match_destr_in inn; intuition; congruence.
    Qed.

    Lemma nnrc_impish_stmt_bound_mcenv_vars_rename_mcenv s v v' :
      nnrc_impish_stmt_bound_mcenv_vars (nnrc_impish_stmt_rename_mc s v v')
      = nnrc_impish_stmt_bound_mcenv_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_free_mdenv_vars_rename_mcenv s v v' :
      nnrc_impish_stmt_free_mdenv_vars (nnrc_impish_stmt_rename_mc s v v')
      = nnrc_impish_stmt_free_mdenv_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_bound_mdenv_vars_rename_mcenv s v v' :
      nnrc_impish_stmt_bound_mdenv_vars (nnrc_impish_stmt_rename_mc s v v')
      = nnrc_impish_stmt_bound_mdenv_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_free_env_vars_rename_mdenv s v v' :
      nnrc_impish_stmt_free_env_vars (nnrc_impish_stmt_rename_md s v v')
      = nnrc_impish_stmt_free_env_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_bound_env_vars_rename_mdenv s v v' :
      nnrc_impish_stmt_bound_env_vars (nnrc_impish_stmt_rename_md s v v')
      = nnrc_impish_stmt_bound_env_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_free_mcenv_vars_rename_mdenv s v v' :
      nnrc_impish_stmt_free_mcenv_vars (nnrc_impish_stmt_rename_md s v v')
      = nnrc_impish_stmt_free_mcenv_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_bound_mcenv_vars_rename_mdenv s v v' :
      nnrc_impish_stmt_bound_mcenv_vars (nnrc_impish_stmt_rename_md s v v')
      = nnrc_impish_stmt_bound_mcenv_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_stmt_free_mdenv_vars_rename_mdenv_in s v0 v v' :
      In v0 (nnrc_impish_stmt_free_mdenv_vars (nnrc_impish_stmt_rename_md s v v')) ->
      v0 = v' \/ (v0 <> v /\ In v0 (nnrc_impish_stmt_free_mdenv_vars s)).
    Proof.
      destruct (v0 == v')
      ; [left; trivial | ].
      intros inn; right.
      nnrc_impish_stmt_cases (induction s) Case
      ; simpl in *
      ; repeat rewrite in_app_iff in *
      ; try solve [intuition].
      - Case "NNRCimpishLetMut"%string.
        destruct inn as [inn|inn].
        + apply remove_inv in inn.
          match_destr_in inn; unfold equiv, complement in *; subst
          ; intuition; left
          ; apply remove_in_neq; tauto.
        + intuition.
      - Case "NNRCimpishAssign"%string.
        match_destr_in inn; intuition; congruence.
    Qed.

    Lemma nnrc_impish_stmt_bound_mdenv_vars_rename_mdenv s v v' :
      nnrc_impish_stmt_bound_mdenv_vars (nnrc_impish_stmt_rename_md s v v')
      = nnrc_impish_stmt_bound_mdenv_vars s.
    Proof.
      induction s; simpl; intuition; try congruence
      ; repeat (match_destr; try congruence).
    Qed.

    
  End rename_vars.

  Section rename_eval.
    
    Lemma nnrc_impish_expr_eval_rename_env c σ e v v' d:
      ~ In v' (nnrc_impish_expr_free_vars e) ->
      nnrc_impish_expr_eval h c ((v', d) :: σ) (nnrc_impish_expr_rename_env e v v')
      = nnrc_impish_expr_eval h c ((v, d) :: σ) e.
    Proof.
      nnrc_impish_expr_cases (induction e) Case; simpl; trivial; intros nin
      ; try solve [ rewrite IHe by intuition; trivial
                  |  rewrite IHe1, IHe2 by intuition; trivial
                  ] .
      - Case "NNRCimpishVar"%string.
        intuition.
        destruct (equiv_dec v0 v)
        ; repeat (match_destr; try congruence).
    Qed.

    Lemma nnrc_impish_expr_eval_rename_env_in c l σ e v v' d:
      ~ In v (domain l) ->
      ~ In v' (domain l) ->
      ~ In v' (nnrc_impish_expr_free_vars e) ->
      nnrc_impish_expr_eval h c (l++(v', d) :: σ) (nnrc_impish_expr_rename_env e v v')
      = nnrc_impish_expr_eval h c (l++(v, d) :: σ) e.
    Proof.
      nnrc_impish_expr_cases (induction e) Case; simpl; trivial
      ; repeat rewrite in_app_iff; intros
      ; try solve [ rewrite IHe by intuition; trivial
                  |  rewrite IHe1, IHe2 by intuition; trivial
                  ].
      - Case "NNRCimpishVar"%string.
        intuition.
        repeat rewrite lookup_app.
        destruct (equiv_dec v0 v); unfold equiv, complement in *
        ; subst.
        + repeat match_option
          ; (try apply lookup_in_domain in eqq
             ; try apply lookup_in_domain in eqq0; try contradiction).
          simpl.
          repeat match_destr; congruence.
        + match_destr; simpl.
          repeat match_destr; congruence.
    Qed.

    Ltac disect_tac H stac
      := 
        unfold var in *
        ; cut_to H; unfold domain in *; [ | solve[stac]..]
        ; unfold lift2P in H
        ; (repeat match_option_in H; try contradiction).

    Ltac rename_inv_tac1 stac
      :=    unfold var in *
            ; repeat rewrite or_assoc
            ; try match goal with
                  | [ H: domain (_ ++ _) = domain _ |- _ ] =>
                    rewrite domain_app in H
                    ; unfold domain in H
                    ; symmetry in H; apply map_app_break in H
                    ; destruct H as [? [?[?[??]]]]; subst; simpl in *
                  | [ H: map (_ ++ _) = map _ |- _ ] =>
                    rewrite map_app in H
                    ; symmetry in H; apply map_app_break in H
                    ; destruct H as [? [?[?[??]]]]; subst; simpl in *
                  | [ H: _ :: _ = map _ ?x |- _ ] =>
                    destruct x; try discriminate; simpl in H; invcs H
                  | [ H: _ :: _ = domain ?x |- _ ] =>
                    destruct x; try discriminate; simpl in H; invcs H
                  | [H: _ * _ * _ |- _ ] => destruct H as [[??]?]; simpl in *
                  | [H: _ * _ |- _ ] => destruct H as [??]; simpl in *
                  | [H : nnrc_impish_stmt_eval _ _ ?p1 _ _ _ = Some (?p2,_,_) |- _ ] =>
                    match p1 with
                    | p2 => fail 1
                    | _ => generalize (nnrc_impish_stmt_eval_domain_stack H)
                           ; intros [?[??]]
                    end
                  | [H: ~ (_ \/ _) |- _] => apply not_or in H
                  | [H: _ /\ _ |- _ ] => destruct H
                  | [H: ?x = ?x |- _] => clear H
                  | [ H: forall a b c, _ -> ?x :: ?x1 ++ ?dd :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                    specialize (H (x::x1) (snd dd) x2); simpl in H
                    ; match dd with
                      | (_,_) => idtac
                      | _ => destruct dd
                      end
                    ; simpl in *
                    ; cut_to H; [ | eauto 3 | reflexivity]
                  | [ H: forall a b c, _ -> ?x1 ++ ?dd :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                    specialize (H x1 (snd dd) x2)
                    ; match dd with
                      | (_,_) => idtac
                      | _ => destruct dd
                      end
                    ; simpl in *
                    ; cut_to H; [ | eauto 3 | reflexivity]
                  | [H : ?x ++ _ = ?y ++ _ |- _ ] =>
                    let HH := fresh in
                    assert (HH:domain y = domain x) by (unfold domain in *; intuition congruence)
                    ; apply app_inv_head_domain in H;[clear HH|apply HH]
                  | [H: _ :: _ = _ :: _ |- _] => invcs H
                  | [H: ?x = (_,_) |- _ ] =>
                    match x with
                    | (_,_) => idtac
                    | _ => destruct x; simpl in H
                    end
                    ; invcs H
                  | [H: (_,_) = ?x |- _ ] =>
                    match x with
                    | (_,_) => fail 1
                    | _ => destruct x; simpl in H
                    end
                    ; invcs H
                  | [|- _ /\ _ ] => try split; [| tauto]
                  | [ |- lift2P _ (match ?x with
                                     _ => _
                                   end)
                                (match ?x with
                                   _ => _
                                 end) ] => destruct x; try reflexivity
                  | [H:forall l es ec ed d,
                        _ -> _ -> _ -> _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                                   
                        |- lift2P _ (nnrc_impish_stmt_eval _ _ (?l ++ (_, ?d) :: ?σ) ?ψc ?ψd ?s)
                                  _ ] => specialize (H l σ ψc ψd d)
                                         ; disect_tac H stac
                                                      
                  | [H:forall l es ec ed d,
                        _ -> _ -> _ -> _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                                   
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ (?l ++ (_, ?d) :: ?σ) ?ψc ?ψd ?s with
                                     | Some _ => _
                                     | None => _
                                     end) _ ] => specialize (H l σ ψc ψd d)
                                                 ; disect_tac H stac
                  | [H:forall l es ec ed d,
                        _ -> _ -> _ -> _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                                   
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ (?x :: ?l ++ (_, ?d) :: ?σ) ?ψc ?ψd ?s with| Some _ => _
                                                                                                            | None => _
                                     end) _ ] => specialize (H (x::l) σ ψc ψd d); simpl in H
                                                 ; disect_tac H stac
                  | [H:forall l es ec ed d,
                        _ -> _ -> _ -> _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                                   
                        |- lift2P _ (nnrc_impish_stmt_eval _ _ ?σ ?ψc (?l ++ (_, ?d) :: ?ψd) ?s)
                                  _ ] => specialize (H l σ ψc ψd d)
                                         ; disect_tac H stac
                                                      
                  | [H:forall l es ec ed d,
                        _ -> _ -> _ -> _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                                   
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ ?σ ?ψc (?l ++ (_, ?d) :: ?ψd) ?s with
                                     | Some _ => _
                                     | None => _
                                     end) _ ] => specialize (H l σ ψc ψd d)
                                                 ; disect_tac H stac
                  | [H:forall l es ec ed d,
                        _ -> _ -> _ -> _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                                   
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ ?σ ?ψc (?x::?l ++ (_, ?d) :: ?ψd)?s with
                                     | Some _ => _
                                     | None => _
                                     end) _ ] => specialize (H (x::l) σ ψc ψd d); simpl in H
                                                 ; disect_tac H stac
                  | [H:forall l es ec ed d,
                        _ -> _ -> _ -> _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                                   
                        |- lift2P _ (nnrc_impish_stmt_eval _ _ ?σ (?l ++ (_, ?d) :: ?ψc) ?ψd ?s)
                                  _ ] => specialize (H l σ ψc ψd d)
                                         ; disect_tac H stac
                                                      
                  | [H:forall l es ec ed d,
                        _ -> _ -> _ -> _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                                   
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ ?σ (?l ++ (_, ?d) :: ?ψc) ?ψd ?s with
                                     | Some _ => _
                                     | None => _
                                     end) _ ] => specialize (H l σ ψc ψd d)
                                                 ; disect_tac H stac
                  | [H:forall l es ec ed d,
                        _ -> _ -> _ -> _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                                   
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ ?σ (?x::?l ++ (_, ?d) :: ?ψc) ?ψd ?s  with
                                     | Some _ => _
                                     | None => _
                                     end) _ ] => specialize (H (x::l) σ ψc ψd d); simpl in H
                                                 ; disect_tac H stac

                  | [H:forall l es ec ed d,
                        _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                    
                        |- lift2P _ (nnrc_impish_stmt_eval _ _ (?l ++ (_, ?d) :: ?σ) ?ψc ?ψd ?s)
                                  _ ] => specialize (H l σ ψc ψd d)
                                         ; disect_tac H stac

                  | [H:forall l es ec ed d,
                        _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                    
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ (?l ++ (_, ?d) :: ?σ) ?ψc ?ψd ?s with
                                     | Some _ => _
                                     | None => _
                                     end) _ ] => specialize (H l σ ψc ψd d)
                                                 ; disect_tac H stac
                  | [H:forall l es ec ed d,
                        _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                    
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ (?x :: ?l ++ (_, ?d) :: ?σ) ?ψc ?ψd ?s with
                                     | Some _ => _
                                     | None => _
                                     end) _ ] => specialize (H (x::l) σ ψc ψd d); simpl in H
                                                 ; disect_tac H stac
                  | [H:forall l es ec ed d, 
                        _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                    
                        |- lift2P _ (nnrc_impish_stmt_eval _ _ ?σ ?ψc (?l ++ (_, ?d) :: ?ψd) ?s)
                                  _ ] => specialize (H l σ ψc ψd d)
                                         ; disect_tac H stac

                  | [H:forall l es ec ed d, 
                        _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                    
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ ?σ ?ψc (?l ++ (_, ?d) :: ?ψd) ?s with
                                     | Some _ => _
                                     | None => _
                                     end) _ ] => specialize (H l σ ψc ψd d)
                                                 ; disect_tac H stac
                  | [H:forall l es ec ed d, 
                        _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                    
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ ?σ ?ψc (?x::?l ++ (_, ?d) :: ?ψd) ?s with
                                     | Some _ => _
                                     | None => _
                                     end) _ ] => specialize (H (x::l) σ ψc ψd d); simpl in H
                                                 ; disect_tac H stac
                  | [H:forall l es ec ed d, 
                        _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                    
                        |- lift2P _ (nnrc_impish_stmt_eval _ _ ?σ (?l ++ (_, ?d) :: ?ψc) ?ψd ?s)
                                  _ ] => specialize (H l σ ψc ψd d)
                                         ; disect_tac H stac

                  | [H:forall l es ec ed d, 
                        _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                    
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ ?σ (?l ++ (_, ?d) :: ?ψc) ?ψd ?s with
                                     | Some _ => _
                                     | None => _
                                     end) _ ] => specialize (H l σ ψc ψd d)
                                                 ; disect_tac H stac
                  | [H:forall l es ec ed d, 
                        _ -> lift2P _ (nnrc_impish_stmt_eval _ _ _ _ _ ?s) _
                                    
                        |- lift2P _ (match nnrc_impish_stmt_eval _ _ ?σ (?x::?l ++ (_, ?d) :: ?ψc) ?ψd ?s with
                                     | Some _ => _
                                     | None => _
                                     end) _ ] => specialize (H (x::l) σ ψc ψd d); simpl in H
                                                 ; disect_tac H stac

                                                              
                  | [H : ~ In _ (remove equiv_dec _ _) |- _ ] =>
                    apply not_in_remove_impl_not_in in H; [| congruence]
                  | [H : In _ (remove equiv_dec _ _) -> False |- _ ] =>
                    apply not_in_remove_impl_not_in in H; [| congruence]
                  | [H1: ?x = Some ?y,
                         H2: ?x = Some ?z |- _ ] =>
                    rewrite H1 in H2; invcs H2
                  | [|- ?x = ?y \/ _ ] => destruct (x == y); unfold equiv, complement in *
                                          ; [left; trivial | right]
                  end
            ; try subst; simpl in *; intros
            ; try congruence
    .
    Ltac unused_inv_tac := repeat progress (try rename_inv_tac1 ltac:( unused_inv_tac ; intuition unused_inv_tac); try rewrite nnrc_impish_expr_eval_unused_env by tauto).

    Ltac rename_inv_extra_tac
      := match goal with
         | [|- context [nnrc_impish_stmt_eval ?h ?c ((?v1, ?d1) :: ?l ++ (?v2, ?d2) :: ?σ) ?ψc ?ψd ?s ]] =>
           let HH := fresh in
           generalize (nnrc_impish_stmt_eval_unused_env h c ((v1,d1)::l) σ ψc ψd s v2 d2); simpl; intros HH; (cut_to HH; [|tauto])
           ; unfold lift2P in HH
           ; unfold var in *
           ; repeat match_option_in HH
         | [|- context [nnrc_impish_stmt_eval ?h ?c ?σ ?ψc ((?v1, ?d1) :: ?l ++ (?v2, ?d2) :: ?ψd) ?s ]] =>
           let HH := fresh in
           generalize (nnrc_impish_stmt_eval_unused_mdenv h c ((v1,d1)::l) σ ψc ψd s v2 d2); simpl; intros HH; (cut_to HH; [|tauto])
           ; unfold lift2P in HH
           ; unfold var in *
           ; repeat match_option_in HH
         | [|- context [nnrc_impish_stmt_eval ?h ?c ?σ ((?v1, ?d1) :: ?l ++ (?v2, ?d2) :: ?ψc) ?ψd ?s ]] =>
           let HH := fresh in
           generalize (nnrc_impish_stmt_eval_unused_mcenv h c ((v1,d1)::l) σ ψc ψd s v2 d2); simpl; intros HH; (cut_to HH; [|tauto])
           ; unfold lift2P in HH
           ; unfold var in *
           ; repeat match_option_in HH
         end.

    Ltac rename_inv_tac := repeat progress (
                                    try rename_inv_tac1 ltac:( intuition congruence ; intuition unused_inv_tac)
                                    ; try rename_inv_extra_tac
                                    ; repeat rewrite nnrc_impish_expr_eval_rename_env_in by tauto).


    Lemma nnrc_impish_stmt_eval_rename_env_in c l σ ψc ψd s (v v':var) d :
      ~ In v (domain l) ->
      ~ In v' (domain l) ->
      ~ In v' (nnrc_impish_stmt_free_env_vars s) ->
      ~ In v' (nnrc_impish_stmt_bound_env_vars s) ->
      lift2P  (fun '(σ₁', ψc₁', ψd₁') '(σ₂', ψc₂', ψd₂') =>
                 (forall l' d σ'',
                     domain l' = domain l ->
                     σ₁' = l' ++ (v',d)::σ'' ->
                     σ₂' = l' ++ (v,d)::σ'')
                 /\ ψc₁' = ψc₂'
                 /\ ψd₁' = ψd₂'
              )
              (nnrc_impish_stmt_eval h c (l++(v',d)::σ) ψc ψd (nnrc_impish_stmt_rename_env s v v'))
              (nnrc_impish_stmt_eval h c (l++(v,d)::σ) ψc ψd s).
    Proof.
      revert l σ ψc ψd d
      ; nnrc_impish_stmt_cases (induction s) Case
      ; simpl; intros l σ ψc ψd d ninl ninl' nine ninb
      ; repeat rewrite in_app_iff in nine
      ; repeat rewrite in_app_iff in ninb
      ; rename_inv_tac
      ; try solve [dest_eqdec; rename_inv_tac].
      - Case "NNRCimpishFor"%string.
        dest_eqdec.
        + revert σ ψc ψd d.
          { induction l0; intros σ ψc ψd d; simpl.
            - rename_inv_tac.
            - unfold lift2P.
              generalize (nnrc_impish_stmt_eval_unused_env h c ((v,Some a)::l) σ ψc ψd s v' d); simpl; intros eqs1.
              cut_to eqs1; [|tauto].
              generalize (nnrc_impish_stmt_eval_unused_env h c ((v,Some a)::l) σ ψc ψd s v d); simpl; intros eqs2.
              cut_to eqs2; [|tauto].
              unfold lift2P in *.
              unfold var in *.
              { repeat match_option_in eqs1
                ; try contradiction
                ; repeat match_option_in eqs2
                ; destruct p as [[??]?]
                ; try contradiction
                ; destruct p0 as [[??]?]
                ; try congruence.
                rename_inv_tac.
                specialize (IHl0 σ m3 m4 d).
                repeat match_option_in IHl0
                ; try contradiction.
              }
          }
        + revert σ ψc ψd d.
          { induction l0; intros σ ψc ψd d; simpl.
            - rename_inv_tac. 
            - unfold lift2P.
              specialize (IHs ((v0, Some a)::l) σ ψc ψd d).
              cut_to IHs; simpl; try tauto.
              unfold lift2P in *; simpl in *.
              repeat match_option_in IHs
              ; try contradiction.
              rename_inv_tac.
              specialize (IHl0 σ m m0 d).
              repeat match_option_in IHl0
              ; try contradiction.
          }
    Qed.

    Lemma nnrc_impish_stmt_eval_rename_mdenv_in c l σ ψc ψd s (v v':var) d :
      ~ In v (domain l) ->
      ~ In v' (domain l) ->
      ~ In v' (nnrc_impish_stmt_free_mdenv_vars s) ->
      ~ In v' (nnrc_impish_stmt_bound_mdenv_vars s) ->
      lift2P  (fun '(σ₁', ψc₁', ψd₁') '(σ₂', ψc₂', ψd₂') =>
                 (forall l' d ψd'',
                     domain l' = domain l ->
                     ψd₁' = l' ++ (v',d)::ψd'' ->
                     ψd₂' = l' ++ (v,d)::ψd'')
                 /\ σ₁' = σ₂'
                 /\ ψc₁' = ψc₂'
              )
              (nnrc_impish_stmt_eval h c σ ψc (l++(v',d)::ψd) (nnrc_impish_stmt_rename_md s v v'))
              (nnrc_impish_stmt_eval h c σ ψc (l++(v,d)::ψd) s).
    Proof.
      revert l σ ψc ψd d
      ; nnrc_impish_stmt_cases (induction s) Case
      ; simpl; intros l σ ψc ψd d ninl ninl' nine ninb
      ; repeat rewrite in_app_iff in nine
      ; repeat rewrite in_app_iff in ninb
      ; rename_inv_tac
      ; try solve [dest_eqdec; rename_inv_tac].
      - Case "NNRCimpishLetMut"%string.
        dest_eqdec.
        + repeat match goal with
                   [|- context [nnrc_impish_stmt_eval ?h ?c ?σ ?ψc ((?v1, ?d1) :: ?l ++ (?v2, ?d2) :: ?ψd) ?s ]] =>
                   let HH := fresh in
                   generalize (nnrc_impish_stmt_eval_unused_mdenv h c ((v1,d1)::l) σ ψc ψd s v2 d2); simpl; intros HH; (cut_to HH; [|tauto])
                   ; unfold lift2P in HH
                   ; unfold var in *
                   ; repeat match_option_in HH
                 end; try contradiction; try congruence.
          rewrite eqq0 in eqq2.
          invcs eqq2.
          rename_inv_tac; unfold domain in *; try congruence.
        + rename_inv_tac.
      - Case "NNRCimpishAssign"%string.
        repeat rewrite lookup_app; simpl.
        dest_eqdec.
        + rewrite (lookup_nin_none string_dec ninl).
          rewrite (lookup_nin_none string_dec ninl').
          repeat rewrite update_app_nin by trivial; simpl.
          destruct (string_dec v v); try congruence.
          destruct (string_dec v' v'); try congruence.
          simpl; repeat split; trivial; intros.
          rename_inv_tac.
        + destruct (string_dec v0 v'); try congruence.
          case_eq (lookup string_dec l v0); simpl; [intros ? inn | intros inn].
          * repeat split; trivial; intros ???? eqq.
            generalize (lookup_in_domain _ _ inn); intros.
            rewrite update_app_in in eqq |- * by trivial.
            apply app_inv_head_domain in eqq
            ; [| rewrite domain_update_first; trivial].
            destruct eqq as [eqq1 eqq2].
            invcs eqq2.
            congruence.
          * generalize (lookup_none_nin _ inn); intros.
            repeat rewrite update_app_nin by trivial.
            simpl.
            destruct (string_dec v0 v); try congruence.
            destruct (string_dec v0 v'); try congruence.
            match_destr; simpl; trivial.
            repeat split; trivial; intros ???? eqq.
            apply app_inv_head_domain in eqq; [| trivial].
            destruct eqq as [eqq1 eqq2].
            invcs eqq2.
            congruence.
      - Case "NNRCimpishFor"%string.
        revert l σ ψc ψd d ninl ninl'.
        induction l0; intros l σ ψc ψd d ninl ninl' ; simpl.
        + rename_inv_tac. 
        + unfold lift2P.
          specialize (IHs l ((v0, Some a)::σ) ψc ψd d).
          cut_to IHs; simpl; try tauto.
          unfold lift2P in *; simpl in *.
          repeat match_option_in IHs
          ; try contradiction.
          rename_inv_tac.
          specialize (IHl0 x1 σ m x2 o0).
          cut_to IHl0; unfold domain in *; try congruence.
          repeat match_option_in IHl0
          ; try contradiction.
          rename_inv_tac.
    Qed.
    
    Lemma nnrc_impish_stmt_eval_rename_mcenv_in c l σ ψc ψd s (v v':var) d :
      ~ In v (domain l) ->
      ~ In v' (domain l) ->
      ~ In v' (nnrc_impish_stmt_free_mcenv_vars s) ->
      ~ In v' (nnrc_impish_stmt_bound_mcenv_vars s) ->
      lift2P  (fun '(σ₁', ψc₁', ψd₁') '(σ₂', ψc₂', ψd₂') =>
                 (forall l' d ψc'',
                     domain l' = domain l ->
                     ψc₁' = l' ++ (v',d)::ψc'' ->
                     ψc₂' = l' ++ (v,d)::ψc'')
                 /\ σ₁' = σ₂'
                 /\ ψd₁' = ψd₂'
              )
              (nnrc_impish_stmt_eval h c σ (l++(v',d)::ψc) ψd (nnrc_impish_stmt_rename_mc s v v'))
              (nnrc_impish_stmt_eval h c σ (l++(v,d)::ψc) ψd s).
    Proof.
      revert l σ ψc ψd d
      ; nnrc_impish_stmt_cases (induction s) Case
      ; simpl; intros l σ ψc ψd d ninl ninl' nine ninb
      ; repeat rewrite in_app_iff in nine
      ; repeat rewrite in_app_iff in ninb
      ; rename_inv_tac
      ; try solve [dest_eqdec; rename_inv_tac].
      - Case "NNRCimpishLetMutColl"%string.
        dest_eqdec.
        + repeat match goal with
                   [|- context [nnrc_impish_stmt_eval ?h ?c ?σ ((?v1, ?d1) :: ?l ++ (?v2, ?d2) :: ?ψc) ?ψd ?s ]] =>
                   let HH := fresh in
                   generalize (nnrc_impish_stmt_eval_unused_mcenv h c ((v1,d1)::l) σ ψc ψd s v2 d2); simpl; intros HH; (cut_to HH; [|tauto])
                   ; unfold lift2P in HH
                   ; unfold var in *
                   ; repeat match_option_in HH
                 end; try contradiction; try congruence.
          rewrite eqq0 in eqq2.
          invcs eqq2.
          rename_inv_tac; unfold domain in *; try congruence.
        + rename_inv_tac.
      - Case "NNRCimpishPush"%string.
        repeat rewrite lookup_app; simpl.
        dest_eqdec.
        + rewrite (lookup_nin_none string_dec ninl).
          rewrite (lookup_nin_none string_dec ninl').
          destruct (string_dec v v); try congruence.
          destruct (string_dec v' v'); try congruence.
          repeat rewrite update_app_nin by trivial; simpl.
          destruct (string_dec v v); try congruence.
          destruct (string_dec v' v'); try congruence.
          simpl; repeat split; trivial; intros.
          rename_inv_tac.
        + destruct (string_dec v0 v'); try congruence.
          case_eq (lookup string_dec l v0); simpl; [intros ? inn | intros inn].
          * repeat split; trivial; intros ???? eqq.
            generalize (lookup_in_domain _ _ inn); intros.
            rewrite update_app_in in eqq |- * by trivial.
            apply app_inv_head_domain in eqq
            ; [| rewrite domain_update_first; trivial].
            destruct eqq as [eqq1 eqq2].
            invcs eqq2.
            congruence.
          * generalize (lookup_none_nin _ inn); intros.
            simpl.
            destruct (string_dec v0 v); try congruence.
            destruct (string_dec v0 v'); try congruence.
            match_destr; simpl; trivial.
            repeat rewrite update_app_nin by trivial.
            simpl.
            repeat split; trivial; intros ???? eqq.
            apply app_inv_head_domain in eqq; [| trivial].
            destruct eqq as [eqq1 eqq2].
            invcs eqq2.
            destruct (string_dec v0 v); try congruence.
            destruct (string_dec v0 v'); try congruence.
      - Case "NNRCimpishFor"%string.
        revert l σ ψc ψd d ninl ninl'.
        induction l0; intros l σ ψc ψd d ninl ninl' ; simpl.
        + rename_inv_tac. 
        + unfold lift2P.
          specialize (IHs l ((v0, Some a)::σ) ψc ψd d).
          cut_to IHs; simpl; try tauto.
          unfold lift2P in *; simpl in *.
          repeat match_option_in IHs
          ; try contradiction.
          rename_inv_tac.
          specialize (IHl0 x1 σ x2 m0 l2).
          cut_to IHl0; unfold domain in *; try congruence.
          repeat match_option_in IHl0
          ; try contradiction.
          rename_inv_tac.
    Qed.
    
    Lemma nnrc_impish_stmt_eval_rename_env c σ ψc ψd s v v' d:
      ~ In v' (nnrc_impish_stmt_free_env_vars s) ->
      ~ In v' (nnrc_impish_stmt_bound_env_vars s) ->
      nnrc_impish_stmt_eval h c ((v',d)::σ) ψc ψd 
                            (nnrc_impish_stmt_rename_env s v v') =
      match nnrc_impish_stmt_eval h c ((v,d)::σ) ψc ψd s with
      | Some ((_,d)::σ',ψc',ψd') => Some ((v',d)::σ',ψc',ψd')
      | _ => None
      end.
    Proof.
      intros.
      generalize (nnrc_impish_stmt_eval_rename_env_in c nil σ ψc ψd s v v' d); simpl; intros HH.
      cut_to HH; try tauto.
      unfold lift2P in *.
      repeat match_option_in HH
      ; try contradiction.
      rename_inv_tac; trivial.
    Qed.
    

    Lemma nnrc_impish_stmt_eval_rename_mdenv c σ ψc ψd s v v' d:
      ~ In v' (nnrc_impish_stmt_free_mdenv_vars s) ->
      ~ In v' (nnrc_impish_stmt_bound_mdenv_vars s) ->
      nnrc_impish_stmt_eval h c σ ψc ((v',d)::ψd)
                            (nnrc_impish_stmt_rename_md s v v') =
      match nnrc_impish_stmt_eval h c σ ψc ((v,d)::ψd) s with
      | Some (σ',ψc',(_,d)::ψd') => Some (σ',ψc',(v',d)::ψd')
      | _ => None
      end.
    Proof.
      intros.
      generalize (nnrc_impish_stmt_eval_rename_mdenv_in c nil σ ψc ψd s v v' d); simpl; intros HH.
      cut_to HH; try tauto.
      unfold lift2P in *.
      repeat match_option_in HH
      ; try contradiction.
      rename_inv_tac; trivial.
      specialize (H1 nil o0 m2).
      cut_to H1; simpl; try congruence.
      invcs H1; trivial.
    Qed.

    Lemma nnrc_impish_stmt_eval_rename_mcenv c σ ψc ψd s v v' d:
      ~ In v' (nnrc_impish_stmt_free_mcenv_vars s) ->
      ~ In v' (nnrc_impish_stmt_bound_mcenv_vars s) ->
      nnrc_impish_stmt_eval h c σ ((v',d)::ψc) ψd
                            (nnrc_impish_stmt_rename_mc s v v') =
      match nnrc_impish_stmt_eval h c σ ((v,d)::ψc) ψd s with
      | Some (σ',(_,d)::ψc',ψd') => Some (σ',(v',d)::ψc',ψd')
      | _ => None
      end.
    Proof.
      intros.
      generalize (nnrc_impish_stmt_eval_rename_mcenv_in c nil σ ψc ψd s v v' d); simpl; intros HH.
      cut_to HH; try tauto.
      unfold lift2P in *.
      repeat match_option_in HH
      ; try contradiction.
      rename_inv_tac; trivial.
      specialize (H1 nil l0 m1).
      cut_to H1; simpl; try congruence.
      invcs H1; trivial.
    Qed.
    
  End rename_eval.

  Section core.

    Lemma nnrc_impish_expr_rename_env_core e v v' :
      nnrc_impish_exprIsCore (nnrc_impish_expr_rename_env e v v') <->
      nnrc_impish_exprIsCore e.
    Proof.
      induction e; simpl; intuition.
    Qed.

    Lemma nnrc_impish_stmt_rename_env_core_f s v v' :
      nnrc_impish_stmtIsCore s ->
      nnrc_impish_stmtIsCore (nnrc_impish_stmt_rename_env s v v').
    Proof.
      nnrc_impish_stmt_cases (induction s) Case
      ; simpl; intros isc.
      - Case "NNRCimpishSeq"%string.
        intuition.
      - Case "NNRCimpishLet"%string.
        destruct isc as [isc1 isc2]; split; trivial.
        + apply nnrc_impish_expr_rename_env_core; trivial.
        + match_destr; intuition.
      - Case "NNRCimpishLetMut"%string.
        destruct isc as [isc1 isc2]; split; trivial.
        + intuition.
        + match_destr; intuition.
      - Case "NNRCimpishLetMutColl"%string.
        destruct isc as [isc1 isc2]; split; trivial.
        + intuition.
        + match_destr; intuition.
      - Case "NNRCimpishAssign"%string.
        apply nnrc_impish_expr_rename_env_core; trivial.
      - Case "NNRCimpishPush"%string.
        apply nnrc_impish_expr_rename_env_core; trivial.
      - Case "NNRCimpishFor"%string.
        destruct isc as [isc1 isc2]; split; trivial.
        + apply nnrc_impish_expr_rename_env_core; trivial.
        + match_destr; intuition.
      - Case "NNRCimpishIf"%string.
        destruct isc as [isc1 [isc2 isc3]]; split; trivial.
        + apply nnrc_impish_expr_rename_env_core; trivial.
        + split; intuition.
      - Case "NNRCimpishEither"%string.
        destruct isc as [isc1 [isc2 isc3]]; split; trivial.
        + apply nnrc_impish_expr_rename_env_core; trivial.
        + split; match_destr; intuition.
    Qed.

    Lemma nnrc_impish_stmt_rename_env_core_b s v v' :
      nnrc_impish_stmtIsCore (nnrc_impish_stmt_rename_env s v v') ->
      nnrc_impish_stmtIsCore s.
    Proof.
      nnrc_impish_stmt_cases (induction s) Case
      ; simpl; intros isc.
      - Case "NNRCimpishSeq"%string.
        intuition.
      - Case "NNRCimpishLet"%string.
        destruct isc as [isc1 isc2].
        split.
        + eapply nnrc_impish_expr_rename_env_core; eauto.
        + match_destr_in isc2; intuition.
      - Case "NNRCimpishLetMut"%string.
        destruct isc as [isc1 isc2]; split; trivial.
        + intuition.
        + match_destr_in isc2; intuition.
      - Case "NNRCimpishLetMutColl"%string.
        destruct isc as [isc1 isc2]; split; trivial.
        + intuition.
        + match_destr_in isc2; intuition.
      - Case "NNRCimpishAssign"%string.
        eapply nnrc_impish_expr_rename_env_core; eauto.
      - Case "NNRCimpishPush"%string.
        eapply nnrc_impish_expr_rename_env_core; eauto.
      - Case "NNRCimpishFor"%string.
        destruct isc as [isc1 isc2]; split; trivial.
        + eapply nnrc_impish_expr_rename_env_core; eauto.
        + match_destr_in isc2; intuition.
      - Case "NNRCimpishIf"%string.
        destruct isc as [isc1 [isc2 isc3]]; split; trivial.
        + eapply nnrc_impish_expr_rename_env_core; eauto.
        + split; intuition.
      - Case "NNRCimpishEither"%string.
        destruct isc as [isc1 [isc2 isc3]]; split; trivial.
        + eapply nnrc_impish_expr_rename_env_core; eauto.
        + split.
          * match_destr_in isc2; intuition.
          * match_destr_in isc3; intuition.
    Qed.

    Lemma nnrc_impish_stmt_rename_env_core s v v' :
      nnrc_impish_stmtIsCore (nnrc_impish_stmt_rename_env s v v') <->
      nnrc_impish_stmtIsCore s.
    Proof.
      split.
      - apply nnrc_impish_stmt_rename_env_core_b.
      - apply nnrc_impish_stmt_rename_env_core_f.
    Qed.

    Lemma nnrc_impish_stmt_rename_mc_core s v v' :
      nnrc_impish_stmtIsCore (nnrc_impish_stmt_rename_mc s v v') <->
      nnrc_impish_stmtIsCore s.
    Proof.
      nnrc_impish_stmt_cases (induction s) Case
      ; simpl; intuition.
      - match_destr_in H4; intuition.
      - match_destr; intuition.
    Qed.

    Lemma nnrc_impish_stmt_rename_md_core s v v' :
      nnrc_impish_stmtIsCore (nnrc_impish_stmt_rename_md s v v') <->
      nnrc_impish_stmtIsCore s.
    Proof.
      nnrc_impish_stmt_cases (induction s) Case
      ; simpl; intuition.
      - match_destr_in H4; intuition.
      - match_destr; intuition.
    Qed.

  End core.

End NNRCimpishRename.

Hint Rewrite
     @nnrc_impish_stmt_bound_env_vars_rename_env 
     @nnrc_impish_stmt_free_mcenv_vars_rename_env 
     @nnrc_impish_stmt_bound_mcenv_vars_rename_env 
     @nnrc_impish_stmt_free_mdenv_vars_rename_env 
     @nnrc_impish_stmt_bound_mdenv_vars_rename_env 
     
     @nnrc_impish_stmt_free_env_vars_rename_mcenv 
     @nnrc_impish_stmt_bound_env_vars_rename_mcenv 
     @nnrc_impish_stmt_bound_mcenv_vars_rename_mcenv 
     @nnrc_impish_stmt_free_mdenv_vars_rename_mcenv 
     @nnrc_impish_stmt_bound_mdenv_vars_rename_mcenv 
     
     @nnrc_impish_stmt_free_env_vars_rename_mdenv 
     @nnrc_impish_stmt_bound_env_vars_rename_mdenv 
     @nnrc_impish_stmt_free_mcenv_vars_rename_mdenv 
     @nnrc_impish_stmt_bound_mcenv_vars_rename_mdenv 
     @nnrc_impish_stmt_bound_mdenv_vars_rename_mdenv : nnrc_impish_rename.