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
Require Import NNRSimp.
Require Import NNRSimpVars.
Require Import NNRSimpUsage.
Require Import NNRSimpEval.

Section NNRSimpRename.

  Context {fruntime:foreign_runtime}.

  Fixpoint nnrs_imp_expr_rename (e:nnrs_imp_expr) (from to:var) : nnrs_imp_expr
    := match e with 
       | NNRSimpGetConstant c =>
         NNRSimpGetConstant c
       | NNRSimpVar v =>
         NNRSimpVar (if v == from then to else v)
       | NNRSimpConst d =>
         NNRSimpConst d
       | NNRSimpBinop b e₁ e₂ =>
         NNRSimpBinop b
                      (nnrs_imp_expr_rename e₁ from to)
                      (nnrs_imp_expr_rename e₂ from to)
       | NNRSimpUnop u e₁ =>
         NNRSimpUnop u
                     (nnrs_imp_expr_rename e₁ from to)
       | NNRSimpGroupBy g sl e₁ =>
         NNRSimpGroupBy g sl
                        (nnrs_imp_expr_rename e₁ from to)
       end.

  Fixpoint nnrs_imp_stmt_rename (s:nnrs_imp_stmt) (from to:var) : nnrs_imp_stmt
    := match s with
       | NNRSimpSkip =>
         NNRSimpSkip
       | NNRSimpSeq s₁ s₂ =>
         NNRSimpSeq
           (nnrs_imp_stmt_rename s₁ from to)
           (nnrs_imp_stmt_rename s₂ from to)
       | NNRSimpAssign v e =>
         NNRSimpAssign
           (if v == from then to else v)
           (nnrs_imp_expr_rename e from to)
       | NNRSimpLet v eo s₀ =>
         NNRSimpLet v 
                    (match eo with
                     | None => None
                     | Some e => Some (nnrs_imp_expr_rename e from to)
                     end)
                    (if v == from
                     then s₀
                     else nnrs_imp_stmt_rename s₀ from to)
       | NNRSimpFor v e s₀ =>
         NNRSimpFor v
                    (nnrs_imp_expr_rename e from to)
                    (if v == from
                     then s₀
                     else nnrs_imp_stmt_rename s₀ from to)
       | NNRSimpIf e s₁ s₂ =>
         NNRSimpIf
           (nnrs_imp_expr_rename e from to)
           (nnrs_imp_stmt_rename s₁ from to)
           (nnrs_imp_stmt_rename s₂ from to)
       | NNRSimpEither e x₁ s₁ x₂ s₂ =>
         NNRSimpEither
           (nnrs_imp_expr_rename e from to)
           x₁
           (if x₁ == from
            then s₁
            else nnrs_imp_stmt_rename s₁ from to)
           x₂
           (if x₂ == from
            then s₂
            else nnrs_imp_stmt_rename s₂ from to)
       end.

  Section vars.

    Lemma nnrs_imp_stmt_rename_bound_vars
          (s:nnrs_imp_stmt) (from to:var) :
      nnrs_imp_stmt_bound_vars (nnrs_imp_stmt_rename s from to)
      = nnrs_imp_stmt_bound_vars s.
    Proof.
      induction s; simpl; try congruence
      ; repeat (match_destr; try congruence).
    Qed.
    
    Lemma nnrs_imp_expr_rename_free_vars
          (e:nnrs_imp_expr) (from to:var) :
      nnrs_imp_expr_free_vars (nnrs_imp_expr_rename e from to)
      = replace_all (nnrs_imp_expr_free_vars e) from to.
    Proof.
      induction e; simpl; trivial.
      rewrite IHe1, IHe2, replace_all_app; trivial.
    Qed.

    Lemma nnrs_imp_stmt_rename_free_vars
          (s:nnrs_imp_stmt) (from to:var) :
      ~ In to (nnrs_imp_stmt_bound_vars s) ->
      nnrs_imp_stmt_free_vars (nnrs_imp_stmt_rename s from to)
      = replace_all (nnrs_imp_stmt_free_vars s) from to.
    Proof.
      induction s; simpl; repeat rewrite in_app_iff; intros inn; trivial
      ; repeat rewrite nnrs_imp_expr_rename_free_vars
      ; repeat rewrite replace_all_app
      ; simpl; trivial
      ; string_eqdec_to_equiv.
      - rewrite IHs1, IHs2 by tauto; trivial.
      - destruct o; simpl.
        + rewrite nnrs_imp_expr_rename_free_vars.
          f_equal.
          match_destr; unfold equiv, complement in *.
          * subst.
            rewrite replace_all_remove_eq; trivial.
          * rewrite IHs by tauto.
            rewrite remove_replace_all_comm by tauto.
            trivial.
        + match_destr; unfold equiv, complement in *.
          * subst.
            rewrite replace_all_remove_eq; trivial.
          * rewrite IHs by tauto.
            rewrite remove_replace_all_comm by tauto.
            trivial.
      - f_equal.
        match_destr; unfold equiv, complement in *.
        + subst.
          rewrite replace_all_remove_eq; trivial.
        + rewrite IHs by tauto.
          rewrite remove_replace_all_comm by tauto.
          trivial.
      - rewrite IHs1, IHs2 by tauto; trivial.
      - f_equal.
        f_equal.
        + match_destr; unfold equiv, complement in *.
          * subst.
            rewrite replace_all_remove_eq; trivial.
          * rewrite IHs1 by tauto.
            rewrite remove_replace_all_comm by tauto.
            trivial.
        + match_destr; unfold equiv, complement in *.
          * subst.
            rewrite replace_all_remove_eq; trivial.
          * simpl in *. rewrite IHs2 by tauto.
            rewrite remove_replace_all_comm by tauto.
            trivial.
    Qed.

  End vars.

  Section var_usage.
    
    Lemma nnrs_imp_expr_rename_may_use_neq e v v' v0 :
      v0 <> v ->
      v0 <> v' ->
      nnrs_imp_expr_may_use (nnrs_imp_expr_rename e v v') v0 =
      nnrs_imp_expr_may_use e v0.
    Proof.
      induction e; simpl; intros
      ; repeat rewrite IHe by tauto
      ; repeat rewrite IHe1 by tauto
      ; repeat rewrite IHe2 by tauto
      ; trivial.
      match_destr.
      unfold equiv_decb in *.
      repeat match_destr; congruence.
    Qed.

    Lemma nnrs_imp_stmt_rename_var_usage_neq s v v' v0 :
      v0 <> v ->
      v0 <> v' ->
      nnrs_imp_stmt_var_usage (nnrs_imp_stmt_rename s v v') v0 =
      nnrs_imp_stmt_var_usage s v0.
    Proof.
      nnrs_imp_stmt_cases (induction s) Case; simpl; intros
      ; repeat rewrite nnrs_imp_expr_rename_may_use_neq
      ; repeat rewrite IHs by tauto
      ; repeat rewrite IHs1 by tauto
      ; repeat rewrite IHs2 by tauto
      ; trivial.
      - Case "NNRSimpAssign"%string.
        match_destr.
        unfold equiv_decb.
        destruct (equiv_dec v1 v)
        ; destruct (equiv_dec v1 v0)
        ; destruct (equiv_dec v' v0)
        ; try congruence.
      - Case "NNRSimpLet"%string.
        destruct o
        ; repeat rewrite nnrs_imp_expr_rename_may_use_neq
        ; repeat rewrite IHs by tauto
        ; repeat match_destr; eauto.
      - Case "NNRSimpFor"%string.
        match_destr.
        unfold equiv_decb.
        destruct (equiv_dec v1 v0); trivial.
        destruct (equiv_dec v1 v); trivial.
        rewrite IHs; tauto.
      - Case "NNRSimpEither"%string.
        match_destr.
        destruct (v1 == v0)
        ; destruct (v2 == v0)
        ; trivial
        ; destruct (v1 == v)
        ; destruct (v2 == v)
        ; trivial
        ; repeat rewrite IHs1 by tauto
        ; repeat rewrite IHs2 by tauto
        ; trivial.
    Qed.
    
    Lemma nnrs_imp_expr_rename_may_use_eq_to e v v'  :
      ~ In v' (nnrs_imp_expr_free_vars e) ->
      nnrs_imp_expr_may_use (nnrs_imp_expr_rename e v v') v' =
      nnrs_imp_expr_may_use e v.
    Proof.
      intros.
      induction e; simpl in *
      ; repeat rewrite in_app_iff in *
      ; intros
      ; repeat rewrite IHe by tauto
      ; repeat rewrite IHe1 by tauto
      ; repeat rewrite IHe2 by tauto
      ; trivial.
      - unfold equiv_decb.
        intuition.
        destruct (v0 == v)
        ; repeat match_destr; try congruence.
    Qed.

    Lemma nnrs_imp_stmt_rename_var_usage_eq_to s v v'  :
      ~ In v' (nnrs_imp_stmt_free_vars s) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s) ->
      nnrs_imp_stmt_var_usage (nnrs_imp_stmt_rename s v v') v' =
      nnrs_imp_stmt_var_usage s v.
    Proof.
      nnrs_imp_stmt_cases (induction s) Case; simpl; intros
      ; repeat rewrite in_app_iff in *
      ; repeat rewrite nnrs_imp_expr_rename_may_use_eq_to by tauto
      ; repeat rewrite IHs by tauto
      ; repeat rewrite IHs1 by tauto
      ; repeat rewrite IHs2 by tauto
      ; trivial.
      - Case "NNRSimpAssign"%string.
        match_destr.
        unfold equiv_decb.
        intuition.
        destruct (equiv_dec v0 v)
        ; destruct (equiv_dec v0 v')
        ; destruct (equiv_dec v' v')
        ; try congruence.
      - Case "NNRSimpLet"%string.
        destruct o.
        + intuition.
          repeat rewrite nnrs_imp_expr_rename_may_use_eq_to by tauto.
          unfold equiv_decb.
          apply remove_nin_inv in H2.
          match_destr.
          destruct (v0 == v); try congruence
          ; destruct (v0 == v'); try congruence
          ;  unfold equiv, complement in *
          ; subst
          ; intuition.
          apply nnrs_imp_stmt_free_unassigned in H0; trivial.
        + intuition.
          unfold equiv_decb.
          apply remove_nin_inv in H2.
          destruct (v0 == v); try congruence
          ; destruct (v0 == v'); try congruence
          ;  unfold equiv, complement in *
          ; subst
          ; intuition.
          apply nnrs_imp_stmt_free_unassigned in H0; trivial.
      - Case "NNRSimpFor"%string.
        match_destr.
        intuition.
        apply remove_nin_inv in H2.
        unfold equiv_decb.
        destruct (equiv_dec v0 v'); try congruence.
        intuition.
        apply nnrs_imp_stmt_free_unassigned in H0; trivial.
        destruct (equiv_dec v0 v).
        + rewrite H0; trivial.
        + rewrite H4; trivial.
      - Case "NNRSimpEither"%string.
        match_destr.
        intuition.
        apply remove_nin_inv in H0.
        apply remove_nin_inv in H4.
        simpl in *.
        intuition.
        destruct (v0 == v'); try congruence.
        destruct (v1 == v'); try congruence.
        destruct (equiv_dec v0 v)
        ; destruct (equiv_dec v1 v)
        ; unfold equiv, complement in *
        ; subst.
        + apply nnrs_imp_stmt_free_unassigned in H3; trivial.
          apply nnrs_imp_stmt_free_unassigned in H0; trivial.
          rewrite H3, H0; trivial.
        + apply nnrs_imp_stmt_free_unassigned in H3; trivial.
          rewrite H3, H5; trivial.
        + apply nnrs_imp_stmt_free_unassigned in H0; trivial.
          rewrite H6, H0; trivial.
        + rewrite H5, H6; trivial.
    Qed.

    Lemma nnrs_imp_stmt_rename_let_var_usage_sub s v v'  :
      ~ In v' (nnrs_imp_stmt_free_vars s) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s) ->
      forall e,
        stmt_var_usage_sub
          (NNRSimpLet v e s)
          (NNRSimpLet v' e (nnrs_imp_stmt_rename s v v')).
    Proof.
      intros inn1 inn2 e x.
      simpl.
      match_destr; simpl; trivial.
      unfold equiv_decb.
      destruct (v == x)
      ; destruct (v' == x)
      ; simpl; trivial
      ; unfold equiv, complement in *.
      - subst.
        rewrite nnrs_imp_stmt_free_unassigned; trivial.
        rewrite nnrs_imp_stmt_rename_free_vars; trivial.
        intros inn.
        apply in_replace_all in inn.
        intuition.
      - subst.
        rewrite nnrs_imp_stmt_free_unassigned; simpl; trivial.
      - rewrite nnrs_imp_stmt_rename_var_usage_neq; eauto.
        reflexivity.
    Qed.

    Lemma nnrs_imp_stmt_rename_let_var_usage_sub_b s v v'  :
      ~ In v' (nnrs_imp_stmt_free_vars s) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s) ->
      forall e,
        stmt_var_usage_sub
          (NNRSimpLet v' e (nnrs_imp_stmt_rename s v v'))
          (NNRSimpLet v e s).
    Proof.
      intros inn1 inn2 e x.
      simpl.
      match_destr; simpl; trivial.
      unfold equiv_decb.
      destruct (v == x)
      ; destruct (v' == x)
      ; simpl; trivial
      ; unfold equiv, complement in *.
      - subst.
        rewrite nnrs_imp_stmt_free_unassigned; simpl; trivial.
        rewrite nnrs_imp_stmt_rename_free_vars; trivial.
        intros inn.
        apply in_replace_all in inn.
        intuition.
      - subst.
        rewrite nnrs_imp_stmt_free_unassigned; simpl; trivial.
      - rewrite nnrs_imp_stmt_rename_var_usage_neq; eauto.
        reflexivity.
    Qed.

    Lemma nnrs_imp_stmt_rename_for_var_usage_sub s v v'  :
      ~ In v' (nnrs_imp_stmt_free_vars s) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s) ->
      forall e,
        stmt_var_usage_sub
          (NNRSimpFor v e s)
          (NNRSimpFor v' e (nnrs_imp_stmt_rename s v v')).
    Proof.
      intros inn1 inn2 e x.
      simpl.
      match_destr; simpl; trivial.
      unfold equiv_decb.
      destruct (v == x)
      ; destruct (v' == x)
      ; simpl; trivial
      ; unfold equiv, complement in *.
      - subst.
        rewrite nnrs_imp_stmt_free_unassigned; trivial.
        rewrite nnrs_imp_stmt_rename_free_vars; trivial.
        intros inn.
        apply in_replace_all in inn.
        intuition.
      - subst.
        rewrite nnrs_imp_stmt_free_unassigned; simpl; trivial.
      - rewrite nnrs_imp_stmt_rename_var_usage_neq; eauto.
        reflexivity.
    Qed.

    Lemma nnrs_imp_stmt_rename_for_var_usage_sub_b s v v'  :
      ~ In v' (nnrs_imp_stmt_free_vars s) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s) ->
      forall e,
        stmt_var_usage_sub
          (NNRSimpFor v' e (nnrs_imp_stmt_rename s v v'))
          (NNRSimpFor v e s).
    Proof.
      intros inn1 inn2 e x.
      simpl.
      match_destr; simpl; trivial.
      unfold equiv_decb.
      destruct (v == x)
      ; destruct (v' == x)
      ; simpl; trivial
      ; unfold equiv, complement in *.
      - subst.
        rewrite nnrs_imp_stmt_free_unassigned; simpl; trivial.
        rewrite nnrs_imp_stmt_rename_free_vars; trivial.
        intros inn.
        apply in_replace_all in inn.
        intuition.
      - subst.
        rewrite nnrs_imp_stmt_free_unassigned; simpl; trivial.
      - rewrite nnrs_imp_stmt_rename_var_usage_neq; eauto.
        reflexivity.
    Qed.

    Lemma nnrs_imp_stmt_rename_either_l_var_usage_sub s1 v1 v'  :
      ~ In v' (nnrs_imp_stmt_free_vars s1) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s1) ->
      forall e v2 s2,
        stmt_var_usage_sub
          (NNRSimpEither e v1 s1 v2 s2)
          (NNRSimpEither e v' (nnrs_imp_stmt_rename s1 v1 v') v2 s2).
    Proof.
      intros inn1 inn2 e v2 s2 x.
      simpl.
      match_destr; simpl; trivial.
      unfold equiv_decb.
      destruct (v1 == x)
      ; destruct (v' == x)
      ; simpl; trivial
      ; unfold equiv, complement in *
      ; try reflexivity.
      - subst.
        rewrite (nnrs_imp_stmt_free_unassigned (nnrs_imp_stmt_rename s1 x v')); simpl; try reflexivity.
        rewrite nnrs_imp_stmt_rename_free_vars; trivial.
        intros inn.
        apply in_replace_all in inn.
        intuition.
      - subst.
        rewrite nnrs_imp_stmt_free_unassigned; simpl; trivial.
        reflexivity.
      - rewrite nnrs_imp_stmt_rename_var_usage_neq; eauto.
        reflexivity.
    Qed.

    Lemma nnrs_imp_stmt_rename_either_l_var_usage_sub_b s1 v1 v'  :
      ~ In v' (nnrs_imp_stmt_free_vars s1) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s1) ->
      forall e v2 s2,
        stmt_var_usage_sub
          (NNRSimpEither e v' (nnrs_imp_stmt_rename s1 v1 v') v2 s2)
          (NNRSimpEither e v1 s1 v2 s2).
    Proof.
      intros inn1 inn2 e v2 s2 x.
      simpl.
      match_destr; simpl; trivial.
      unfold equiv_decb.
      destruct (v1 == x)
      ; destruct (v' == x)
      ; simpl; trivial
      ; unfold equiv, complement in *
      ; try reflexivity.
      - subst.
        rewrite (nnrs_imp_stmt_free_unassigned (nnrs_imp_stmt_rename s1 x v')); simpl; try reflexivity.
        rewrite nnrs_imp_stmt_rename_free_vars; trivial.
        intros inn.
        apply in_replace_all in inn.
        intuition.
      - subst.
        rewrite (nnrs_imp_stmt_free_unassigned s1); simpl; trivial.
        reflexivity.
      - rewrite nnrs_imp_stmt_rename_var_usage_neq; eauto.
        reflexivity.
    Qed.

    Lemma nnrs_imp_stmt_rename_either_r_var_usage_sub s2 v2 v'  :
      ~ In v' (nnrs_imp_stmt_free_vars s2) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s2) ->
      forall e v1 s1,
        stmt_var_usage_sub
          (NNRSimpEither e v1 s1 v2 s2)
          (NNRSimpEither e v1 s1 v' (nnrs_imp_stmt_rename s2 v2 v')).
    Proof.
      intros inn1 inn2 e v1 s1 x.
      simpl.
      match_destr; simpl; trivial.
      unfold equiv_decb.
      destruct (v2 == x)
      ; destruct (v' == x)
      ; simpl; trivial
      ; unfold equiv, complement in *
      ; try reflexivity.
      - subst.
        rewrite (nnrs_imp_stmt_free_unassigned (nnrs_imp_stmt_rename s2 x v')); simpl; try reflexivity.
        rewrite nnrs_imp_stmt_rename_free_vars; trivial.
        intros inn.
        apply in_replace_all in inn.
        intuition.
      - subst.
        rewrite nnrs_imp_stmt_free_unassigned; simpl; trivial.
        reflexivity.
      - rewrite nnrs_imp_stmt_rename_var_usage_neq; eauto.
        reflexivity.
    Qed.

    Lemma nnrs_imp_stmt_rename_either_r_var_usage_sub_b s2 v2 v'  :
      ~ In v' (nnrs_imp_stmt_free_vars s2) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s2) ->
      forall e v1 s1,
        stmt_var_usage_sub
          (NNRSimpEither e v1 s1 v' (nnrs_imp_stmt_rename s2 v2 v'))
          (NNRSimpEither e v1 s1 v2 s2).
    Proof.
      intros inn1 inn2 e v1 s1 x.
      simpl.
      match_destr; simpl; trivial.
      unfold equiv_decb.
      destruct (v2 == x)
      ; destruct (v' == x)
      ; simpl; trivial
      ; unfold equiv, complement in *
      ; try reflexivity.
      - subst.
        rewrite (nnrs_imp_stmt_free_unassigned (nnrs_imp_stmt_rename s2 x v')); simpl; try reflexivity.
        rewrite nnrs_imp_stmt_rename_free_vars; trivial.
        intros inn.
        apply in_replace_all in inn.
        intuition.
      - subst.
        rewrite (nnrs_imp_stmt_free_unassigned s2); simpl; trivial.
        reflexivity.
      - rewrite nnrs_imp_stmt_rename_var_usage_neq; eauto.
        reflexivity.
    Qed.
    
  End var_usage.

  Section id.
    
    Lemma nnrs_imp_expr_rename_id
          (e:nnrs_imp_expr) (v:var) :
      nnrs_imp_expr_rename e v v = e.
    Proof.
      induction e; simpl; try congruence.
      match_destr; congruence.
    Qed.

    Lemma nnrs_imp_stmt_rename_id
          (s:nnrs_imp_stmt) (v:var) :
      nnrs_imp_stmt_rename s v v = s.
    Proof.
      induction s; simpl
      ; repeat rewrite nnrs_imp_expr_rename_id
      ; try congruence
      ; repeat (match_destr
                ; repeat rewrite nnrs_imp_expr_rename_id 
                ; try congruence).
    Qed.

  End id.

  Section nfree.
    
    Lemma nnrs_imp_expr_rename_nin e from to :
      ~ In from (nnrs_imp_expr_free_vars e) ->
      nnrs_imp_expr_rename e from to = e.
    Proof.
      induction e; simpl
      ; repeat rewrite in_app_iff
      ; intros
      ; try congruence
      ; try match_destr
      ; try intuition congruence.
    Qed.

    Lemma nnrs_imp_stmt_rename_nin s from to :
      ~ In from (nnrs_imp_stmt_free_vars s) ->
      nnrs_imp_stmt_rename s from to = s.
    Proof.
      induction s; simpl
      ; repeat rewrite in_app_iff
      ; repeat rewrite nnrs_imp_expr_rename_nin by tauto
      ; intros
      ; try congruence
      ; repeat match_destr
      ; repeat rewrite nnrs_imp_expr_rename_nin by tauto
      ; try (intuition congruence)
      ; try solve [rewrite IHs; intuition
                   ; apply remove_nin_inv in H2; intuition]
      ; try solve [rewrite IHs; intuition
                   ; apply remove_nin_inv in H2; intuition].
      - rewrite IHs2; intuition.
        apply remove_nin_inv in H3; intuition.
      - rewrite IHs1; intuition.
        apply remove_nin_inv in H; intuition.
      - rewrite IHs1, IHs2; intuition.
        + apply remove_nin_inv in H3; intuition.
        + apply remove_nin_inv in H; intuition.
    Qed.
    
  End nfree.

  Section involutive.

    Lemma nnrs_imp_expr_rename_involutive e v v' :
      ~ In v' (nnrs_imp_expr_free_vars e) ->
      nnrs_imp_expr_rename (nnrs_imp_expr_rename e v v') v' v = e.
    Proof.
      induction e; simpl
      ; repeat rewrite in_app_iff
      ; intros inn
      ; try rewrite IHe by tauto
      ; try rewrite IHe1 by tauto
      ; try rewrite IHe2 by tauto
      ; try rewrite IHe3 by tauto
      ; trivial.
      - destruct (equiv_dec v0 v); match_destr; try congruence; tauto.
    Qed.

    Lemma nnrs_imp_stmt_rename_involutive s v v' :
      ~ In v' (nnrs_imp_stmt_free_vars s) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s) ->
      nnrs_imp_stmt_rename (nnrs_imp_stmt_rename s v v') v' v = s.
    Proof.
      induction s; simpl
      ; repeat rewrite in_app_iff
      ; intros innf innb
      ; try rewrite nnrs_imp_expr_rename_involutive by tauto
      ; try rewrite IHs by tauto
      ; try rewrite IHs1 by tauto
      ; try rewrite IHs2 by tauto
      ; try rewrite IHs3 by tauto
      ; trivial.
      - destruct (equiv_dec v0 v); match_destr; unfold equiv, complement in *
        ; try congruence.
        tauto.
      - f_equal.
        + destruct o; trivial. rewrite nnrs_imp_expr_rename_involutive; tauto.
        + intuition.
          apply remove_nin_inv in H0; intuition.
          destruct (equiv_dec v0 v'); try congruence.
          match_destr.
          rewrite nnrs_imp_stmt_rename_nin; tauto.
      - f_equal.
        intuition.
        apply remove_nin_inv in H0; intuition.
        destruct (equiv_dec v0 v'); try congruence.
        match_destr.
        rewrite nnrs_imp_stmt_rename_nin; tauto.
      - intuition.
        apply remove_nin_inv in H3.
        apply remove_nin_inv in H4.
        simpl in *.
        intuition.
        f_equal.
        + destruct (equiv_dec v0 v'); try congruence.
          match_destr.
          rewrite nnrs_imp_stmt_rename_nin; tauto.
        + destruct (equiv_dec v1 v'); try congruence.
          match_destr.
          rewrite nnrs_imp_stmt_rename_nin; tauto.
    Qed.

  End involutive.
  
  Section eval.

    Lemma nnrs_imp_expr_eval_rename_in h c l σ e v v' d:
      ~ In v (domain l) ->
      ~ In v' (domain l) ->
      ~ In v' (nnrs_imp_expr_free_vars e) ->
      nnrs_imp_expr_eval h c (l++(v', d) :: σ) (nnrs_imp_expr_rename e v v')
      = nnrs_imp_expr_eval h c (l++(v, d) :: σ) e.
    Proof.
      nnrs_imp_expr_cases (induction e) Case; simpl; trivial
      ; repeat rewrite in_app_iff; intros
      ; try solve [ rewrite IHe by intuition; trivial
                  |  rewrite IHe1, IHe2 by intuition; trivial
                  ].
      - Case "NNRSimpVar"%string.
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
    
    Lemma nnrs_imp_expr_eval_rename h c σ e v v' d:
      ~ In v' (nnrs_imp_expr_free_vars e) ->
      nnrs_imp_expr_eval h c ((v', d) :: σ) (nnrs_imp_expr_rename e v v')
      = nnrs_imp_expr_eval h c ((v, d) :: σ) e.
    Proof.
      apply (nnrs_imp_expr_eval_rename_in h c nil); simpl; tauto.
    Qed.

    Lemma nnrs_imp_stmt_eval_rename_in h c l σ s v v' d:
      ~ In v (domain l) ->
      ~ In v' (domain l) ->
      ~ In v' (nnrs_imp_stmt_free_vars s) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s) ->

      lift2P  (fun σ₁' σ₂' =>
                 (forall l' d σ'',
                     domain l' = domain l ->
                     σ₁' = l' ++ (v',d)::σ'' ->
                     σ₂' = l' ++ (v,d)::σ'')
              )
              (nnrs_imp_stmt_eval h c (nnrs_imp_stmt_rename s v v') (l++(v',d)::σ))
              (nnrs_imp_stmt_eval h c s (l++(v,d)::σ)).
    Proof.

      Ltac disect_tac H stac
        := 
          unfold var in *
          ; cut_to H; unfold domain in *; [ | solve[stac]..]
          ; unfold lift2P in H
          ; (repeat match_option_in H; try contradiction).

      Ltac pcong
        := solve[repeat (match goal with
                         | [H: _ = _ |- _ ] => rewrite H in *; clear H
                         end; try tauto)].

      Ltac ren_eval_t stac
        := repeat progress (
                    repeat rewrite in_app_iff in *
                    ; repeat
                        match goal with
                        | [H : ~ (_ \/ _ ) |- _ ] => apply not_or in H
                        | [H : (_ \/ _ ) -> False |- _ ] => apply not_or in H
                        | [H: _ /\ _ |- _ ] => destruct H
                        | [ H : _ * _ |- _ ] => destruct H
                        | [H: _::_ = _::_ |- _ ] => invcs H
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
                        | [H : ~ In _ (remove _ _ _) |- _ ] =>
                          apply not_in_remove_impl_not_in in H; [| congruence]
                        | [H : ?x ++ _ = ?y ++ _ |- _ ] =>
                          let HH := fresh in
                          assert (HH:domain y = domain x) by
                              (unfold domain in *;
                               try (intuition congruence)
                               ; pcong)
                          ; apply app_inv_head_domain in H;[clear HH|apply HH]
                                                             

                        | [ H: forall a b c, _ -> ?x1 ++ ?dd :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                          specialize (H x1 (snd dd) x2); simpl in H
                          ; match dd with
                            | (_,_) => idtac
                            | _ => destruct dd
                            end
                          ; simpl in *
                          ; cut_to H; [ | eauto 3 | reflexivity]
                        | [ H: forall a b c, _ -> ?dd0::?x1 ++ ?dd :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                          specialize (H (dd0::x1) (snd dd) x2); simpl in H
                          ; match dd with
                            | (_,_) => idtac
                            | _ => destruct dd
                            end
                          ; simpl in *
                          ; cut_to H; [ | eauto 3 | reflexivity]

                                        
                        | [H : nnrs_imp_stmt_eval _ _ _ ?p1 = ?p2 |- _ ] =>
                          match p1 with
                          | p2 => fail 1
                          | _ =>  extend (nnrs_imp_stmt_eval_domain_stack H); clear H
                          end
                            
                        | [H:forall l σ d,
                              _ -> _ -> _ -> _ -> lift2P _ (nnrs_imp_stmt_eval _ _ ?s _) _
                                                         
                              |- lift2P _ (olift _ (nnrs_imp_stmt_eval _ _ ?s (?l ++ (_, ?d) :: ?σ) ))
                                        _ ] =>
                          specialize (H l σ d)
                          ; disect_tac H stac
                        | [H:forall l σ d,
                              _ -> _ -> _ -> _ -> lift2P _ (nnrs_imp_stmt_eval _ _ ?s _) _
                                                         
                              |- lift2P _ (nnrs_imp_stmt_eval _ _ ?s (?l ++ (_, ?d) :: ?σ) )
                                        _ ] =>
                          specialize (H l σ d)
                          ; disect_tac H stac
                        | [H:forall l σ d,
                              _ -> _ -> _ -> _ -> lift2P _ (nnrs_imp_stmt_eval _ _ ?s _) _
                                                         
                              |- lift2P _ (match nnrs_imp_stmt_eval _ _ ?s (?x::?l ++ (_, ?d) :: ?σ)
                                           with | Some _ => _ | None => _ end)
                                        _ ] =>
                          specialize (H (x::l) σ d); simpl in H
                          ; disect_tac H stac
                        end; simpl in *; trivial; intros; try subst; try solve [congruence | f_equal; congruence]).

      Ltac ren_eval_tt := ren_eval_t ltac:(try tauto; try congruence).
      
      revert l σ d.
      nnrs_imp_stmt_cases (induction s) Case; simpl; trivial
      ; repeat rewrite in_app_iff in *; intros l σ d; intros
      ; repeat rewrite nnrs_imp_expr_eval_rename_in by tauto
      ; try solve [ rewrite IHs by intuition; trivial
                  |  rewrite IHs1, IHs2 by intuition; trivial
                  ].
      - Case "NNRSimpSkip"%string.
        ren_eval_tt.
      - Case "NNRSimpSeq"%string.
        ren_eval_tt.
      - Case "NNRSimpAssign"%string.
        match_destr; try reflexivity.
        destruct (equiv_dec v0 v); unfold equiv, complement in *.
        + subst.
          repeat rewrite lookup_app.
          rewrite (lookup_nin_none _ H0).
          rewrite (lookup_nin_none _ H).
          simpl.
          repeat rewrite update_app_nin by trivial.
          simpl.
          destruct (string_dec v' v'); try congruence.
          destruct (string_dec v v); try congruence.
          ren_eval_tt.
        + repeat rewrite lookup_app.
          case_eq (lookup string_dec l v0); [intros ? inn | intros nin].
          * repeat rewrite update_app_in
              by (apply lookup_in_domain in inn; trivial).
            simpl.
            intros ? ? ? domeq eqq.
            apply app_inv_head_domain in eqq
            ; [ |rewrite domain_update_first; trivial].
            destruct eqq as [eqq1 eqq2].
            invcs eqq2.
            trivial.
          * apply lookup_none_nin in nin.
            repeat rewrite update_app_nin by trivial.
            simpl.
            destruct (string_dec v0 v'); try tauto.
            destruct (string_dec v0 v); try congruence.
            match_destr; try reflexivity.
            ren_eval_tt.
      - Case "NNRSimpLet"%string.
        destruct o.
        + ren_eval_tt.
          rewrite nnrs_imp_expr_eval_rename_in by trivial.
          destruct (nnrs_imp_expr_eval h c (l ++ (v, d) :: σ) n); simpl; trivial.
          destruct (equiv_dec v0 v); unfold equiv, complement in *.
          * subst.
            generalize (nnrs_imp_stmt_eval_unused h c
                                                  ((v, Some d0) :: l) σ s v' d).
            generalize (nnrs_imp_stmt_eval_unused h c
                                                  ((v, Some d0) :: l) σ s v d).
            simpl; intros HH1 HH2.
            cut_to HH1; [| tauto].
            cut_to HH2; [| tauto].
            unfold lift2P in *.

            repeat match_option_in HH1
            ; rewrite eqq0 in *
            ; repeat match_option_in HH2
            ; subst
            ; try contradiction
            ; ren_eval_tt; subst
            ; f_equal
            ; unfold domain in *; eauto.
          * ren_eval_tt.
        + destruct (equiv_dec v0 v); unfold equiv, complement in *.
          * subst.
            generalize (nnrs_imp_stmt_eval_unused h c
                                                  ((v, None) :: l) σ s v' d).
            generalize (nnrs_imp_stmt_eval_unused h c
                                                  ((v, None) :: l) σ s v d).
            simpl; intros HH1 HH2.
            cut_to HH1; [| tauto].
            simpl in H1.
            apply remove_nin_inv in H1.
            cut_to HH2; [ | intuition ].
            unfold lift2P in *.

            repeat match_option_in HH1
            ; rewrite eqq0 in *
            ; repeat match_option_in HH2
            ; subst
            ; try contradiction
            ; ren_eval_tt; subst
            ; f_equal
            ; unfold domain in *; eauto.
          * ren_eval_tt.
      - Case "NNRSimpFor"%string.
        ren_eval_tt.
        rewrite nnrs_imp_expr_eval_rename_in by trivial.
        destruct (nnrs_imp_expr_eval h c (l ++ (v, d) :: σ) n); simpl; trivial.
        destruct d0; simpl; trivial.
        revert l σ d H H0.
        induction l0; intros l σ d ninv ninv'; simpl; ren_eval_tt.
        destruct (equiv_dec v0 v); unfold equiv, complement in *.
        + subst.
          generalize (nnrs_imp_stmt_eval_unused h c
                                                ((v, Some a) :: l) σ s v' d).
          generalize (nnrs_imp_stmt_eval_unused h c
                                                ((v, Some a) :: l) σ s v d).
          simpl; intros HH1 HH2.
          cut_to HH1; [| tauto].
          simpl in H1.
          cut_to HH2; [ | intuition ].
          unfold lift2P in *.
          
          repeat match_option_in HH1
          ; rewrite eqq0 in *
          ; repeat match_option_in HH2
          ; subst
          ; try contradiction
          ; ren_eval_tt; subst
          ; f_equal
          ; unfold domain in *; eauto.
          * specialize (IHl0 x x0 o0).
            unfold var in *.
            { cut_to IHl0.
              - unfold lift2P in *.
                repeat match_option_in IHl0.
                ren_eval_tt.
              - pcong.
              - pcong.
            }
        + specialize (IHs ((v0, Some a)::l) σ d); simpl in IHs.
          cut_to IHs; simpl; [ | intuition..].
          unfold lift2P in *.
          unfold var in *.
          repeat match_option_in IHs
          ; try contradiction
          ; ren_eval_tt.
          * specialize (IHl0 x x0 o0).
            { cut_to IHl0.
              - unfold lift2P in *.
                repeat match_option_in IHl0.
                ren_eval_tt.
                pcong.
              - unfold domain in *; congruence.
              - unfold domain in *; congruence.
            }
          * f_equal.
            unfold domain in *; congruence.
      - Case "NNRSimpIf"%string.
        ren_eval_tt.
        rewrite nnrs_imp_expr_eval_rename_in by trivial.
        destruct (nnrs_imp_expr_eval h c (l ++ (v, d) :: σ) n); simpl; trivial.
        destruct d0; simpl; trivial. 
        destruct b; ren_eval_tt.
      - Case "NNRSimpEither"%string.
        ren_eval_tt.
        rewrite nnrs_imp_expr_eval_rename_in by trivial.
        destruct (nnrs_imp_expr_eval h c (l ++ (v, d) :: σ) n); simpl; trivial.
        destruct d0; simpl; trivial.
        + destruct (equiv_dec v0 v); unfold equiv, complement in *.
          * subst.
            generalize (nnrs_imp_stmt_eval_unused h c
                                                  ((v, Some d0) :: l) σ s1 v' d).
            generalize (nnrs_imp_stmt_eval_unused h c
                                                  ((v, Some d0) :: l) σ s1 v d).
            simpl; intros HH1 HH2.
            cut_to HH1; [| tauto].
            simpl in H1.
            cut_to HH2; [ | intuition ].
            unfold lift2P in *.

            repeat match_option_in HH1
            ; rewrite eqq0 in *
            ; repeat match_option_in HH2
            ; subst
            ; try contradiction
            ; ren_eval_tt; subst
            ; f_equal
            ; unfold domain in *; eauto.
          * ren_eval_tt. 
        + destruct (equiv_dec v1 v); unfold equiv, complement in *.
          * subst.
            generalize (nnrs_imp_stmt_eval_unused h c
                                                  ((v, Some d0) :: l) σ s2 v' d).
            generalize (nnrs_imp_stmt_eval_unused h c
                                                  ((v, Some d0) :: l) σ s2 v d).
            simpl; intros HH1 HH2.
            cut_to HH1; [| tauto].
            simpl in H1.
            cut_to HH2; [ | intuition ].
            unfold lift2P in *.

            repeat match_option_in HH1
            ; rewrite eqq0 in *
            ; repeat match_option_in HH2
            ; subst
            ; try contradiction
            ; ren_eval_tt; subst
            ; f_equal
            ; unfold domain in *; eauto.
          * ren_eval_tt. 
    Qed.                               

    Lemma nnrs_imp_stmt_eval_rename h c σ s v v' d:
      ~ In v' (nnrs_imp_stmt_free_vars s) ->
      ~ In v' (nnrs_imp_stmt_bound_vars s) ->
      match
        (nnrs_imp_stmt_eval h c (nnrs_imp_stmt_rename s v v') ((v',d)::σ)),
        (nnrs_imp_stmt_eval h c s ((v,d)::σ)) with
      | None, None => True
      | Some ((v₁,d₁)::σ₁'), Some ((v₂,d₂)::σ₂') => v₁ = v' /\ v₂ = v /\ d₁ = d₂ /\ σ₁' = σ₂'
      | _, _ => False
      end.
    Proof.
      intros inn.
      generalize (nnrs_imp_stmt_eval_rename_in h c nil σ s v v' d)
      ; simpl; intros; intuition.
      match_option
      ; rewrite eqq in *
      ; simpl in *
      ; trivial.
      match_option_in H; try contradiction.
      apply nnrs_imp_stmt_eval_domain_stack in eqq.
      apply nnrs_imp_stmt_eval_domain_stack in eqq0.
      simpl in *.
      destruct p; simpl in *; invcs eqq.
      destruct p0; simpl in *; invcs eqq0.
      destruct p; destruct p0; simpl.
      specialize (H nil o p1 (eq_refl _) (eq_refl _))
      ; simpl in *.
      invcs H.
      tauto.
    Qed.
    
  End eval.

  Section core.

    Lemma nnrs_imp_expr_rename_core e v v' :
      nnrs_imp_exprIsCore (nnrs_imp_expr_rename e v v') <->
      nnrs_imp_exprIsCore e.
    Proof.
      induction e; simpl; intuition.
    Qed.

    Lemma nnrs_imp_stmt_rename_core_f s v v' :
      nnrs_imp_stmtIsCore s ->
      nnrs_imp_stmtIsCore (nnrs_imp_stmt_rename s v v').
    Proof.
      induction s; simpl
      ; repeat rewrite nnrs_imp_expr_rename_core in *
      ; intuition.
      - destruct o; match_destr
        ; repeat rewrite nnrs_imp_expr_rename_core in *
        ; intuition.
      - match_destr
        ; repeat rewrite nnrs_imp_expr_rename_core in *
        ; intuition.
      - match_destr 
        ; repeat rewrite nnrs_imp_expr_rename_core in *
        ; intuition.
      - match_destr
        ; repeat rewrite nnrs_imp_expr_rename_core in *
        ; intuition.
    Qed.

    Lemma nnrs_imp_stmt_rename_core_b s v v' :
      nnrs_imp_stmtIsCore (nnrs_imp_stmt_rename s v v') ->
      nnrs_imp_stmtIsCore s.
    Proof.
      induction s; simpl
      ; repeat rewrite nnrs_imp_expr_rename_core in *
      ; intuition.
      - destruct o; match_destr_in H
        ; repeat rewrite nnrs_imp_expr_rename_core in *
        ; intuition.
      - match_destr_in H1
        ; repeat rewrite nnrs_imp_expr_rename_core in *
        ; intuition.
      - match_destr_in H
        ; repeat rewrite nnrs_imp_expr_rename_core in *
        ; intuition.
      - match_destr_in H2
        ; repeat rewrite nnrs_imp_expr_rename_core in *
        ; intuition.
    Qed.

    Lemma nnrs_imp_stmt_rename_core s v v' :
      nnrs_imp_stmtIsCore (nnrs_imp_stmt_rename s v v') <->
      nnrs_imp_stmtIsCore s.
    Proof.
      split; intros HH.
      - eapply nnrs_imp_stmt_rename_core_b; eauto.
      - eapply nnrs_imp_stmt_rename_core_f; eauto.
    Qed.
    
  End core.

  Section lazy.
    (* The lazy variants have the same semantics, but are more efficient
       if we expect it likely that from == to.
       This is the case when we are enabling an optimization to "lazily" rename
       to avoid a possible conflict and there is not actual conflict.
     *)
    Definition nnrs_imp_expr_rename_lazy (e:nnrs_imp_expr) (from to:var)
      := if from == to
         then e
         else nnrs_imp_expr_rename e from to.
    
    Definition nnrs_imp_stmt_rename_lazy (s:nnrs_imp_stmt) (from to:var)
      := if from == to
         then s
         else nnrs_imp_stmt_rename s from to.

    Lemma nnrs_imp_expr_rename_lazy_eq (e:nnrs_imp_expr) (from to:var) :
      nnrs_imp_expr_rename_lazy e from to = nnrs_imp_expr_rename e from to.
    Proof.
      unfold nnrs_imp_expr_rename_lazy.
      match_destr; unfold equiv in *; subst.
      rewrite nnrs_imp_expr_rename_id; trivial.
    Qed.

    Lemma nnrs_imp_stmt_rename_lazy_eq (s:nnrs_imp_stmt) (from to:var) :
      nnrs_imp_stmt_rename_lazy s from to = nnrs_imp_stmt_rename s from to.
    Proof.
      unfold nnrs_imp_stmt_rename_lazy.
      match_destr; unfold equiv in *; subst.
      rewrite nnrs_imp_stmt_rename_id; trivial.
    Qed.

  End lazy.
  
End NNRSimpRename.
