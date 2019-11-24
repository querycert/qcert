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
Require Import Max.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNNRC.

Section cNNRCVars.
  Close Scope nnrc_scope.
  
  (* Since we are translating from a language with scoped variables
     (For) to a language without scoping, we need to alpha convert the input
     to ensure that there are no shadowed variable names.
   *)

  Context {fruntime:foreign_runtime}.

  Fixpoint nnrc_global_vars (e:nnrc) : list var :=
    match e with
    | NNRCGetConstant x => x :: nil
    | NNRCVar x => nil
    | NNRCConst d => nil
    | NNRCBinop bop e1 e2 => nnrc_global_vars e1 ++ nnrc_global_vars e2
    | NNRCUnop uop e1 => nnrc_global_vars e1
    | NNRCLet x e1 e2 => (nnrc_global_vars e1 ++ remove string_eqdec x (nnrc_global_vars e2))
    | NNRCFor x e1 e2 => (nnrc_global_vars e1 ++ remove string_eqdec x (nnrc_global_vars e2))
    | NNRCIf e1 e2 e3 =>  nnrc_global_vars e1 ++ nnrc_global_vars e2 ++ nnrc_global_vars e3
    | NNRCEither ed xl el xr er => nnrc_global_vars ed ++ (remove string_eqdec xl (nnrc_global_vars el)) ++ (remove string_eqdec xr (nnrc_global_vars er))
    | NNRCGroupBy g sl e => nnrc_global_vars e
    end.
  
  (* Java equivalent: NnrcOptimizer.nrc_bound_vars *)
  Fixpoint nnrc_bound_vars (e:nnrc) : list var :=
    match e with
    | NNRCGetConstant x => nil
    | NNRCVar x => nil
    | NNRCConst d => nil
    | NNRCBinop bop e1 e2 => nnrc_bound_vars e1 ++ nnrc_bound_vars e2
    | NNRCUnop uop e1 => nnrc_bound_vars e1
    | NNRCLet x e1 e2 => x :: (nnrc_bound_vars e1 ++ nnrc_bound_vars e2)
    | NNRCFor x e1 e2 => x :: (nnrc_bound_vars e1 ++ nnrc_bound_vars e2)
    | NNRCIf e1 e2 e3 =>  nnrc_bound_vars e1 ++ nnrc_bound_vars e2 ++ nnrc_bound_vars e3
    | NNRCEither ed xl el xr er =>  xl :: xr :: nnrc_bound_vars ed ++ nnrc_bound_vars el++ nnrc_bound_vars er
    | NNRCGroupBy g s e => nnrc_bound_vars e
    end.

  (* Java equivalent: JavaScriptBackend.nnrc_free_vars *)
  Fixpoint nnrc_free_vars (e:nnrc) : list var :=
    match e with
    | NNRCGetConstant x => nil
    | NNRCVar x => x :: nil
    | NNRCConst d => nil
    | NNRCBinop bop e1 e2 => nnrc_free_vars e1 ++ nnrc_free_vars e2
    | NNRCUnop uop e1 => nnrc_free_vars e1
    | NNRCLet x e1 e2 => (nnrc_free_vars e1 ++ remove string_eqdec x (nnrc_free_vars e2))
    | NNRCFor x e1 e2 => (nnrc_free_vars e1 ++ remove string_eqdec x (nnrc_free_vars e2))
    | NNRCIf e1 e2 e3 =>  nnrc_free_vars e1 ++ nnrc_free_vars e2 ++ nnrc_free_vars e3
    | NNRCEither ed xl el xr er => nnrc_free_vars ed ++ (remove string_eqdec xl (nnrc_free_vars el)) ++ (remove string_eqdec xr (nnrc_free_vars er))
    | NNRCGroupBy g sl e => nnrc_free_vars e
    end.

  Definition nnrc_vars e := nnrc_free_vars e ++ nnrc_bound_vars e.

  (* capture avoiding substitution *)
  (* Java equivalent: NnnrcOptimizer.nnrc_subst *)
  Fixpoint nnrc_subst (e:nnrc) (x:var) (e':nnrc) : nnrc 
    := match e with
       | NNRCGetConstant y => NNRCGetConstant y
       | NNRCVar y => if y == x then e' else NNRCVar y
       | NNRCConst d => NNRCConst d
       | NNRCBinop bop e1 e2 => NNRCBinop bop
                                          (nnrc_subst e1 x e') 
                                          (nnrc_subst e2 x e')
       | NNRCUnop uop e1 => NNRCUnop uop (nnrc_subst e1 x e')
       | NNRCLet y e1 e2 => 
         NNRCLet y 
                 (nnrc_subst e1 x e') 
                 (if y == x then e2 else nnrc_subst e2 x e')
       | NNRCFor y e1 e2 => 
         NNRCFor y 
                 (nnrc_subst e1 x e') 
                 (if y == x then e2 else nnrc_subst e2 x e')
       | NNRCIf e1 e2 e3 =>  NNRCIf
                               (nnrc_subst e1 x e')
                               (nnrc_subst e2 x e')
                               (nnrc_subst e3 x e')
       | NNRCEither ed xl el xr er =>
         NNRCEither (nnrc_subst ed x e')
                    xl
                    (if xl == x then el else nnrc_subst el x e')
                    xr
                    (if xr == x then er else nnrc_subst er x e')
       | NNRCGroupBy g sl e1 => NNRCGroupBy g sl (nnrc_subst e1 x e')
       end.

  Lemma nnrc_subst_not_free e x : 
    ~ In x (nnrc_free_vars e) ->
    forall e', nnrc_subst e x e' = e.
  Proof.
    induction e; simpl in *; intros.
    - intuition.
    - intuition. dest_eqdec; intuition.
    - intuition.
    - intuition; congruence.
    - intuition; congruence.
    - intuition. dest_eqdec; [congruence | ].
      f_equal; auto.
      apply nin_app_or in H.
      intuition.
      apply IHe2.
      intro inn; apply H2.
      apply remove_in_neq; auto.
    - intuition. dest_eqdec; [congruence | ].
      f_equal; auto.
      apply nin_app_or in H.
      destruct H.
      apply IHe2.
      intro inn; apply H1.
      apply remove_in_neq; auto.
    - repeat rewrite nin_app_or in H.
      intuition.
      congruence.
    - repeat rewrite nin_app_or in H. 
      destruct H as [?[??]].
      rewrite IHe1; trivial.
      f_equal;dest_eqdec; trivial.
      + apply IHe2; rewrite remove_in_neq; eauto.
      + apply IHe3; rewrite remove_in_neq; eauto.
    - intuition; congruence.
  Qed.

  Lemma nnrc_subst_remove_one_free e x e' :
    nnrc_free_vars e' = nil ->
    nnrc_free_vars (nnrc_subst e x e') = remove string_eqdec x (nnrc_free_vars e).
  Proof.
    intros Hfv_e'.
    nnrc_cases (induction e) Case; try reflexivity.
    - Case "NNRCVar"%string.
      simpl.
      case (equiv_dec v x).
      + intros Heq; rewrite Heq in *; clear Heq.
        destruct (string_eqdec x x); try congruence.
        assumption.
      + intros Heq.
        destruct (string_eqdec x v); try congruence.
        reflexivity.
    - Case "NNRCBinop"%string.
      simpl.
      rewrite IHe1.
      rewrite IHe2.
      apply list_remove_append_distrib.
    - Case "NNRCUnop"%string.
      simpl.
      rewrite IHe.
      reflexivity.
    - Case "NNRCLet"%string.
      simpl.
      rewrite IHe1.
      case (equiv_dec v x).
      + intros Heq.
        assert (v = x) as Hrew.
        rewrite Heq; reflexivity.
        rewrite Hrew in *; clear Hrew Heq.
        rewrite <- list_remove_append_distrib.
        rewrite list_remove_idempotent.
        reflexivity.
      + intros Heq.
        rewrite IHe2.
        rewrite <- list_remove_append_distrib.
        rewrite list_remove_commute.
        reflexivity.
    - Case "NNRCFor"%string.
      simpl.
      rewrite IHe1.
      case (equiv_dec v x).
      + intros Heq.
        assert (v = x) as Hrew.
        rewrite Heq; reflexivity.
        rewrite Hrew in *; clear Hrew Heq.
        rewrite <- list_remove_append_distrib.
        rewrite list_remove_idempotent.
        reflexivity.
      + intros Heq.
        rewrite IHe2.
        rewrite <- list_remove_append_distrib.
        rewrite list_remove_commute.
        reflexivity.
    - Case "NNRCIf"%string.
      simpl.
      rewrite IHe1.
      rewrite IHe2.
      rewrite IHe3.
      rewrite <- list_remove_append_distrib.
      rewrite <- list_remove_append_distrib.
      reflexivity.
    - Case "NNRCEither"%string.
      simpl.
      rewrite IHe1.
      case (equiv_dec v x).
      + intros Heq.
        assert (v = x) as Hrew.
        rewrite Heq; reflexivity.
        rewrite Hrew in *; clear Hrew Heq.
        rewrite <- list_remove_append_distrib.
        case (equiv_dec v0 x).
        * intros Heq.
          assert (v0 = x) as Hrew.
          rewrite Heq; reflexivity.
          rewrite Hrew in *; clear Hrew Heq.
          rewrite <- list_remove_append_distrib.
          rewrite list_remove_idempotent.
          rewrite list_remove_idempotent.
          reflexivity.
        * intros Heq.
          rewrite IHe3.
          rewrite <- list_remove_append_distrib.
          rewrite list_remove_idempotent.
          rewrite list_remove_commute.
          reflexivity.
      + intros Heq.
        case (equiv_dec v0 x).
        * intros Heq0.
          assert (v0 = x) as Hrew.
          rewrite Heq0; reflexivity.
          rewrite Hrew in *; clear Hrew Heq0.
          rewrite IHe2.
          rewrite <- list_remove_append_distrib.
          rewrite <- list_remove_append_distrib.
          rewrite list_remove_commute.
          rewrite list_remove_idempotent.
          reflexivity.
        * intros Heq0.
          rewrite IHe2.
          rewrite IHe3.
          rewrite <- list_remove_append_distrib.
          rewrite <- list_remove_append_distrib.
          rewrite list_remove_commute.
          rewrite (list_remove_commute v0 x).
          reflexivity.
    - Case "NNRCGroupBy"%string.
      simpl.
      rewrite IHe.
      reflexivity.
  Qed.

  Lemma nnrc_subst_not_in_free e x e':
    nnrc_free_vars e' = nil ->
    forall y,
      In y (nnrc_free_vars (nnrc_subst e x e')) -> x <> y.
  Proof.
    intros Hfv_e'.
    nnrc_cases (induction e) Case.
    - Case "NNRCGetConstant"%string.
      contradiction.
    - Case "NNRCVar"%string.
      simpl.
      case (equiv_dec v x).
      + intros Heq y.
        rewrite Hfv_e'.
        contradiction.
      + intros Heq y.
        simpl.
        intros H; destruct H; try contradiction.
        rewrite H in *.
        congruence.
    - Case "NNRCConst"%string.
      contradiction.
    - Case "NNRCBinop"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply IHe1 in H.
        assumption.
      + apply IHe2 in H.
        assumption.
    - Case "NNRCUnop"%string.
      simpl.
      intros y Hy.
      apply IHe in Hy.
      assumption.
    - Case "NNRCLet"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy; auto.
      match_destr_in H; unfold equiv, complement in *; intros.
      + apply IHe2.
        rewrite e in H.
        rewrite nnrc_subst_remove_one_free; auto.
      + apply IHe2.
        apply remove_in_neq in H; auto.
        apply (list_in_remove_impl_diff _ _ (nnrc_free_vars (nnrc_subst e2 x e'))).
        assumption.
    - Case "NNRCFor"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply IHe1; auto.
      + match_destr_in H.
        * rewrite e in *; clear e.
          assert (y <> x); try congruence.
          apply (list_in_remove_impl_diff _ _ (nnrc_free_vars e2)).
          assumption.
        * apply IHe2.
          apply remove_in_neq in H; auto.
          apply (list_in_remove_impl_diff _ _ (nnrc_free_vars (nnrc_subst e2 x e'))).
          assumption.
    - Case "NNRCIf"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply IHe1 in H.
        assumption.
      + destruct H.
        * apply IHe2.
          assumption.
        * apply IHe3.
          assumption.
    - Case "NNRCEither"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply IHe1 in H.
        assumption.
      + rewrite in_app_iff in H.
        destruct H.
        * match_destr_in H.
          (* case "v = x" *)
          assert (v = x) as Hrew; [ rewrite e; reflexivity | ].
          rewrite Hrew in *; clear Hrew e.
          assert (y <> x); try congruence.
          apply (list_in_remove_impl_diff _ _ (nnrc_free_vars e2)).
          assumption.
          (* case "v <> x" *)
          apply IHe2.
          apply remove_in_neq in H; auto.
          apply (list_in_remove_impl_diff _ _ (nnrc_free_vars (nnrc_subst e2 x e'))).
          assumption.
        * match_destr_in H.
          (* case "v0 = x" *)
          assert (v0 = x) as Hrew; [ rewrite e; reflexivity | ].
          rewrite Hrew in *; clear Hrew e.
          assert (y <> x); try congruence.
          apply (list_in_remove_impl_diff _ _ (nnrc_free_vars e3)).
          assumption.
          (* case "v <> x" *)
          apply IHe3.
          apply remove_in_neq in H; auto.
          apply (list_in_remove_impl_diff _ _ (nnrc_free_vars (nnrc_subst e3 x e'))).
          assumption.
    - Case "NNRCGroupBy"%string.
      simpl.
      intros y Hy.
      apply IHe in Hy.
      assumption.
  Qed.

  Lemma nnrc_subst_remove_free e x e':
    nnrc_free_vars e' = nil ->
    forall y,
      In y (nnrc_free_vars (nnrc_subst e x e')) -> In y (nnrc_free_vars e).
  Proof.
    intros Hfv_e'.
    nnrc_cases (induction e) Case.
    - Case "NNRCGetConstant"%string.
      contradiction.
    - Case "NNRCVar"%string.
      simpl.
      case (equiv_dec v x); auto.
      intros Heq y; rewrite Heq in *; clear Heq.
      rewrite Hfv_e'.
      contradiction.
    - Case "NNRCConst"%string.
      contradiction.
    - Case "NNRCBinop"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply IHe1 in H.
        apply in_or_app; auto.
      + apply IHe2 in H.
        apply in_or_app; auto.
    - Case "NNRCUnop"%string.
      simpl.
      intros y Hy.
      apply IHe in Hy.
      assumption.
    - Case "NNRCLet"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply in_or_app; auto.
      + apply in_or_app; auto.
        right.
        match_destr_in H; auto.
        apply (list_remove_in _ _ (nnrc_free_vars (nnrc_subst e2 x e'))); auto.
    - Case "NNRCFor"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply in_or_app; auto.
      + apply in_or_app; auto.
        right.
        match_destr_in H; auto.
        apply (list_remove_in _ _ (nnrc_free_vars (nnrc_subst e2 x e'))); auto.
    - Case "NNRCIf"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply IHe1 in H.
        apply in_or_app; auto.
      + destruct H.
        apply IHe2 in H.
        apply in_or_app; auto.
        right.
        apply in_or_app; auto.
        apply IHe3 in H.
        apply in_or_app; auto.
        right.
        apply in_or_app; auto.
    - Case "NNRCEither"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply IHe1 in H.
        apply in_or_app; auto.
      + rewrite in_app_iff in H.
        destruct H.
        * match_destr_in H.
          (* case "v = x" *)
          assert (v = x) as Hrew; [ rewrite e; reflexivity | ].
          rewrite Hrew in *; clear Hrew e.
          apply in_or_app; auto.
          right.
          apply in_or_app; auto.
          (* case "v <> x" *)
          apply in_or_app; auto.
          right.
          apply in_or_app; auto.
          left.
          apply (list_remove_in _ _ (nnrc_free_vars (nnrc_subst e2 x e'))); auto.
        * match_destr_in H.
          (* case "v0 = x" *)
          assert (v0 = x) as Hrew; [ rewrite e; reflexivity | ].
          rewrite Hrew in *; clear Hrew e.
          apply in_or_app; auto.
          right.
          apply in_or_app; auto.
          (* case "v0 <> x" *)
          apply in_or_app; auto.
          right.
          apply in_or_app; auto.
          right.
          apply (list_remove_in _ _ (nnrc_free_vars (nnrc_subst e3 x e'))); auto.
    - Case "NNRCGroupBy"%string.
      simpl.
      intros y Hy.
      apply IHe in Hy.
      assumption.
  Qed.

  (* picks a variable that is fresh even with respect to bound variables *)
  Definition really_fresh_in (sep:string) (oldvar:var) (avoid:list var) (e:nnrc) 
    := fresh_var_from
         sep
         oldvar
         (avoid ++ nnrc_free_vars e ++ nnrc_bound_vars e).

  Lemma really_fresh_in_fresh (sep:string) (oldvar:var) (avoid:list var) (e:nnrc)  :
    ~ In (really_fresh_in sep oldvar avoid e)
      (avoid ++ nnrc_free_vars e ++ nnrc_bound_vars e).
  Proof.
    unfold really_fresh_in.
    apply fresh_var_from_fresh.
  Qed.
  
  Lemma really_fresh_from_avoid sep old avoid (e:nnrc) :
    ~ In (really_fresh_in sep old avoid e) avoid.
  Proof.
    intros inn1.
    apply (really_fresh_in_fresh sep old avoid e).
    repeat rewrite in_app_iff; intuition.
  Qed.

  Lemma really_fresh_from_free sep old avoid (e:nnrc) :
    ~ In (really_fresh_in sep old avoid e) (nnrc_free_vars e).
  Proof.
    intros inn1.
    apply (really_fresh_in_fresh sep old avoid e).
    repeat rewrite in_app_iff; intuition.
  Qed.

  Lemma really_fresh_from_bound sep old avoid (e:nnrc) :
    ~ In (really_fresh_in sep old avoid e) (nnrc_bound_vars e).
  Proof.
    intros inn1.
    apply (really_fresh_in_fresh sep old avoid e).
    repeat rewrite in_app_iff; intuition.
  Qed.

  Lemma nnrc_bound_vars_subst_preserved e x e' :
    nnrc_bound_vars e' = nil -> 
    nnrc_bound_vars (nnrc_subst e x e') = nnrc_bound_vars e.
  Proof.
    induction e; simpl; intuition; repeat dest_eqdec; simpl; try congruence.
  Qed.

  Lemma nnrc_free_vars_subst e v n: ~ In n (nnrc_bound_vars e) ->
                                    nnrc_free_vars ((nnrc_subst e v (NNRCVar n))) = 
                                    replace_all (nnrc_free_vars e) v n.
  Proof.
    unfold var.
    induction e; simpl; trivial; 
      unfold equiv_dec, nat_eq_eqdec;
      unfold replace_all in *;try repeat rewrite map_app.
    - destruct (string_eqdec v0 v); simpl; trivial.
    - intros; f_equal; intuition.
    - intuition. f_equal; auto.
      destruct (string_eqdec v0 v); unfold equiv in *; subst.
      + rewrite (replace_all_remove_eq' (nnrc_free_vars e2) v n); trivial.
      + rewrite H2. apply replace_all_remove_neq; auto.
    - intuition. f_equal; auto.
      destruct (string_eqdec v0 v); unfold equiv in *; subst.
      + rewrite (replace_all_remove_eq' (nnrc_free_vars e2) v n); trivial.
      + rewrite H2. apply replace_all_remove_neq; auto.
    - intros. rewrite nin_app_or in H; destruct H as [? HH].
      rewrite nin_app_or in HH; intuition. 
      rewrite H2, H3, H4; trivial.
    - intros.
      apply not_or in H. destruct H.
      apply not_or in H0. destruct H0.
      apply nin_app_or in H1; destruct H1.
      apply nin_app_or in H2; destruct H2.
      rewrite IHe1; trivial.
      f_equal.
      match_destr; match_destr; unfold equiv in *; subst;
        try rewrite (replace_all_remove_eq' (nnrc_free_vars e2) v n);
        try rewrite (replace_all_remove_eq' (nnrc_free_vars e3) v n);
        trivial;
        repeat rewrite <- (replace_all_remove_neq) by congruence;
        try rewrite IHe2 by congruence;
        try rewrite IHe3 by congruence;
        trivial.
      (* For some reason, rewrite does not work here.  I cannot figure out the cause *)
      + f_equal.
        generalize (replace_all_remove_neq (eqdec:=string_eqdec) (nnrc_free_vars e3) v1 v n); intros eqq.
        cut_to eqq ; [|  intuition..].
        etransitivity; [| eapply eqq].
        trivial.
      + f_equal.
        generalize (replace_all_remove_neq (eqdec:=string_eqdec) (nnrc_free_vars e2) v0 v n); intros eqq.
        cut_to eqq ; [|  intuition..].
        etransitivity; [| eapply eqq].
        trivial.
      + f_equal.
        * generalize (replace_all_remove_neq (eqdec:=string_eqdec) (nnrc_free_vars e2) v0 v n); intros eqq.
          cut_to eqq ; [|  intuition..].
          etransitivity; [| eapply eqq].
          trivial.
        * generalize (replace_all_remove_neq (eqdec:=string_eqdec) (nnrc_free_vars e3) v1 v n); intros eqq.
          cut_to eqq ; [|  intuition..].
          etransitivity; [| eapply eqq].
          trivial.
  Qed.

  Lemma nnrc_subst_eq e v : nnrc_subst e v (NNRCVar v) = e.
  Proof.
    induction e; simpl; repeat match_destr; congruence.
  Qed.

  Lemma incl_letvars1 v e1 e2 env :
    incl (nnrc_vars (NNRCLet v e1 e2)) env ->
    incl (nnrc_vars e1) env.
  Proof.
    intros inclvars.
    transitivity env; unfold incl, nnrc_vars in *;
      simpl in *; auto 2; intros.
    apply inclvars.
    rewrite in_app_iff in H.
    repeat rewrite in_app_iff.
    simpl; rewrite in_app_iff.
    destruct H; try tauto.
  Qed.
  
  Lemma incl_letvars2 v e1 e2 env :
    incl (nnrc_vars (NNRCLet v e1 e2)) env ->
    incl (nnrc_vars e2) (env).
  Proof.
    intros inclvars.
    transitivity env; unfold incl, nnrc_vars in *;
      simpl in *; auto 2; intros.
    apply inclvars.
    rewrite in_app_iff in H.
    repeat rewrite in_app_iff.
    simpl; rewrite in_app_iff.
    destruct H; try tauto.
    destruct (a == v).
    - red in e; subst; auto.
    - left; right.
      apply remove_in_neq; auto.
  Qed.
  
  Section core.
    (* Proof for operations that preserve core NNRC property *)
    Lemma nnrc_subst_preserve_core n1 n2 v1 :
      nnrcIsCore n1 -> nnrcIsCore n2 -> nnrcIsCore (nnrc_subst n1 v1 n2).
    Proof.
      induction n1; simpl; intros; intuition;
        try (destruct (equiv_dec v v1); trivial);
        destruct (equiv_dec v0 v1); trivial.
    Qed.

  End core.
  
  Section FreeVars.
    Fixpoint nnrc_free_variables (q:nnrc) : list var := nnrc_free_vars q.
  End FreeVars.

End cNNRCVars.