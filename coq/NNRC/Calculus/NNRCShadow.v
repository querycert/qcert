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

Section NNRCShadow.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import Peano_dec.
  Require Import EquivDec Decidable.

  Require Import Utils BasicRuntime.

  Require Import NNRC.

  Close Scope nrc_scope.
  
  (* Since we are translating from a language with scoped variables
     (For) to a language without scoping, we need to alpha convert the input
     to ensure that there are no shadowed variable names.
   *)

  Context {fruntime:foreign_runtime}.

  (* Java equivalent: NnrcOptimizer.nrc_bound_vars *)
  Fixpoint nrc_bound_vars (e:nrc) : list var :=
    match e with
    | NRCVar x => nil
    | NRCConst d => nil
    | NRCBinop bop e1 e2 => nrc_bound_vars e1 ++ nrc_bound_vars e2
    | NRCUnop uop e1 => nrc_bound_vars e1
    | NRCLet x e1 e2 => x :: (nrc_bound_vars e1 ++ nrc_bound_vars e2)
    | NRCFor x e1 e2 => x :: (nrc_bound_vars e1 ++ nrc_bound_vars e2)
    | NRCIf e1 e2 e3 =>  nrc_bound_vars e1 ++ nrc_bound_vars e2 ++ nrc_bound_vars e3
    | NRCEither ed xl el xr er =>  xl :: xr :: nrc_bound_vars ed ++ nrc_bound_vars el++ nrc_bound_vars er
    end.

  (* Java equivalent: JavaScriptBackend.nrc_free_vars *)
  Fixpoint nrc_free_vars (e:nrc) : list var :=
    match e with
    | NRCVar x => x :: nil
    | NRCConst d => nil
    | NRCBinop bop e1 e2 => nrc_free_vars e1 ++ nrc_free_vars e2
    | NRCUnop uop e1 => nrc_free_vars e1
    | NRCLet x e1 e2 => (nrc_free_vars e1 ++ remove string_eqdec x (nrc_free_vars e2))
    | NRCFor x e1 e2 => (nrc_free_vars e1 ++ remove string_eqdec x (nrc_free_vars e2))
    | NRCIf e1 e2 e3 =>  nrc_free_vars e1 ++ nrc_free_vars e2 ++ nrc_free_vars e3
    | NRCEither ed xl el xr er => nrc_free_vars ed ++ (remove string_eqdec xl (nrc_free_vars el)) ++ (remove string_eqdec xr (nrc_free_vars er))
    end.

  Require Import Arith Max.

  (* capture avoiding substitution *)
  (* Java equivalent: NnrcOptimizer.nrc_subst *)
  Fixpoint nrc_subst (e:nrc) (x:var) (e':nrc) : nrc 
    := match e with
       | NRCVar y => if y == x then e' else NRCVar y
       | NRCConst d => NRCConst d
       | NRCBinop bop e1 e2 => NRCBinop bop
                                        (nrc_subst e1 x e') 
                                        (nrc_subst e2 x e')
       | NRCUnop uop e1 => NRCUnop uop (nrc_subst e1 x e')
       | NRCLet y e1 e2 => 
         NRCLet y 
                (nrc_subst e1 x e') 
                (if y == x then e2 else nrc_subst e2 x e')
       | NRCFor y e1 e2 => 
         NRCFor y 
                (nrc_subst e1 x e') 
                (if y == x then e2 else nrc_subst e2 x e')
       | NRCIf e1 e2 e3 =>  NRCIf
                              (nrc_subst e1 x e')
                              (nrc_subst e2 x e')
                              (nrc_subst e3 x e')
       | NRCEither ed xl el xr er =>
         NRCEither (nrc_subst ed x e')
                   xl
                   (if xl == x then el else nrc_subst el x e')
                   xr
                   (if xr == x then er else nrc_subst er x e')
       end.

  Lemma nrc_subst_not_free e x : 
    ~ In x (nrc_free_vars e) ->
    forall e', nrc_subst e x e' = e.
  Proof.
    induction e; simpl in *; intros.
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
  Qed.

  Lemma nrc_subst_remove_one_free e x e' :
    nrc_free_vars e' = nil ->
    nrc_free_vars (nrc_subst e x e') = remove string_eqdec x (nrc_free_vars e).
  Proof.
    intros Hfv_e'.
    nrc_cases (induction e) Case; try reflexivity.
    - Case "NRCVar"%string.
      simpl.
      case (equiv_dec v x).
      + intros Heq; rewrite Heq in *; clear Heq.
        destruct (string_eqdec x x); try congruence.
        assumption.
      + intros Heq.
        destruct (string_eqdec x v); try congruence.
        reflexivity.
    - Case "NRCBinop"%string.
      simpl.
      rewrite IHe1.
      rewrite IHe2.
      apply list_remove_append_distrib.
    - Case "NRCUnop"%string.
      simpl.
      rewrite IHe.
      reflexivity.
    - Case "NRCLet"%string.
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
    - Case "NRCFor"%string.
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
    - Case "NRCIf"%string.
      simpl.
      rewrite IHe1.
      rewrite IHe2.
      rewrite IHe3.
      rewrite <- list_remove_append_distrib.
      rewrite <- list_remove_append_distrib.
      reflexivity.
    - Case "NRCEither"%string.
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
  Qed.

  Lemma nrc_subst_not_in_free e x e':
    nrc_free_vars e' = nil ->
    forall y,
      In y (nrc_free_vars (nrc_subst e x e')) -> x <> y.
  Proof.
    intros Hfv_e'.
    nrc_cases (induction e) Case.
    - Case "NRCVar"%string.
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
    - Case "NRCConst"%string.
      contradiction.
    - Case "NRCBinop"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply IHe1 in H.
        assumption.
      + apply IHe2 in H.
        assumption.
    - Case "NRCUnop"%string.
      simpl.
      intros y Hy.
      apply IHe in Hy.
      assumption.
    - Case "NRCLet"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy; auto.
      match_destr_in H; unfold equiv, complement in *; intros.
      + apply IHe2.
        rewrite e in H.
        rewrite nrc_subst_remove_one_free; auto.
      + apply IHe2.
        apply remove_in_neq in H; auto.
        apply (list_in_remove_impl_diff _ _ (nrc_free_vars (nrc_subst e2 x e'))).
        assumption.
    - Case "NRCFor"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply IHe1; auto.
      + match_destr_in H.
        * rewrite e in *; clear e.
          assert (y <> x); try congruence.
          apply (list_in_remove_impl_diff _ _ (nrc_free_vars e2)).
          assumption.
        * apply IHe2.
          apply remove_in_neq in H; auto.
          apply (list_in_remove_impl_diff _ _ (nrc_free_vars (nrc_subst e2 x e'))).
          assumption.
    - Case "NRCIf"%string.
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
    - Case "NRCEither"%string.
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
          apply (list_in_remove_impl_diff _ _ (nrc_free_vars e2)).
          assumption.
          (* case "v <> x" *)
          apply IHe2.
          apply remove_in_neq in H; auto.
          apply (list_in_remove_impl_diff _ _ (nrc_free_vars (nrc_subst e2 x e'))).
          assumption.
        * match_destr_in H.
          (* case "v0 = x" *)
          assert (v0 = x) as Hrew; [ rewrite e; reflexivity | ].
          rewrite Hrew in *; clear Hrew e.
          assert (y <> x); try congruence.
          apply (list_in_remove_impl_diff _ _ (nrc_free_vars e3)).
          assumption.
          (* case "v <> x" *)
          apply IHe3.
          apply remove_in_neq in H; auto.
          apply (list_in_remove_impl_diff _ _ (nrc_free_vars (nrc_subst e3 x e'))).
          assumption.
  Qed.

  Lemma nrc_subst_remove_free e x e':
    nrc_free_vars e' = nil ->
    forall y,
      In y (nrc_free_vars (nrc_subst e x e')) -> In y (nrc_free_vars e).
  Proof.
    intros Hfv_e'.
    nrc_cases (induction e) Case.
    - Case "NRCVar"%string.
      simpl.
      case (equiv_dec v x); auto.
      intros Heq y; rewrite Heq in *; clear Heq.
      rewrite Hfv_e'.
      contradiction.
    - Case "NRCConst"%string.
      contradiction.
    - Case "NRCBinop"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply IHe1 in H.
        apply in_or_app; auto.
      + apply IHe2 in H.
        apply in_or_app; auto.
    - Case "NRCUnop"%string.
      simpl.
      intros y Hy.
      apply IHe in Hy.
      assumption.
    - Case "NRCLet"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply in_or_app; auto.
      + apply in_or_app; auto.
        right.
        match_destr_in H; auto.
        apply (list_remove_in _ _ (nrc_free_vars (nrc_subst e2 x e'))); auto.
    - Case "NRCFor"%string.
      intros y.
      simpl.
      rewrite in_app_iff.
      intros Hy.
      destruct Hy.
      + apply in_or_app; auto.
      + apply in_or_app; auto.
        right.
        match_destr_in H; auto.
        apply (list_remove_in _ _ (nrc_free_vars (nrc_subst e2 x e'))); auto.
    - Case "NRCIf"%string.
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
    - Case "NRCEither"%string.
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
          apply (list_remove_in _ _ (nrc_free_vars (nrc_subst e2 x e'))); auto.
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
          apply (list_remove_in _ _ (nrc_free_vars (nrc_subst e3 x e'))); auto.
  Qed.

  (* picks a variable that is fresh even with respect to bound variables *)
  Definition really_fresh_in (sep:string) (oldvar:var) (avoid:list var) (e:nrc) 
    := fresh_var_from
         sep
         oldvar
         (avoid ++ nrc_free_vars e ++ nrc_bound_vars e).

  Lemma really_fresh_in_fresh (sep:string) (oldvar:var) (avoid:list var) (e:nrc)  :
    ~ In (really_fresh_in sep oldvar avoid e)
         (avoid ++ nrc_free_vars e ++ nrc_bound_vars e).
  Proof.
    unfold really_fresh_in.
    apply fresh_var_from_fresh.
  Qed.
  
  Lemma really_fresh_from_avoid sep old avoid (e:nrc) :
    ~ In (really_fresh_in sep old avoid e) avoid.
  Proof.
    intros inn1.
    apply (really_fresh_in_fresh sep old avoid e).
    repeat rewrite in_app_iff; intuition.
  Qed.

  Lemma really_fresh_from_free sep old avoid (e:nrc) :
    ~ In (really_fresh_in sep old avoid e) (nrc_free_vars e).
  Proof.
    intros inn1.
    apply (really_fresh_in_fresh sep old avoid e).
    repeat rewrite in_app_iff; intuition.
  Qed.

  Lemma really_fresh_from_bound sep old avoid (e:nrc) :
    ~ In (really_fresh_in sep old avoid e) (nrc_bound_vars e).
  Proof.
    intros inn1.
    apply (really_fresh_in_fresh sep old avoid e).
    repeat rewrite in_app_iff; intuition.
  Qed.

  Require Import Bool.

  Fixpoint shadow_free (e:nrc) : bool :=
    match e with
    | NRCVar x => true
    | NRCConst d => true
    | NRCBinop bop e1 e2 => shadow_free e1 && shadow_free e2
    | NRCUnop uop e1 => shadow_free e1
    | NRCLet x e1 e2 => 
      (if in_dec string_eqdec x (nrc_bound_vars e2) then false else true) 
        && shadow_free e1 && shadow_free e2
    | NRCFor x e1 e2 => 
      (if in_dec string_eqdec x (nrc_bound_vars e2) then false else true) 
        && shadow_free e1 && shadow_free e2
    | NRCIf e1 e2 e3 =>  shadow_free e1 && shadow_free e2 && shadow_free e3
    | NRCEither ed xl el xr er =>
      (if in_dec string_eqdec xl (nrc_bound_vars el) then false else true)
        && (if in_dec string_eqdec xr (nrc_bound_vars er) then false else true) 
        && shadow_free ed && shadow_free el && shadow_free er
    end.

  Definition pick_new_really_fresh_in (sep:string) (name:var) (avoid:list var) (e:nrc)
    := if in_dec string_eqdec name (avoid ++ (nrc_free_vars e) ++ (nrc_bound_vars e))
       then really_fresh_in sep name avoid e
       else name.

  (* Java equivalent: NnrcOptimizer.pick_same_really_fresh_in *)
  Definition pick_same_really_fresh_in (sep:string) (name:var) (avoid:list var) (e:nrc)
    := if in_dec string_eqdec name (avoid ++ (nrc_bound_vars e))
       then really_fresh_in sep name avoid e
       else name.

  (* unshadow preserves semantics and ensures that there is no shadowing *)
  Section unsh.
   (* Java equivalent: NnrcOptimizer.nrc_rename_lazy *)
    Definition nrc_rename_lazy (e:nrc) (oldvar newvar:var)
      := if oldvar == newvar
         then e
         else (nrc_subst e oldvar (NRCVar newvar)).

    Context (sep:string).
    (* as part of unshadowing, we also support a user defined renaming function *)
    Context (renamer:string->string).
    Context (avoid:list var).

   (* Java equivalent: NnrcOptimizer.nrc_pick_name *)
    Definition nrc_pick_name (oldvar:var) (e:nrc) 
      := let name := renamer oldvar in
         if name == oldvar
         then pick_same_really_fresh_in sep name avoid e
         else pick_new_really_fresh_in sep name avoid e.
    
  (* Java equivalent: NnrcOptimizer.unshadow *)
  Fixpoint unshadow (e:nrc) : nrc
    :=   
      match e with
      | NRCVar x => NRCVar x
      | NRCConst d => NRCConst d
      | NRCBinop bop e1 e2 => NRCBinop bop (unshadow e1) (unshadow e2)
      | NRCUnop uop e1 => NRCUnop uop (unshadow e1)
      | NRCLet x e1 e2 => 
        let e1' := unshadow e1 in
        let e2' := unshadow e2 in
        let x' := nrc_pick_name x e2' in
        NRCLet x' e1' (nrc_rename_lazy e2' x x')
      | NRCFor x e1 e2 => 
        let e1' := unshadow e1 in
        let e2' := unshadow e2 in
        let x' := nrc_pick_name x e2' in
        NRCFor x' e1' (nrc_rename_lazy e2' x x')
      | NRCIf e1 e2 e3 =>  NRCIf (unshadow e1) (unshadow e2) (unshadow e3)
      | NRCEither ed xl el xr er =>
        let ed' := unshadow ed in
        let el' := unshadow el in
        let er' := unshadow er in
        let xl' := nrc_pick_name xl el' in
        let xr' := nrc_pick_name xr er' in
        NRCEither ed' xl' (nrc_rename_lazy el' xl xl') xr' (nrc_rename_lazy er' xr xr')                end.
  
  Lemma nrc_bound_vars_subst_preserved e x e' :
    nrc_bound_vars e' = nil -> 
    nrc_bound_vars (nrc_subst e x e') = nrc_bound_vars e.
  Proof.
    induction e; simpl; intuition; repeat dest_eqdec; simpl; try congruence.
  Qed.

  Lemma no_bound_shadow_free e :
    nrc_bound_vars e = nil -> shadow_free e = true.
  Proof.
    induction e; simpl; intuition; repeat rewrite andb_true_iff.
    - apply app_eq_nil in H; intuition.
    - discriminate. 
    - discriminate.
    - apply app_eq_nil in H; 
      destruct H as [? HH]. 
      apply app_eq_nil in HH; intuition.
    - discriminate.
  Qed.

  Lemma nrc_shadow_free_subst_preserved e x e' :
    nrc_bound_vars e' = nil -> 
    shadow_free (nrc_subst e x e') = shadow_free e.
  Proof.
    induction e; simpl; try dest_eqdec; try solve[intuition; simpl; try congruence]; intros.
    - apply no_bound_shadow_free; auto.
    - rewrite nrc_bound_vars_subst_preserved; auto.
      destruct (in_dec string_eqdec v (nrc_bound_vars e2)); simpl; trivial.
      intuition congruence.
    - rewrite nrc_bound_vars_subst_preserved; auto.
      destruct (in_dec string_eqdec v (nrc_bound_vars e2)); simpl; trivial.
      intuition congruence.
    - rewrite IHe1 by trivial. dest_eqdec; trivial.
      match_destr.
      rewrite nrc_bound_vars_subst_preserved; trivial.
      simpl.
      match_destr; simpl.
      rewrite IHe3; trivial.
    - rewrite IHe1, IHe2 by trivial.
      match_destr; simpl.
      + rewrite nrc_bound_vars_subst_preserved in i; trivial.
         match_destr; simpl; congruence.
      + rewrite nrc_bound_vars_subst_preserved in n; trivial.
        dest_eqdec; try rewrite H3; trivial.
        * match_destr; simpl; match_destr; simpl.
           congruence.
        * { match_destr.
            - rewrite nrc_bound_vars_subst_preserved in i; trivial;
                match_destr; match_destr; try congruence.
            - rewrite nrc_bound_vars_subst_preserved in n0; trivial.
              rewrite IHe3 by trivial.
              repeat match_destr; try congruence.
          }
  Qed.

  Lemma nrc_shadow_free_rename_nrc_pick_name_preserved e v :
    shadow_free (nrc_rename_lazy e v (nrc_pick_name v e)) = shadow_free e.
  Proof.
    unfold nrc_rename_lazy.
    match_destr.
    rewrite nrc_shadow_free_subst_preserved; trivial.
  Qed.

  Lemma nrc_bound_vars_rename_lazy_preserved e oldvar newvar :
    nrc_bound_vars (nrc_rename_lazy e oldvar newvar) = nrc_bound_vars e.
  Proof.
    unfold nrc_rename_lazy.
    match_destr.
    apply nrc_bound_vars_subst_preserved; simpl.
    trivial.
  Qed.

  Lemma nrc_pick_name_avoid old (e:nrc) :
    ~ In (nrc_pick_name old e) avoid.
  Proof.
    unfold nrc_pick_name, pick_new_really_fresh_in, pick_same_really_fresh_in.
    match_destr.
    - match_destr.
      + intros inn1.
        apply (really_fresh_in_fresh sep (renamer old) avoid e).
        repeat rewrite in_app_iff; intuition.
      + rewrite in_app_iff in n; intuition.
    - match_destr.
      + intros inn1.
        apply (really_fresh_in_fresh sep (renamer old) avoid e).
        repeat rewrite in_app_iff; intuition.
      + rewrite in_app_iff in n; intuition.
  Qed.


  Lemma nrc_pick_name_bound old (e:nrc) :
    ~ In (nrc_pick_name old e) (nrc_bound_vars e).
  Proof.
    unfold nrc_pick_name, pick_new_really_fresh_in, pick_same_really_fresh_in.
    match_destr.
    - match_destr.
      + intros inn1.
        apply (really_fresh_in_fresh sep (renamer old) avoid e).
        repeat rewrite in_app_iff; intuition.
      + rewrite in_app_iff in n; intuition.
    - match_destr.
      + intros inn1.
        apply (really_fresh_in_fresh sep (renamer old) avoid e).
        repeat rewrite in_app_iff; intuition.
      + rewrite in_app_iff in n; intuition.
  Qed.
  
  Lemma unshadow_shadow_free (e:nrc) : 
    shadow_free (unshadow e) = true.
  Proof.
    induction e; simpl; intuition.
    - rewrite nrc_shadow_free_rename_nrc_pick_name_preserved.
      rewrite nrc_bound_vars_rename_lazy_preserved.
      rewrite IHe1, IHe2.
      match_destr.
      eelim nrc_pick_name_bound; eauto.
    - rewrite nrc_shadow_free_rename_nrc_pick_name_preserved.
      rewrite nrc_bound_vars_rename_lazy_preserved.
      rewrite IHe1, IHe2.
      match_destr.
      eelim nrc_pick_name_bound; eauto.
    - repeat rewrite nrc_shadow_free_rename_nrc_pick_name_preserved.
      repeat rewrite nrc_bound_vars_rename_lazy_preserved.
      rewrite IHe1, IHe2, IHe3.
      match_destr.
      + eelim nrc_pick_name_bound; eauto.
      + match_destr.
        eelim nrc_pick_name_bound; eauto.
  Qed.

  Lemma unshadow_avoid (e:nrc) x : 
    In x avoid -> ~ In x (nrc_bound_vars (unshadow e)).
  Proof.
    induction e; simpl; auto; intros
    ; repeat rewrite nrc_bound_vars_rename_lazy_preserved
    ; repeat rewrite in_app_iff; intuition
    ; subst; eelim nrc_pick_name_avoid; eauto.
  Qed.      

  Lemma nrc_free_vars_subst e v n: ~ In n (nrc_bound_vars e) ->
    nrc_free_vars ((nrc_subst e v (NRCVar n))) = 
    replace_all (nrc_free_vars e) v n.
  Proof.
    unfold var.
    induction e; simpl; trivial; 
    unfold equiv_dec, nat_eq_eqdec;
    unfold replace_all in *;try repeat rewrite map_app.
    - destruct (string_eqdec v0 v); simpl; trivial.
    - intros; f_equal; intuition.
    - intuition. f_equal; auto.
      destruct (string_eqdec v0 v); unfold equiv in *; subst.
      + rewrite (replace_all_remove_eq (nrc_free_vars e2) v n); trivial.
      + rewrite H3. apply replace_all_remove_neq; auto.
    - intuition. f_equal; auto.
      destruct (string_eqdec v0 v); unfold equiv in *; subst.
      + rewrite (replace_all_remove_eq (nrc_free_vars e2) v n); trivial.
      + rewrite H3. apply replace_all_remove_neq; auto.
    - intros. rewrite nin_app_or in H; destruct H as [? HH].
      rewrite nin_app_or in HH; intuition. 
      rewrite H3, H4, H5; trivial.
    - intros.
      apply not_or in H. destruct H.
      apply not_or in H0. destruct H0.
      apply nin_app_or in H1; destruct H1.
      apply nin_app_or in H2; destruct H2.
      rewrite IHe1; trivial.
      f_equal.
      match_destr; match_destr; unfold equiv in *; subst;
      try rewrite (replace_all_remove_eq (nrc_free_vars e2) v n);
        try rewrite (replace_all_remove_eq (nrc_free_vars e3) v n);
      trivial;
      repeat rewrite <- (replace_all_remove_neq) by congruence;
      try rewrite IHe2 by congruence;
      try rewrite IHe3 by congruence;
      trivial.
      (* For some reason, rewrite does not work here.  I cannot figure out the cause *)
      + f_equal.
      generalize (replace_all_remove_neq (eqdec:=string_eqdec) (nrc_free_vars e3) v1 v n); intros eqq.
      cut_to eqq ; [|  intuition..].
      etransitivity; [| eapply eqq].
      trivial.
      + f_equal.
      generalize (replace_all_remove_neq (eqdec:=string_eqdec) (nrc_free_vars e2) v0 v n); intros eqq.
      cut_to eqq ; [|  intuition..].
      etransitivity; [| eapply eqq].
      trivial.
      + f_equal.
        * generalize (replace_all_remove_neq (eqdec:=string_eqdec) (nrc_free_vars e2) v0 v n); intros eqq.
      cut_to eqq ; [|  intuition..].
      etransitivity; [| eapply eqq].
      trivial.
        * generalize (replace_all_remove_neq (eqdec:=string_eqdec) (nrc_free_vars e3) v1 v n); intros eqq.
      cut_to eqq ; [|  intuition..].
      etransitivity; [| eapply eqq].
      trivial.
  Qed.

  Lemma nrc_subst_eq e v : nrc_subst e v (NRCVar v) = e.
  Proof.
    induction e; simpl; repeat match_destr; congruence.
  Qed.
  
  Lemma nrc_pick_name_remove_free v e :
  remove string_eqdec (nrc_pick_name v e) 
     (nrc_free_vars (nrc_rename_lazy e v (nrc_pick_name v e))) =
   remove string_eqdec v (nrc_free_vars e).
  Proof.
    unfold nrc_pick_name.
    match_destr.
    - unfold pick_new_really_fresh_in.
      unfold nrc_rename_lazy.
      match_destr.
      + congruence.
      + unfold pick_same_really_fresh_in.
        match_destr.
        * rewrite nrc_free_vars_subst; [|apply really_fresh_from_bound].
          rewrite remove_replace_all_nin; [|apply really_fresh_from_free].
          trivial.
        * rewrite e0.
          rewrite nrc_subst_eq.
          trivial.
    - unfold pick_new_really_fresh_in.
      unfold nrc_rename_lazy.
      match_destr.
      + match_destr.
        * congruence.
        * rewrite nrc_free_vars_subst; [|apply really_fresh_from_bound].
          rewrite remove_replace_all_nin; [|apply really_fresh_from_free].
          trivial.
      + match_destr.
        * congruence.
        * repeat rewrite in_app_iff in n.
          rewrite nrc_free_vars_subst; [|intuition].
          rewrite remove_replace_all_nin; [|intuition].
          trivial.
  Qed.
          
  Lemma unshadow_nrc_free_vars (e:nrc) :
    nrc_free_vars (unshadow e) = nrc_free_vars e.
  Proof.
    induction e; simpl
    ; repeat rewrite nrc_pick_name_remove_free
    ; congruence.
  Qed.

  End unsh.


  Lemma nrc_eval_remove_duplicate_env {h:brand_relation_t} l v x l' x' l'' e :
    nrc_eval h (l ++ (v,x)::l' ++ (v,x')::l'') e =
    nrc_eval h (l ++ (v,x)::l' ++ l'') e.
  Proof.
    rewrite lookup_remove_duplicate; trivial.
  Qed.

  Lemma nrc_eval_remove_duplicate_env_weak {h:list (string*string)} v1 v2 x x' x'' l e :
    nrc_eval h ((v1,x)::(v2,x')::(v1,x'')::l) e =
    nrc_eval h ((v1,x)::(v2,x')::l) e.
  Proof.
    apply nrc_eval_lookup_equiv_prop; trivial.
    red; intros; simpl.
    match_destr.
  Qed.

  Lemma nrc_eval_remove_duplicate_env_weak_cons {h:list (string*string)} v1 v2 x x' x'' l e :
    nrc_eval h ((v1,x)::(v2,x')::(v2,x'')::l) e =
    nrc_eval h ((v1,x)::(v2,x')::l) e.
  Proof.
    apply nrc_eval_lookup_equiv_prop; trivial.
    red; intros; simpl.
    match_destr.
    match_destr.
  Qed.

  Lemma nrc_eval_remove_free_env {h:list (string*string)} l v x l' e :
          ~ In v (nrc_free_vars e) ->
          nrc_eval h (l ++ (v,x)::l') e = nrc_eval h (l ++ l') e.
  Proof.
    revert l v x l'.
    induction e; simpl; intros; trivial.
    - intuition. apply lookup_remove_nin; auto.
    - apply nin_app_or in H. rewrite IHe1, IHe2; intuition.
    - rewrite IHe; intuition.
    - apply nin_app_or in H. rewrite IHe1 by intuition.
      destruct (nrc_eval h (l ++ l') e1); trivial. 
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst.
      + generalize (@nrc_eval_remove_duplicate_env h nil v0 d l); simpl; auto.
      + generalize (IHe2 ((v,d)::l)); simpl; intros rr; rewrite rr; intuition.
         elim H2. apply remove_in_neq; auto.
    - apply nin_app_or in H. rewrite IHe1 by intuition.
      destruct (nrc_eval h (l ++ l') e1); trivial. destruct d; trivial.
      f_equal. apply rmap_ext; intros.
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst.
      + generalize (@nrc_eval_remove_duplicate_env h nil v0 x0 l); simpl; auto.
      + generalize (IHe2 ((v,x0)::l)); simpl; intros rr; rewrite rr; intuition.
         elim H3. apply remove_in_neq; auto.
    - apply nin_app_or in H; destruct H as [? HH]; apply nin_app_or in HH.
      rewrite IHe1, IHe2, IHe3; intuition.
    - repeat rewrite nin_app_or in H.
      rewrite IHe1 by intuition.
      match_destr. destruct d; trivial.
      + destruct (string_eqdec v v1); unfold Equivalence.equiv in * .
        * subst. generalize (@nrc_eval_remove_duplicate_env h nil v1 d l).
          simpl; trivial.
        * generalize (IHe2 ((v,d)::l)); simpl; intros r.
          apply r.
          rewrite <- (remove_in_neq _ v1 v) in H by intuition.
          intuition.
      + destruct (string_eqdec v0 v1); unfold Equivalence.equiv in * .
        * subst. generalize (@nrc_eval_remove_duplicate_env h nil v1 d l).
          simpl; trivial.
        * generalize (IHe3 ((v0,d)::l)); simpl; intros r.
          apply r.
          rewrite <- (remove_in_neq _ v1 v0) in H by intuition.
          intuition.
  Qed.

  Lemma nrc_eval_remove_free_env_weak {h:list (string*string)} v1 x1 v x e :
    ~ In v (nrc_free_vars e) ->
    nrc_eval h ((v1,x1)::(v,x)::nil) e = nrc_eval h ((v1,x1)::nil) e.
  Proof.
    assert ((v1,x1)::(v,x)::nil =
            ((v1,x1)::nil) ++ (v,x)::nil).
    reflexivity.
    assert (((v1,x1)::nil) = ((v1,x1)::nil ++ nil)).
    reflexivity.
    rewrite H; rewrite H0.
    apply nrc_eval_remove_free_env.
  Qed.

  Lemma nrc_eval_swap_neq {h:list (string*string)} l1 v1 x1 v2 x2 l2 e : v1 <> v2 ->
           nrc_eval h (l1++(v1,x1)::(v2,x2)::l2) e = 
           nrc_eval h (l1++(v2,x2)::(v1,x1)::l2) e.
  Proof.
    intros.
    rewrite lookup_swap_neq; trivial.
  Qed.

  Lemma nrc_eval_subst_dunit {h:list (string*string)} env e v :
    nrc_eval h ((v,dunit)::env) e = nrc_eval h env (nrc_subst e v (NRCConst dunit)).
  Proof.
    generalize env; clear env.
    nrc_cases (induction e) Case.
    - Case "NRCVar"%string.
      simpl.
      case (string_eqdec v0 v).
      + SCase "v0 = v"%string.
        intros Hv; rewrite Hv in *; clear Hv.
        match_destr; try congruence.
        match_destr; try congruence.
      + SCase "v0 <> v"%string.
        intros Hv ?.
        match_destr; try congruence.
        match_destr; try congruence.
    - Case "NRCConst"%string.
      reflexivity.
    - Case "NRCBinop"%string.
      intros env.
      simpl.
      rewrite IHe1.
      rewrite IHe2.
      reflexivity.
    - Case "NRCUnop"%string.
      intros env.
      simpl.
      rewrite IHe.
      reflexivity.
    - Case "NRCLet"%string.
      intros env.
      simpl.
      rewrite IHe1.
      destruct (nrc_eval h env (nrc_subst e1 v (NRCConst dunit))); try reflexivity.
      case (equiv_dec v0 v); unfold Equivalence.equiv in *.
      + SCase "v0 = v"%string.
        intros Hv; rewrite Hv in *; clear Hv.
        generalize (nrc_eval_remove_duplicate_env (h:=h) nil v d nil dunit env e2).
        simpl.
        trivial.
      + SCase "v0 <> v"%string.
        intros Hv.
        generalize (nrc_eval_swap_neq (h:=h) nil); simpl; intros eqq.
        rewrite eqq; auto.
    - Case "NRCFor"%string.
      intros env.
      simpl.
      rewrite IHe1.
      destruct (nrc_eval h env (nrc_subst e1 v (NRCConst dunit))); try reflexivity.
      destruct d; try reflexivity.
      apply lift_dcoll_inversion.
      apply rmap_ext.
      intros d Hd.
      match_destr; unfold Equivalence.equiv in * .
      + SCase "v0 = v"%string.
        subst.
        generalize (nrc_eval_remove_duplicate_env (h:=h) nil v d nil dunit env e2); simpl; trivial.
      + SCase "v0 <> v"%string.
        generalize (nrc_eval_swap_neq (h:=h) nil); simpl; intros eqq.
        rewrite eqq; auto.
    - Case "NRCIf"%string.
      intros env.
      simpl.
      unfold olift.
      rewrite IHe1.
      destruct (nrc_eval h env (nrc_subst e1 v (NRCConst dunit))); try reflexivity.
      destruct d; try reflexivity.
      destruct b.
      + SCase "b = true"%string.
        rewrite IHe2.
        reflexivity.
      + SCase "b = false"%string.
        rewrite IHe3.
        reflexivity.
    - Case "NRCEither"%string.
      intros env.
      simpl.
      rewrite IHe1.
      destruct (nrc_eval h env (nrc_subst e1 v (NRCConst dunit))); try reflexivity.
      destruct d; try reflexivity.
      + SCase "left"%string.
        match_destr; unfold Equivalence.equiv in * .
        * SSCase "v0 = v"%string.
          subst.
          generalize (nrc_eval_remove_duplicate_env (h:=h) nil v d nil dunit env e2).
          simpl; trivial.
        * SSCase "v0 <> v"%string.
          generalize (nrc_eval_swap_neq (h:=h) nil); simpl; intros eqq.
          rewrite eqq; auto.
      + SCase "right"%string.
        match_destr; unfold Equivalence.equiv in * .
        * SSCase "v0 = v"%string.
          subst.
          generalize (nrc_eval_remove_duplicate_env (h:=h) nil v d nil dunit env e3).
          simpl; trivial.
        * SSCase "v0 <> v"%string.
          generalize (nrc_eval_swap_neq (h:=h) nil); simpl; intros eqq.
          rewrite eqq; auto.
  Qed.

  Lemma nrc_eval_cons_subst {h:list (string*string)} e env v x v' :
    ~ (In v' (nrc_free_vars e)) ->
    ~ (In v' (nrc_bound_vars e)) ->
    nrc_eval h ((v',x)::env) (nrc_subst e v (NRCVar v')) = 
    nrc_eval h ((v,x)::env) e.
  Proof.
    revert env v x v'.
    induction e; simpl; unfold equiv_dec;
    trivial; intros.
    - intuition. destruct (string_eqdec v0 v); simpl; subst; intuition.
      + match_destr; intuition. simpl. dest_eqdec; intuition.
      + match_destr; subst; simpl; dest_eqdec; intuition.
    - rewrite nin_app_or in H. f_equal; intuition.
    - f_equal; intuition.
    - rewrite nin_app_or in H. rewrite IHe1 by intuition.
      case_eq (nrc_eval h ((v0, x) :: env) e1); trivial; intros d deq.
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst; simpl.
      + generalize (@nrc_eval_remove_duplicate_env h nil v0 d nil); 
        simpl; intros rr1; rewrite rr1.
        destruct (string_eqdec v0 v'); unfold Equivalence.equiv in *; subst.
        * generalize (@nrc_eval_remove_duplicate_env h nil v' d nil); 
          simpl; auto.
        * generalize (@nrc_eval_remove_free_env h ((v0,d)::nil)); 
          simpl; intros rr2; apply rr2. intuition.
          elim H3. apply remove_in_neq; auto.
      + destruct (string_eqdec v v'); unfold Equivalence.equiv in *; subst; [intuition | ].
        generalize (@nrc_eval_swap_neq h nil v d); simpl; intros rr2; 
        repeat rewrite rr2 by trivial.
        apply IHe2.
        * intros nin; intuition. elim H2; apply remove_in_neq; auto.
        * intuition.
    - rewrite nin_app_or in H. rewrite IHe1 by intuition.
      case_eq (nrc_eval h ((v0, x) :: env) e1); trivial; intros d deq.
      destruct d; trivial.
      f_equal.
      apply rmap_ext; intros.
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst; simpl.
      + generalize (@nrc_eval_remove_duplicate_env h nil v0 x0 nil); 
        simpl; intros rr1; rewrite rr1.
        destruct (string_eqdec v0 v'); unfold Equivalence.equiv in *; subst.
        * generalize (@nrc_eval_remove_duplicate_env h nil v' x0 nil); 
          simpl; auto.
        * generalize (@nrc_eval_remove_free_env h ((v0,x0)::nil)); 
          simpl; intros rr2; apply rr2. intuition.
          elim H4. apply remove_in_neq; auto.
      + destruct (string_eqdec v v'); unfold Equivalence.equiv in *; subst; [intuition | ].
        generalize (@nrc_eval_swap_neq h nil v x0); simpl; intros rr2; 
        repeat rewrite rr2 by trivial.
        apply IHe2.
        * intros nin; intuition. elim H3; apply remove_in_neq; auto.
        * intuition.
    - rewrite nin_app_or in H; destruct H as [? HH]; 
      rewrite nin_app_or in HH, H0.
      rewrite nin_app_or in H0.
      rewrite IHe1, IHe2, IHe3; intuition.
    - apply not_or in H0; destruct H0 as [neq1 neq2].
      apply not_or in neq2; destruct neq2 as [neq2 neq3].
      repeat rewrite nin_app_or in neq3.
      repeat rewrite nin_app_or in H.
      rewrite IHe1 by intuition.
      repeat rewrite <- remove_in_neq in H by congruence.
      match_destr. destruct d; trivial.
      + match_destr; unfold Equivalence.equiv in *; subst.
        * generalize (@nrc_eval_remove_duplicate_env h nil v1 d nil); simpl;
          intros re2; rewrite re2 by trivial.
          generalize (@nrc_eval_remove_free_env h ((v1,d)::nil)); 
            simpl; intros re3. rewrite re3; intuition.
        *  generalize (@nrc_eval_swap_neq h nil v d); simpl;
           intros re1; repeat rewrite re1 by trivial.
           rewrite IHe2; intuition.
      +  match_destr; unfold Equivalence.equiv in *; subst.
         * generalize (@nrc_eval_remove_duplicate_env h nil v1 d nil); simpl;
           intros re2; rewrite re2 by trivial.
           generalize (@nrc_eval_remove_free_env h ((v1,d)::nil)); 
             simpl; intros re3. rewrite re3; intuition.
         *  generalize (@nrc_eval_swap_neq h nil v0 d); simpl;
            intros re1; repeat rewrite re1 by trivial.
            rewrite IHe3; intuition.
  Qed.

  (* This relation is finer then the Proper relation already shown *)
  Lemma nrc_eval_equiv_free_in_env:
    forall n,
    forall env1 env2,
      (forall x, In x (nrc_free_vars n) -> lookup equiv_dec env1 x = lookup equiv_dec env2 x) ->
      forall h,
        nrc_eval h env1 n = nrc_eval h env2 n.
  Proof.
    intros n.
    nrc_cases (induction n) Case; intros env1 env2 Henv_eq h.
    - Case "NRCVar"%string.
      simpl.
      apply Henv_eq.
      simpl; auto.
    - Case "NRCConst"%string.
      simpl.
      reflexivity.
    - Case "NRCBinop"%string.
      simpl.
      rewrite (IHn1 env1 env2).
      rewrite (IHn2 env1 env2).
      reflexivity.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nrc_free_vars (NRCBinop b n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nrc_free_vars n2)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nrc_free_vars (NRCBinop b n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nrc_free_vars n1)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
    - Case "NRCUnop"%string.
      simpl.
      rewrite (IHn env1 env2).
      reflexivity.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nrc_free_vars (NRCUnop u n)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nrc_free_vars n)); [ | contradiction ].
        simpl in n0.
        assumption.
    - Case "NRCLet"%string.
      simpl.
      rewrite (IHn1 env1 env2).
      destruct (nrc_eval h env2 n1); try congruence.
      rewrite (IHn2 ((v, d) :: env1) ((v, d) :: env2)); try reflexivity.
      intros x.
      simpl.
      destruct (equiv_dec x v); try reflexivity.
      + intros Hx.
        destruct (in_dec equiv_dec x (nrc_free_vars (NRCLet v n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nrc_free_vars n2)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n.
        apply (not_in_remove_impl_not_in x v); assumption.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nrc_free_vars (NRCLet v n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nrc_free_vars n1)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
    - Case "NRCFor"%string.
      simpl.
      rewrite (IHn1 env1 env2).
      destruct (nrc_eval h env2 n1); try reflexivity.
      destruct d; try reflexivity.
      unfold lift.
      
      assert (rmap (fun d1 : data => nrc_eval h ((v, d1) :: env1) n2) l = rmap (fun d1 : data => nrc_eval h ((v, d1) :: env2) n2) l) as Hfun_eq; try solve [rewrite Hfun_eq; reflexivity].
      apply rmap_ext; intros d ind.
      rewrite (IHn2 ((v, d) :: env1) ((v, d) :: env2)); try reflexivity.
      intros x.
      simpl.
      destruct (equiv_dec x v); try reflexivity.
      + intros Hx.
        destruct (in_dec string_eqdec x (nrc_free_vars (NRCFor v n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nrc_free_vars n2)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n.
        apply (not_in_remove_impl_not_in x v); assumption.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nrc_free_vars (NRCFor v n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nrc_free_vars n1)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
    - Case "NRCIf"%string.
      simpl.
      unfold olift.
      rewrite (IHn1 env1 env2).
      destruct (nrc_eval h env2 n1); try reflexivity.
      destruct d; try reflexivity.
      destruct b.
      + rewrite (IHn2 env1 env2).
        reflexivity.
        * intros x Hx.
          destruct (in_dec string_eqdec x (nrc_free_vars (NRCIf n1 n2 n3)));
            [ apply Henv_eq; assumption | ].
          assert (~In x (nrc_free_vars n2)); [ | contradiction ].
          simpl in n.
          apply nin_app_or in n.
          destruct n.
          apply nin_app_or in H0.
          destruct H0; assumption.
      + rewrite (IHn3 env1 env2).
        reflexivity.
        * intros x Hx.
          destruct (in_dec string_eqdec x (nrc_free_vars (NRCIf n1 n2 n3)));
            [ apply Henv_eq; assumption | ].
          assert (~In x (nrc_free_vars n3)); [ | contradiction ].
          simpl in n.
          apply nin_app_or in n.
          destruct n.
          apply nin_app_or in H0.
          destruct H0; assumption.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nrc_free_vars (NRCIf n1 n2 n3)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nrc_free_vars n1)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
    - Case "NRCEither"%string.
      simpl.
      rewrite (IHn1 env1 env2).
      destruct (nrc_eval h env2 n1); try reflexivity.
      destruct (d); try reflexivity.
      + rewrite (IHn2 ((v, d0) :: env1) ((v, d0) :: env2)); try reflexivity.
        simpl.
        intros x.
        destruct (equiv_dec x v); try reflexivity.
        * intros Hx.
          destruct (in_dec string_eqdec x (nrc_free_vars (NRCEither n1 v n2 v0 n3)));
            [ apply Henv_eq; assumption | ].
          assert (~In x (nrc_free_vars n2)); [ | contradiction ].
          simpl in n.
          apply nin_app_or in n.
          destruct n.
          apply nin_app_or in H0.
          destruct H0.
          apply (not_in_remove_impl_not_in x v); assumption.
      + rewrite (IHn3 ((v0, d0) :: env1) ((v0, d0) :: env2)); try reflexivity.
        simpl.
        intros x.
        destruct (equiv_dec x v0); try reflexivity.
        * intros Hx.
          destruct (in_dec string_eqdec x (nrc_free_vars (NRCEither n1 v n2 v0 n3)));
            [ apply Henv_eq; assumption | ].
          assert (~In x (nrc_free_vars n3)); [ | contradiction ].
          simpl in n.
          apply nin_app_or in n.
          destruct n.
          apply nin_app_or in H0.
          destruct H0.
          apply (not_in_remove_impl_not_in x v0); assumption.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nrc_free_vars (NRCEither n1 v n2 v0 n3)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nrc_free_vars n1)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
  Qed.

  Lemma nrc_eval_equiv_env:
    forall n,
    forall env1 env2,
      (forall x, lookup equiv_dec env1 x = lookup equiv_dec env2 x) ->
      forall h,
        nrc_eval h env1 n = nrc_eval h env2 n.
  Proof.
    intros.
    apply nrc_eval_lookup_equiv_prop; trivial.
  Qed.

  Lemma nrc_no_free_vars_eval_equiv_env:
    forall n,
    forall env1 env2,
      nrc_free_vars n = nil ->
      forall h,
        nrc_eval h env1 n = nrc_eval h env2 n.
  Proof.
    intros.
    apply nrc_eval_equiv_free_in_env; intros.
    rewrite H in H0; simpl in H0.
    contradiction.
  Qed.

  Lemma nrc_eval_single_context_var_uncons h env n v d:
    lookup equiv_dec env v = Some d ->
    nrc_eval h env n = nrc_eval h ((v, d) :: env) n.
  Proof.
    intros.
    apply nrc_eval_equiv_env.
    intros x.
    case (string_eqdec x v).
    + Case "x = v"%string.
      intros Hx; rewrite Hx in *; clear Hx.
      rewrite H.
      simpl.
      match_destr.
      congruence.
    + Case "x <> v"%string.
      intros Hx.
      simpl.
      match_destr.
      congruence.
  Qed.

  Lemma nrc_eval_single_context_var h env n v d:
    (forall x, In x (nrc_free_vars n) -> x = v) ->
    lookup equiv_dec env v = Some d ->
    nrc_eval h ((v, d) :: nil) n = nrc_eval h env n.
  Proof.
    intros.
    rewrite (nrc_eval_single_context_var_uncons h env n v d); try assumption.
    clear H0.
    induction env; try reflexivity.
    destruct a.
    case (string_eqdec v0 v).
    * Case "v0 = v"%string.
      intros Hv; red in Hv; rewrite Hv in *; clear Hv.
      rewrite (nrc_eval_remove_duplicate_env nil v d nil d0 env n).
      simpl. assumption.
    * Case "v0 <> v"%string.
      intros Hv.
      rewrite (nrc_eval_remove_free_env ((v, d)::nil) v0 d0 env n); try solve [ simpl; reflexivity ].
      rewrite IHenv. reflexivity.
      specialize (H v0).
      unfold not.
      intros H'.
      assert (v0 = v); try congruence.
      apply H.
      exact H'.
  Qed.

  Lemma nrc_eval_single_context_var_cons h env n v d:
    (forall x, In x (nrc_free_vars n) -> x = v) ->
    nrc_eval h ((v, d) :: nil) n = nrc_eval h ((v,d)::env) n.
  Proof.
    intros.
    apply nrc_eval_single_context_var; try assumption.
    simpl.
    match_destr.
    congruence.
  Qed.

  Lemma nrc_eval_single_context_var_cons_keepone h env n v d v1 d1:
    (forall x, In x (nrc_free_vars n) -> x = v) ->
    nrc_eval h ((v, d) :: (v1, d1) :: nil) n = nrc_eval h ((v,d) :: (v1,d1) :: env) n.
  Proof.
    intros.
    rewrite <- (nrc_eval_single_context_var h ((v,d) :: (v1,d1) :: nil) n v d); try assumption.
    - rewrite <- (nrc_eval_single_context_var h ((v,d) :: (v1,d1) :: env) n v d); try assumption; trivial.
      simpl; match_destr; congruence.
    - simpl; match_destr; congruence.
  Qed.

  Lemma nrc_eval_single_context_var_two_cons h env n v1 d1 v2 d2 :
    (forall x, In x (nrc_free_vars n) -> x = v1 \/ x = v2) ->
    nrc_eval h ((v1,d1) :: (v2,d2) :: nil) n = nrc_eval h ((v1,d1) :: (v2,d2) :: env) n.
  Proof.
    intros.
    induction env; try reflexivity.
    destruct a.
    case (string_eqdec v1 v); intros.
    red in e; rewrite e in *; clear e.
    rewrite nrc_eval_remove_duplicate_env_weak; assumption.
    case (string_eqdec v2 v); intros.
    red in e; rewrite e in *; clear e.
    rewrite nrc_eval_remove_duplicate_env_weak_cons; assumption.
    rewrite (nrc_eval_remove_free_env ((v1,d1)::(v2,d2)::nil) v d env n).
    assumption.
    specialize (H v).
    unfold not; intros.
    specialize (H H0).
    elim H; intros; congruence.
  Qed.

  Lemma nrc_eval_single_context_var_cons_rmap h env n v l:
    (forall x, In x (nrc_free_vars n) -> x = v) ->
    rmap (fun d => nrc_eval h ((v, d) :: nil) n) l =
    rmap (fun d => nrc_eval h ((v,d)::env) n) l.
  Proof.
    intros.
    induction l; simpl; try reflexivity.
    rewrite (nrc_eval_single_context_var_cons h env n v a); try assumption.
    destruct (nrc_eval h ((v, a) :: env) n); try reflexivity.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma nrc_eval_single_context_var_cons_keepone_rmap h env n v v1 d1 l:
    (forall x, In x (nrc_free_vars n) -> x = v) ->
    rmap (fun d => nrc_eval h ((v, d) :: (v1,d1) :: nil) n) l =
    rmap (fun d => nrc_eval h ((v,d) :: (v1,d1) :: env) n) l.
  Proof.
    intros.
    induction l; simpl; try reflexivity.
    rewrite (nrc_eval_single_context_var_cons_keepone h env n v a v1 d1); try assumption.
    destruct (nrc_eval h ((v, a) :: (v1,d1) :: env) n); try reflexivity.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma rmap_skip_free_var h v1 v2 d2 n l:
    ~ In v2 (nrc_free_vars n) ->
    (rmap (fun d : data => nrc_eval h ((v1, d) :: (v2, d2) :: nil) n) l) =
    (rmap (fun d : data => nrc_eval h ((v1, d) :: nil) n) l).
  Proof.
    intros; induction l; try reflexivity; simpl.
    rewrite nrc_eval_remove_free_env_weak.
    destruct (nrc_eval h ((v1, a) :: nil) n); try reflexivity; rewrite IHl; reflexivity.
    auto.
  Qed.

  Lemma nrc_eval_cons_subst_disjoint {h: list (string*string)} e e' env v d :
    disjoint (nrc_bound_vars e) (nrc_free_vars e') ->
         nrc_eval h env e' = Some d ->
         nrc_eval h ((v,d)::env) e = nrc_eval h env (nrc_subst e v e').
  Proof.
    intros disj eval1.
    revert env e' v d disj eval1.
    nrc_cases (induction e) Case; simpl in *;
      trivial; intros env e' v' d disj; simpl; intros eval1;
        unfold equiv_dec, olift2, olift in * .
    - Case "NRCVar"%string.
      match_destr.
      congruence.
    - Case "NRCBinop"%string.
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      erewrite IHe1 by eauto.
      erewrite IHe2 by eauto.
      trivial.
    - Case "NRCUnop"%string.
      erewrite IHe by eauto.
      trivial.
    - Case "NRCLet"%string.
      apply disjoint_cons_inv1 in disj.
      destruct disj as [disj nin].
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      erewrite IHe1 by eauto.
      match_destr.
      match_destr.
      + red in e; subst.
        unfold var in *.
        generalize (nrc_eval_remove_duplicate_env (h:=h) nil v' d0 nil d env e2); simpl; intros re1; rewrite re1; trivial.
      + erewrite <- IHe2; try reflexivity; eauto 2.
        * generalize (nrc_eval_swap_neq (h:=h) nil v d0 v' d); simpl;
          intros re1; rewrite re1; eauto.
        * generalize (nrc_eval_remove_free_env (h:=h) nil v d0 env);
            simpl; intros re1; rewrite re1; eauto.
    - Case "NRCFor"%string.
      apply disjoint_cons_inv1 in disj.
      destruct disj as [disj nin].
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      erewrite IHe1; eauto 2.
      match_destr.
      match_destr.
      match_destr.
      + red in e; subst.
        unfold var in *.
        f_equal.
        apply rmap_ext; intros.
        generalize (nrc_eval_remove_duplicate_env (h:=h) nil v' x nil d env e2); simpl; congruence.
      + f_equal.
        apply rmap_ext; intros.
        generalize (nrc_eval_swap_neq (h:=h) nil v x v' d); simpl;
          intros re1; rewrite re1; eauto 2.
        erewrite IHe2; try reflexivity; eauto 2.
        generalize (nrc_eval_remove_free_env (h:=h) nil v x env);
            simpl; intros re2; rewrite re2; eauto.
    - Case "NRCIf"%string.
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      apply disjoint_app_l in disj2.
      destruct disj2 as [disj2 disj3].
      erewrite IHe1; eauto 2.
      match_destr.
      match_destr.
      match_destr.
      + erewrite IHe2; eauto 2.
      + erewrite IHe3; eauto 2.
    - Case "NRCEither"%string.
      apply disjoint_cons_inv1 in disj.
      destruct disj as [disj nin].
      apply disjoint_cons_inv1 in disj.
      destruct disj as [disj nin2].
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      apply disjoint_app_l in disj2.
      destruct disj2 as [disj2 disj3].
      erewrite IHe1; eauto 2.
      match_destr.
      match_destr.
      + {
          match_destr.
          + red in e; subst.
            unfold var in *.
            generalize (nrc_eval_remove_duplicate_env (h:=h) nil v' d0 nil d env e2); simpl; intros re1; rewrite re1; trivial.
          + generalize (nrc_eval_swap_neq (h:=h) nil v d0 v' d); simpl;
                intros re1; rewrite re1; eauto 2.
            erewrite IHe2; try reflexivity; eauto 2.
            generalize (nrc_eval_remove_free_env (h:=h) nil v d0 env);
                simpl; intros re2; rewrite re2; trivial.
        } 
      + {
          match_destr.
          + red in e; subst.
            unfold var in *.
            generalize (nrc_eval_remove_duplicate_env (h:=h) nil v' d0 nil d env e3); simpl; intros re1; rewrite re1; trivial.
          + generalize (nrc_eval_swap_neq (h:=h) nil v0 d0 v' d); simpl;
                intros re1; rewrite re1; eauto 2.
            erewrite IHe3; try reflexivity; eauto 2.
            generalize (nrc_eval_remove_free_env (h:=h) nil v0 d0 env);
                simpl; intros re2; rewrite re2; trivial.
        }
  Qed.

  Lemma nrc_pick_name_neq_nfree sep renamer avoid v e :
    v =/= nrc_pick_name sep renamer avoid v e ->
    ~ In (nrc_pick_name sep renamer avoid v e) (nrc_free_vars e).
  Proof.
    unfold nrc_pick_name, pick_same_really_fresh_in, pick_new_really_fresh_in.
    intros eqq.
    match_destr.
    - match_destr.
      + apply really_fresh_from_free.
      + congruence.
    - match_destr.
      + apply really_fresh_from_free.
      + repeat rewrite in_app_iff in n; intuition.
  Qed.

  Lemma nrc_eval_cons_rename_pick h sep renamer avoid v e d env:
    nrc_eval h ((nrc_pick_name sep renamer avoid v e, d) :: env)
             (nrc_rename_lazy e v (nrc_pick_name sep renamer avoid v e)) = 
    nrc_eval h ((v, d) :: env) e.
  Proof.
    unfold nrc_rename_lazy.
    match_destr.
    - rewrite <- e0.
      trivial.
    - rewrite nrc_eval_cons_subst; trivial.
      + apply nrc_pick_name_neq_nfree; trivial.
      + apply nrc_pick_name_bound.
  Qed.

  Theorem unshadow_eval {h:list (string*string)} sep renamer avoid e env :
    nrc_eval h env (unshadow sep renamer avoid e) = nrc_eval h env e.
  Proof.
    revert env.
    induction e; simpl; trivial; intros; try congruence.
    - rewrite IHe1.
      match_destr.
      rewrite nrc_eval_cons_rename_pick.
      trivial.
    - rewrite IHe1.
      match_destr.
      match_destr.
      f_equal.
      apply rmap_ext; intros.
      rewrite <- IHe2.
      apply nrc_eval_cons_rename_pick.
    - rewrite IHe1, IHe2, IHe3; trivial.
    - rewrite IHe1.
      match_destr.
      match_destr.
      + rewrite nrc_eval_cons_rename_pick.
        rewrite IHe2.
        trivial.
      + rewrite nrc_eval_cons_rename_pick.
        rewrite IHe3.
        trivial.
  Qed.

  Lemma nrc_pick_name_id_nin_eq sep avoid v e :
    ~ In v (nrc_bound_vars e) ->
    ~ In v avoid ->
    (nrc_pick_name sep id avoid v e) = v.
  Proof.
    unfold nrc_pick_name, id.
    intros.
    match_destr; [|congruence].
    unfold pick_same_really_fresh_in.
    match_destr.
    repeat rewrite in_app_iff in i; intuition.
  Qed.

  Lemma nrc_rename_lazy_eq e v :
    nrc_rename_lazy e v v = e.
  Proof.
    unfold nrc_rename_lazy.
    match_destr.
    congruence.
  Qed.

  Lemma shadow_free_unshadow_id sep avoid (e:nrc) : 
    shadow_free e = true ->
    (forall x, In x avoid -> ~In x (nrc_bound_vars e)) ->
    unshadow sep id avoid e = e.
  Proof.
    induction e; simpl; trivial; repeat rewrite andb_true_iff;
    intuition;
     try apply in_in_app_false in H0;
     intuition; try congruence.
    - rewrite H1, H4 by (intros ? av; generalize (H0 _ av); intuition).
      match_destr_in H.
      rewrite nrc_pick_name_id_nin_eq.
      + rewrite nrc_rename_lazy_eq; trivial.
      + trivial.
      + intros inn; apply (H0 _ inn); intuition.
    - rewrite H1, H4 by (intros ? av; generalize (H0 _ av); intuition).
      match_destr_in H.
      rewrite nrc_pick_name_id_nin_eq.
      + rewrite nrc_rename_lazy_eq; trivial.
      + trivial.
      + intros inn; apply (H0 _ inn); intuition.
    - rewrite H0, H1, H5 by (intros ? av; generalize (H7 _ av); intuition).
      trivial.
    - match_destr_in H. match_destr_in H5.
      assert (H0':forall x : var,
       In x avoid ->
       (v = x \/
       v0 = x \/
       In x (nrc_bound_vars e1) \/
       In x (nrc_bound_vars e2) \/
       In x (nrc_bound_vars e3)) -> False)
        by (intros ? av; specialize (H0 _ av);
      intuition; try solve[apply nin_app_or in H11; intuition]).
      rewrite H1, H6, H7; try solve [intros ? av; specialize (H0' _ av); intuition].
      rewrite nrc_pick_name_id_nin_eq.
      + rewrite nrc_rename_lazy_eq; trivial.
        rewrite nrc_pick_name_id_nin_eq.
        * rewrite nrc_rename_lazy_eq; trivial.
        * trivial.
        * intros inn; apply (H0 _ inn); intuition.
      + trivial.
      + intros inn; apply (H0 _ inn); intuition.
  Qed.

  Lemma unshadow_id_idempotent sep renamer1 avoid (e:nrc) 
    : unshadow sep id avoid (unshadow sep renamer1 avoid e) = unshadow sep renamer1 avoid e.
  Proof.
    apply shadow_free_unshadow_id.
    - apply unshadow_shadow_free.
    - apply unshadow_avoid.
  Qed.

  (* Java equivalent: inlined in several places *)  
  Definition nrc_unshadow_sep := "$"%string.
  (* Java equivalent: inlined in several places *)  
  Definition unshadow_simpl := unshadow nrc_unshadow_sep id.

  (* Java equivalent: MROptimizer.nrc_subslist_subst *)
  Definition nrc_substlist_subst (substlist:list (var*var)) (e:nrc) :=
    List.fold_left
      (fun e (subst: var * var) =>
         let (x, x') := subst in
         nrc_subst e x (NRCVar x'))
      substlist e.

End NNRCShadow.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
