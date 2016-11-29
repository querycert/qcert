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
  Require Import NNRCSize.

  Close Scope nnrc_scope.
  
  (* Since we are translating from a language with scoped variables
     (For) to a language without scoping, we need to alpha convert the input
     to ensure that there are no shadowed variable names.
   *)

  Context {fruntime:foreign_runtime}.

  (* Java equivalent: NnrcOptimizer.nrc_bound_vars *)
  Fixpoint nnrc_bound_vars (e:nnrc) : list var :=
    match e with
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

  Require Import Arith Max.

  (* capture avoiding substitution *)
  (* Java equivalent: NnnrcOptimizer.nnrc_subst *)
  Fixpoint nnrc_subst (e:nnrc) (x:var) (e':nnrc) : nnrc 
    := match e with
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

  Require Import Bool.

  Fixpoint shadow_free (e:nnrc) : bool :=
    match e with
    | NNRCVar x => true
    | NNRCConst d => true
    | NNRCBinop bop e1 e2 => shadow_free e1 && shadow_free e2
    | NNRCUnop uop e1 => shadow_free e1
    | NNRCLet x e1 e2 => 
      (if in_dec string_eqdec x (nnrc_bound_vars e2) then false else true) 
        && shadow_free e1 && shadow_free e2
    | NNRCFor x e1 e2 => 
      (if in_dec string_eqdec x (nnrc_bound_vars e2) then false else true) 
        && shadow_free e1 && shadow_free e2
    | NNRCIf e1 e2 e3 =>  shadow_free e1 && shadow_free e2 && shadow_free e3
    | NNRCEither ed xl el xr er =>
      (if in_dec string_eqdec xl (nnrc_bound_vars el) then false else true)
        && (if in_dec string_eqdec xr (nnrc_bound_vars er) then false else true) 
        && shadow_free ed && shadow_free el && shadow_free er
    | NNRCGroupBy g sl e1 => shadow_free e1
    end.

  Definition pick_new_really_fresh_in (sep:string) (name:var) (avoid:list var) (e:nnrc)
    := if in_dec string_eqdec name (avoid ++ (nnrc_free_vars e) ++ (nnrc_bound_vars e))
       then really_fresh_in sep name avoid e
       else name.

  (* Java equivalent: NnnrcOptimizer.pick_same_really_fresh_in *)
  Definition pick_same_really_fresh_in (sep:string) (name:var) (avoid:list var) (e:nnrc)
    := if in_dec string_eqdec name (avoid ++ (nnrc_bound_vars e))
       then really_fresh_in sep name avoid e
       else name.

  (* unshadow preserves semantics and ensures that there is no shadowing *)
  Section unsh.
   (* Java equivalent: NnnrcOptimizer.nnrc_rename_lazy *)
    Definition nnrc_rename_lazy (e:nnrc) (oldvar newvar:var)
      := if oldvar == newvar
         then e
         else (nnrc_subst e oldvar (NNRCVar newvar)).

    Lemma nnrc_rename_lazy_size n x1 x2:
      nnrc_size (nnrc_rename_lazy n x1 x2) = nnrc_size n.
    Proof.
      nnrc_cases (induction n) Case;
        unfold nnrc_rename_lazy in *;
        simpl;
        destruct (equiv_dec x1 x2);
        simpl;
        try reflexivity;
        try solve [ rewrite IHn1;
                    rewrite IHn2;
                    rewrite IHn3;
                    reflexivity ];
        try solve [ rewrite IHn1;
                    rewrite IHn2;
                    reflexivity ];
        try solve [ rewrite IHn;
                    reflexivity ];
        try solve [ rewrite IHn1;
                    destruct (equiv_dec v x1);
                      simpl; try reflexivity;
                    rewrite IHn2;
                    reflexivity ].
      - Case "NNRCVar"%string.
        destruct (equiv_dec v x1);
            simpl; reflexivity.
      - Case "NNRCEither"%string.
        rewrite IHn1.
        destruct (equiv_dec v x1);
          destruct (equiv_dec v0 x1);
          simpl; try reflexivity.
        + rewrite IHn3.
          reflexivity.
        + rewrite IHn2.
          reflexivity.
        + rewrite IHn2.
          rewrite IHn3.
          reflexivity.
    Qed.

    Context (sep:string).
    (* as part of unshadowing, we also support a user defined renaming function *)
    Context (renamer:string->string).
    Context (avoid:list var).

   (* Java equivalent: NnnrcOptimizer.nnrc_pick_name *)
    Definition nnrc_pick_name (oldvar:var) (e:nnrc) 
      := let name := renamer oldvar in
         if name == oldvar
         then pick_same_really_fresh_in sep name avoid e
         else pick_new_really_fresh_in sep name avoid e.
    
  (* Java equivalent: NnnrcOptimizer.unshadow *)
  Fixpoint unshadow (e:nnrc) : nnrc
    :=   
      match e with
      | NNRCVar x => NNRCVar x
      | NNRCConst d => NNRCConst d
      | NNRCBinop bop e1 e2 => NNRCBinop bop (unshadow e1) (unshadow e2)
      | NNRCUnop uop e1 => NNRCUnop uop (unshadow e1)
      | NNRCLet x e1 e2 => 
        let e1' := unshadow e1 in
        let e2' := unshadow e2 in
        let x' := nnrc_pick_name x e2' in
        NNRCLet x' e1' (nnrc_rename_lazy e2' x x')
      | NNRCFor x e1 e2 => 
        let e1' := unshadow e1 in
        let e2' := unshadow e2 in
        let x' := nnrc_pick_name x e2' in
        NNRCFor x' e1' (nnrc_rename_lazy e2' x x')
      | NNRCIf e1 e2 e3 =>  NNRCIf (unshadow e1) (unshadow e2) (unshadow e3)
      | NNRCEither ed xl el xr er =>
        let ed' := unshadow ed in
        let el' := unshadow el in
        let er' := unshadow er in
        let xl' := nnrc_pick_name xl el' in
        let xr' := nnrc_pick_name xr er' in
        NNRCEither ed' xl' (nnrc_rename_lazy el' xl xl') xr' (nnrc_rename_lazy er' xr xr')
      | NNRCGroupBy g sl e1 => NNRCGroupBy g sl (unshadow e1)
      end.
  
  Lemma nnrc_bound_vars_subst_preserved e x e' :
    nnrc_bound_vars e' = nil -> 
    nnrc_bound_vars (nnrc_subst e x e') = nnrc_bound_vars e.
  Proof.
    induction e; simpl; intuition; repeat dest_eqdec; simpl; try congruence.
  Qed.

  Lemma no_bound_shadow_free e :
    nnrc_bound_vars e = nil -> shadow_free e = true.
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

  Lemma nnrc_shadow_free_subst_preserved e x e' :
    nnrc_bound_vars e' = nil -> 
    shadow_free (nnrc_subst e x e') = shadow_free e.
  Proof.
    induction e; simpl; try dest_eqdec; try solve[intuition; simpl; try congruence]; intros.
    - apply no_bound_shadow_free; auto.
    - rewrite nnrc_bound_vars_subst_preserved; auto.
      destruct (in_dec string_eqdec v (nnrc_bound_vars e2)); simpl; trivial.
      intuition congruence.
    - rewrite nnrc_bound_vars_subst_preserved; auto.
      destruct (in_dec string_eqdec v (nnrc_bound_vars e2)); simpl; trivial.
      intuition congruence.
    - rewrite IHe1 by trivial. dest_eqdec; trivial.
      match_destr.
      rewrite nnrc_bound_vars_subst_preserved; trivial.
      simpl.
      match_destr; simpl.
      rewrite IHe3; trivial.
    - rewrite IHe1, IHe2 by trivial.
      match_destr; simpl.
      + rewrite nnrc_bound_vars_subst_preserved in i; trivial.
         match_destr; simpl; congruence.
      + rewrite nnrc_bound_vars_subst_preserved in n; trivial.
        dest_eqdec; try rewrite H3; trivial.
        * match_destr; simpl; match_destr; simpl.
           congruence.
        * { match_destr.
            - rewrite nnrc_bound_vars_subst_preserved in i; trivial;
                match_destr; match_destr; try congruence.
            - rewrite nnrc_bound_vars_subst_preserved in n0; trivial.
              rewrite IHe3 by trivial.
              repeat match_destr; try congruence.
          }
  Qed.

  Lemma nnrc_shadow_free_rename_nnrc_pick_name_preserved e v :
    shadow_free (nnrc_rename_lazy e v (nnrc_pick_name v e)) = shadow_free e.
  Proof.
    unfold nnrc_rename_lazy.
    match_destr.
    rewrite nnrc_shadow_free_subst_preserved; trivial.
  Qed.

  Lemma nnrc_bound_vars_rename_lazy_preserved e oldvar newvar :
    nnrc_bound_vars (nnrc_rename_lazy e oldvar newvar) = nnrc_bound_vars e.
  Proof.
    unfold nnrc_rename_lazy.
    match_destr.
    apply nnrc_bound_vars_subst_preserved; simpl.
    trivial.
  Qed.

  Lemma nnrc_pick_name_avoid old (e:nnrc) :
    ~ In (nnrc_pick_name old e) avoid.
  Proof.
    unfold nnrc_pick_name, pick_new_really_fresh_in, pick_same_really_fresh_in.
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


  Lemma nnrc_pick_name_bound old (e:nnrc) :
    ~ In (nnrc_pick_name old e) (nnrc_bound_vars e).
  Proof.
    unfold nnrc_pick_name, pick_new_really_fresh_in, pick_same_really_fresh_in.
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
  
  Lemma unshadow_shadow_free (e:nnrc) : 
    shadow_free (unshadow e) = true.
  Proof.
    induction e; simpl; intuition.
    - rewrite nnrc_shadow_free_rename_nnrc_pick_name_preserved.
      rewrite nnrc_bound_vars_rename_lazy_preserved.
      rewrite IHe1, IHe2.
      match_destr.
      eelim nnrc_pick_name_bound; eauto.
    - rewrite nnrc_shadow_free_rename_nnrc_pick_name_preserved.
      rewrite nnrc_bound_vars_rename_lazy_preserved.
      rewrite IHe1, IHe2.
      match_destr.
      eelim nnrc_pick_name_bound; eauto.
    - repeat rewrite nnrc_shadow_free_rename_nnrc_pick_name_preserved.
      repeat rewrite nnrc_bound_vars_rename_lazy_preserved.
      rewrite IHe1, IHe2, IHe3.
      match_destr.
      + eelim nnrc_pick_name_bound; eauto.
      + match_destr.
        eelim nnrc_pick_name_bound; eauto.
  Qed.

  Lemma unshadow_avoid (e:nnrc) x : 
    In x avoid -> ~ In x (nnrc_bound_vars (unshadow e)).
  Proof.
    induction e; simpl; auto; intros
    ; repeat rewrite nnrc_bound_vars_rename_lazy_preserved
    ; repeat rewrite in_app_iff; intuition
    ; subst; eelim nnrc_pick_name_avoid; eauto.
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
      + rewrite (replace_all_remove_eq (nnrc_free_vars e2) v n); trivial.
      + rewrite H3. apply replace_all_remove_neq; auto.
    - intuition. f_equal; auto.
      destruct (string_eqdec v0 v); unfold equiv in *; subst.
      + rewrite (replace_all_remove_eq (nnrc_free_vars e2) v n); trivial.
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
      try rewrite (replace_all_remove_eq (nnrc_free_vars e2) v n);
        try rewrite (replace_all_remove_eq (nnrc_free_vars e3) v n);
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
  
  Lemma nnrc_pick_name_remove_free v e :
  remove string_eqdec (nnrc_pick_name v e) 
     (nnrc_free_vars (nnrc_rename_lazy e v (nnrc_pick_name v e))) =
   remove string_eqdec v (nnrc_free_vars e).
  Proof.
    unfold nnrc_pick_name.
    match_destr.
    - unfold pick_new_really_fresh_in.
      unfold nnrc_rename_lazy.
      match_destr.
      + congruence.
      + unfold pick_same_really_fresh_in.
        match_destr.
        * rewrite nnrc_free_vars_subst; [|apply really_fresh_from_bound].
          rewrite remove_replace_all_nin; [|apply really_fresh_from_free].
          trivial.
        * rewrite e0.
          rewrite nnrc_subst_eq.
          trivial.
    - unfold pick_new_really_fresh_in.
      unfold nnrc_rename_lazy.
      match_destr.
      + match_destr.
        * congruence.
        * rewrite nnrc_free_vars_subst; [|apply really_fresh_from_bound].
          rewrite remove_replace_all_nin; [|apply really_fresh_from_free].
          trivial.
      + match_destr.
        * congruence.
        * repeat rewrite in_app_iff in n.
          rewrite nnrc_free_vars_subst; [|intuition].
          rewrite remove_replace_all_nin; [|intuition].
          trivial.
  Qed.
          
  Lemma unshadow_nnrc_free_vars (e:nnrc) :
    nnrc_free_vars (unshadow e) = nnrc_free_vars e.
  Proof.
    induction e; simpl
    ; repeat rewrite nnrc_pick_name_remove_free
    ; congruence.
  Qed.

  End unsh.


  Lemma nnrc_core_eval_remove_duplicate_env {h:brand_relation_t} l v x l' x' l'' e :
    nnrc_core_eval h (l ++ (v,x)::l' ++ (v,x')::l'') e =
    nnrc_core_eval h (l ++ (v,x)::l' ++ l'') e.
  Proof.
    rewrite lookup_remove_duplicate; trivial.
  Qed.

  Lemma nnrc_core_eval_remove_duplicate_env_weak {h:list (string*string)} v1 v2 x x' x'' l e :
    nnrc_core_eval h ((v1,x)::(v2,x')::(v1,x'')::l) e =
    nnrc_core_eval h ((v1,x)::(v2,x')::l) e.
  Proof.
    apply nnrc_core_eval_lookup_equiv_prop; trivial.
    red; intros; simpl.
    match_destr.
  Qed.

  Lemma nnrc_core_eval_remove_duplicate_env_weak_cons {h:list (string*string)} v1 v2 x x' x'' l e :
    nnrc_core_eval h ((v1,x)::(v2,x')::(v2,x'')::l) e =
    nnrc_core_eval h ((v1,x)::(v2,x')::l) e.
  Proof.
    apply nnrc_core_eval_lookup_equiv_prop; trivial.
    red; intros; simpl.
    match_destr.
    match_destr.
  Qed.

  Lemma nnrc_core_eval_remove_free_env {h:list (string*string)} l v x l' e :
          ~ In v (nnrc_free_vars e) ->
          nnrc_core_eval h (l ++ (v,x)::l') e = nnrc_core_eval h (l ++ l') e.
  Proof.
    revert l v x l'.
    induction e; simpl; intros; trivial.
    - intuition. apply lookup_remove_nin; auto.
    - apply nin_app_or in H. rewrite IHe1, IHe2; intuition.
    - rewrite IHe; intuition.
    - apply nin_app_or in H. rewrite IHe1 by intuition.
      destruct (nnrc_core_eval h (l ++ l') e1); trivial. 
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst.
      + generalize (@nnrc_core_eval_remove_duplicate_env h nil v0 d l); simpl; auto.
      + generalize (IHe2 ((v,d)::l)); simpl; intros rr; rewrite rr; intuition.
         elim H2. apply remove_in_neq; auto.
    - apply nin_app_or in H. rewrite IHe1 by intuition.
      destruct (nnrc_core_eval h (l ++ l') e1); trivial. destruct d; trivial.
      f_equal. apply rmap_ext; intros.
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst.
      + generalize (@nnrc_core_eval_remove_duplicate_env h nil v0 x0 l); simpl; auto.
      + generalize (IHe2 ((v,x0)::l)); simpl; intros rr; rewrite rr; intuition.
         elim H3. apply remove_in_neq; auto.
    - apply nin_app_or in H; destruct H as [? HH]; apply nin_app_or in HH.
      rewrite IHe1, IHe2, IHe3; intuition.
    - repeat rewrite nin_app_or in H.
      rewrite IHe1 by intuition.
      match_destr. destruct d; trivial.
      + destruct (string_eqdec v v1); unfold Equivalence.equiv in * .
        * subst. generalize (@nnrc_core_eval_remove_duplicate_env h nil v1 d l).
          simpl; trivial.
        * generalize (IHe2 ((v,d)::l)); simpl; intros r.
          apply r.
          rewrite <- (remove_in_neq _ v1 v) in H by intuition.
          intuition.
      + destruct (string_eqdec v0 v1); unfold Equivalence.equiv in * .
        * subst. generalize (@nnrc_core_eval_remove_duplicate_env h nil v1 d l).
          simpl; trivial.
        * generalize (IHe3 ((v0,d)::l)); simpl; intros r.
          apply r.
          rewrite <- (remove_in_neq _ v1 v0) in H by intuition.
          intuition.
  Qed.

  Lemma nnrc_core_eval_remove_free_env_weak {h:list (string*string)} v1 x1 v x e :
    ~ In v (nnrc_free_vars e) ->
    nnrc_core_eval h ((v1,x1)::(v,x)::nil) e = nnrc_core_eval h ((v1,x1)::nil) e.
  Proof.
    assert ((v1,x1)::(v,x)::nil =
            ((v1,x1)::nil) ++ (v,x)::nil).
    reflexivity.
    assert (((v1,x1)::nil) = ((v1,x1)::nil ++ nil)).
    reflexivity.
    rewrite H; rewrite H0.
    apply nnrc_core_eval_remove_free_env.
  Qed.

  Lemma nnrc_core_eval_swap_neq {h:list (string*string)} l1 v1 x1 v2 x2 l2 e : v1 <> v2 ->
           nnrc_core_eval h (l1++(v1,x1)::(v2,x2)::l2) e = 
           nnrc_core_eval h (l1++(v2,x2)::(v1,x1)::l2) e.
  Proof.
    intros.
    rewrite lookup_swap_neq; trivial.
  Qed.

  Lemma nnrc_core_eval_subst_dunit {h:list (string*string)} env e v :
    nnrc_core_eval h ((v,dunit)::env) e = nnrc_core_eval h env (nnrc_subst e v (NNRCConst dunit)).
  Proof.
    generalize env; clear env.
    nnrc_cases (induction e) Case.
    - Case "NNRCVar"%string.
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
    - Case "NNRCConst"%string.
      reflexivity.
    - Case "NNRCBinop"%string.
      intros env.
      simpl.
      rewrite IHe1.
      rewrite IHe2.
      reflexivity.
    - Case "NNRCUnop"%string.
      intros env.
      simpl.
      rewrite IHe.
      reflexivity.
    - Case "NNRCLet"%string.
      intros env.
      simpl.
      rewrite IHe1.
      destruct (nnrc_core_eval h env (nnrc_subst e1 v (NNRCConst dunit))); try reflexivity.
      case (equiv_dec v0 v); unfold Equivalence.equiv in *.
      + SCase "v0 = v"%string.
        intros Hv; rewrite Hv in *; clear Hv.
        generalize (nnrc_core_eval_remove_duplicate_env (h:=h) nil v d nil dunit env e2).
        simpl.
        trivial.
      + SCase "v0 <> v"%string.
        intros Hv.
        generalize (nnrc_core_eval_swap_neq (h:=h) nil); simpl; intros eqq.
        rewrite eqq; auto.
    - Case "NNRCFor"%string.
      intros env.
      simpl.
      rewrite IHe1.
      destruct (nnrc_core_eval h env (nnrc_subst e1 v (NNRCConst dunit))); try reflexivity.
      destruct d; try reflexivity.
      apply lift_dcoll_inversion.
      apply rmap_ext.
      intros d Hd.
      match_destr; unfold Equivalence.equiv in * .
      + SCase "v0 = v"%string.
        subst.
        generalize (nnrc_core_eval_remove_duplicate_env (h:=h) nil v d nil dunit env e2); simpl; trivial.
      + SCase "v0 <> v"%string.
        generalize (nnrc_core_eval_swap_neq (h:=h) nil); simpl; intros eqq.
        rewrite eqq; auto.
    - Case "NNRCIf"%string.
      intros env.
      simpl.
      unfold olift.
      rewrite IHe1.
      destruct (nnrc_core_eval h env (nnrc_subst e1 v (NNRCConst dunit))); try reflexivity.
      destruct d; try reflexivity.
      destruct b.
      + SCase "b = true"%string.
        rewrite IHe2.
        reflexivity.
      + SCase "b = false"%string.
        rewrite IHe3.
        reflexivity.
    - Case "NNRCEither"%string.
      intros env.
      simpl.
      rewrite IHe1.
      destruct (nnrc_core_eval h env (nnrc_subst e1 v (NNRCConst dunit))); try reflexivity.
      destruct d; try reflexivity.
      + SCase "left"%string.
        match_destr; unfold Equivalence.equiv in * .
        * SSCase "v0 = v"%string.
          subst.
          generalize (nnrc_core_eval_remove_duplicate_env (h:=h) nil v d nil dunit env e2).
          simpl; trivial.
        * SSCase "v0 <> v"%string.
          generalize (nnrc_core_eval_swap_neq (h:=h) nil); simpl; intros eqq.
          rewrite eqq; auto.
      + SCase "right"%string.
        match_destr; unfold Equivalence.equiv in * .
        * SSCase "v0 = v"%string.
          subst.
          generalize (nnrc_core_eval_remove_duplicate_env (h:=h) nil v d nil dunit env e3).
          simpl; trivial.
        * SSCase "v0 <> v"%string.
          generalize (nnrc_core_eval_swap_neq (h:=h) nil); simpl; intros eqq.
          rewrite eqq; auto.
    - Case "NNRCGroupBy"%string. (* Fail case for core *)
      intros; reflexivity.
  Qed.

  Lemma nnrc_core_eval_cons_subst {h:list (string*string)} e env v x v' :
    ~ (In v' (nnrc_free_vars e)) ->
    ~ (In v' (nnrc_bound_vars e)) ->
    nnrc_core_eval h ((v',x)::env) (nnrc_subst e v (NNRCVar v')) = 
    nnrc_core_eval h ((v,x)::env) e.
  Proof.
    revert env v x v'.
    nnrc_cases (induction e) Case; simpl; unfold equiv_dec;
    trivial; intros.
    - Case "NNRCVar"%string.
      intuition. destruct (string_eqdec v0 v); simpl; subst; intuition.
      + match_destr; intuition. simpl. dest_eqdec; intuition.
      + match_destr; subst; simpl; dest_eqdec; intuition.
    - Case "NNRCBinop"%string.
      rewrite nin_app_or in H. f_equal; intuition.
    - Case "NNRCUnop"%string.
      f_equal; intuition.
    - Case "NNRCLet"%string.
      rewrite nin_app_or in H. rewrite IHe1 by intuition.
      case_eq (nnrc_core_eval h ((v0, x) :: env) e1); trivial; intros d deq.
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst; simpl.
      + generalize (@nnrc_core_eval_remove_duplicate_env h nil v0 d nil); 
        simpl; intros rr1; rewrite rr1.
        destruct (string_eqdec v0 v'); unfold Equivalence.equiv in *; subst.
        * generalize (@nnrc_core_eval_remove_duplicate_env h nil v' d nil); 
          simpl; auto.
        * generalize (@nnrc_core_eval_remove_free_env h ((v0,d)::nil)); 
          simpl; intros rr2; apply rr2. intuition.
          elim H3. apply remove_in_neq; auto.
      + destruct (string_eqdec v v'); unfold Equivalence.equiv in *; subst; [intuition | ].
        generalize (@nnrc_core_eval_swap_neq h nil v d); simpl; intros rr2; 
        repeat rewrite rr2 by trivial.
        apply IHe2.
        * intros nin; intuition. elim H2; apply remove_in_neq; auto.
        * intuition.
    - rewrite nin_app_or in H. rewrite IHe1 by intuition.
      case_eq (nnrc_core_eval h ((v0, x) :: env) e1); trivial; intros d deq.
      destruct d; trivial.
      f_equal.
      apply rmap_ext; intros.
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst; simpl.
      + generalize (@nnrc_core_eval_remove_duplicate_env h nil v0 x0 nil); 
        simpl; intros rr1; rewrite rr1.
        destruct (string_eqdec v0 v'); unfold Equivalence.equiv in *; subst.
        * generalize (@nnrc_core_eval_remove_duplicate_env h nil v' x0 nil); 
          simpl; auto.
        * generalize (@nnrc_core_eval_remove_free_env h ((v0,x0)::nil)); 
          simpl; intros rr2; apply rr2. intuition.
          elim H4. apply remove_in_neq; auto.
      + destruct (string_eqdec v v'); unfold Equivalence.equiv in *; subst; [intuition | ].
        generalize (@nnrc_core_eval_swap_neq h nil v x0); simpl; intros rr2; 
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
        * generalize (@nnrc_core_eval_remove_duplicate_env h nil v1 d nil); simpl;
          intros re2; rewrite re2 by trivial.
          generalize (@nnrc_core_eval_remove_free_env h ((v1,d)::nil)); 
            simpl; intros re3. rewrite re3; intuition.
        *  generalize (@nnrc_core_eval_swap_neq h nil v d); simpl;
           intros re1; repeat rewrite re1 by trivial.
           rewrite IHe2; intuition.
      +  match_destr; unfold Equivalence.equiv in *; subst.
         * generalize (@nnrc_core_eval_remove_duplicate_env h nil v1 d nil); simpl;
           intros re2; rewrite re2 by trivial.
           generalize (@nnrc_core_eval_remove_free_env h ((v1,d)::nil)); 
             simpl; intros re3. rewrite re3; intuition.
         *  generalize (@nnrc_core_eval_swap_neq h nil v0 d); simpl;
            intros re1; repeat rewrite re1 by trivial.
            rewrite IHe3; intuition.
  Qed.

  (* This relation is finer then the Proper relation already shown *)
  Lemma nnrc_core_eval_equiv_free_in_env:
    forall n,
    forall env1 env2,
      (forall x, In x (nnrc_free_vars n) -> lookup equiv_dec env1 x = lookup equiv_dec env2 x) ->
      forall h,
        nnrc_core_eval h env1 n = nnrc_core_eval h env2 n.
  Proof.
    intros n.
    nnrc_cases (induction n) Case; intros env1 env2 Henv_eq h.
    - Case "NNRCVar"%string.
      simpl.
      apply Henv_eq.
      simpl; auto.
    - Case "NNRCConst"%string.
      simpl.
      reflexivity.
    - Case "NNRCBinop"%string.
      simpl.
      rewrite (IHn1 env1 env2).
      rewrite (IHn2 env1 env2).
      reflexivity.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCBinop b n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nnrc_free_vars n2)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCBinop b n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nnrc_free_vars n1)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
    - Case "NNRCUnop"%string.
      simpl.
      rewrite (IHn env1 env2).
      reflexivity.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCUnop u n)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nnrc_free_vars n)); [ | contradiction ].
        simpl in n0.
        assumption.
    - Case "NNRCLet"%string.
      simpl.
      rewrite (IHn1 env1 env2).
      destruct (nnrc_core_eval h env2 n1); try congruence.
      rewrite (IHn2 ((v, d) :: env1) ((v, d) :: env2)); try reflexivity.
      intros x.
      simpl.
      destruct (equiv_dec x v); try reflexivity.
      + intros Hx.
        destruct (in_dec equiv_dec x (nnrc_free_vars (NNRCLet v n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nnrc_free_vars n2)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n.
        apply (not_in_remove_impl_not_in x v); assumption.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCLet v n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nnrc_free_vars n1)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
    - Case "NNRCFor"%string.
      simpl.
      rewrite (IHn1 env1 env2).
      destruct (nnrc_core_eval h env2 n1); try reflexivity.
      destruct d; try reflexivity.
      unfold lift.
      
      assert (rmap (fun d1 : data => nnrc_core_eval h ((v, d1) :: env1) n2) l = rmap (fun d1 : data => nnrc_core_eval h ((v, d1) :: env2) n2) l) as Hfun_eq; try solve [rewrite Hfun_eq; reflexivity].
      apply rmap_ext; intros d ind.
      rewrite (IHn2 ((v, d) :: env1) ((v, d) :: env2)); try reflexivity.
      intros x.
      simpl.
      destruct (equiv_dec x v); try reflexivity.
      + intros Hx.
        destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCFor v n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nnrc_free_vars n2)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n.
        apply (not_in_remove_impl_not_in x v); assumption.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCFor v n1 n2)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nnrc_free_vars n1)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
    - Case "NNRCIf"%string.
      simpl.
      unfold olift.
      rewrite (IHn1 env1 env2).
      destruct (nnrc_core_eval h env2 n1); try reflexivity.
      destruct d; try reflexivity.
      destruct b.
      + rewrite (IHn2 env1 env2).
        reflexivity.
        * intros x Hx.
          destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCIf n1 n2 n3)));
            [ apply Henv_eq; assumption | ].
          assert (~In x (nnrc_free_vars n2)); [ | contradiction ].
          simpl in n.
          apply nin_app_or in n.
          destruct n.
          apply nin_app_or in H0.
          destruct H0; assumption.
      + rewrite (IHn3 env1 env2).
        reflexivity.
        * intros x Hx.
          destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCIf n1 n2 n3)));
            [ apply Henv_eq; assumption | ].
          assert (~In x (nnrc_free_vars n3)); [ | contradiction ].
          simpl in n.
          apply nin_app_or in n.
          destruct n.
          apply nin_app_or in H0.
          destruct H0; assumption.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCIf n1 n2 n3)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nnrc_free_vars n1)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
    - Case "NNRCEither"%string.
      simpl.
      rewrite (IHn1 env1 env2).
      destruct (nnrc_core_eval h env2 n1); try reflexivity.
      destruct (d); try reflexivity.
      + rewrite (IHn2 ((v, d0) :: env1) ((v, d0) :: env2)); try reflexivity.
        simpl.
        intros x.
        destruct (equiv_dec x v); try reflexivity.
        * intros Hx.
          destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCEither n1 v n2 v0 n3)));
            [ apply Henv_eq; assumption | ].
          assert (~In x (nnrc_free_vars n2)); [ | contradiction ].
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
          destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCEither n1 v n2 v0 n3)));
            [ apply Henv_eq; assumption | ].
          assert (~In x (nnrc_free_vars n3)); [ | contradiction ].
          simpl in n.
          apply nin_app_or in n.
          destruct n.
          apply nin_app_or in H0.
          destruct H0.
          apply (not_in_remove_impl_not_in x v0); assumption.
      + intros x Hx.
        destruct (in_dec string_eqdec x (nnrc_free_vars (NNRCEither n1 v n2 v0 n3)));
          [ apply Henv_eq; assumption | ].
        assert (~In x (nnrc_free_vars n1)); [ | contradiction ].
        simpl in n.
        apply nin_app_or in n.
        destruct n; assumption.
    - Case "NNRCGroupBy"%string. (* Fail case for core *)
      intros; reflexivity.
  Qed.

  Lemma nnrc_core_eval_equiv_env:
    forall n,
    forall env1 env2,
      (forall x, lookup equiv_dec env1 x = lookup equiv_dec env2 x) ->
      forall h,
        nnrc_core_eval h env1 n = nnrc_core_eval h env2 n.
  Proof.
    intros.
    apply nnrc_core_eval_lookup_equiv_prop; trivial.
  Qed.

  Lemma nnrc_no_free_vars_eval_equiv_env:
    forall n,
    forall env1 env2,
      nnrc_free_vars n = nil ->
      forall h,
        nnrc_core_eval h env1 n = nnrc_core_eval h env2 n.
  Proof.
    intros.
    apply nnrc_core_eval_equiv_free_in_env; intros.
    rewrite H in H0; simpl in H0.
    contradiction.
  Qed.

  Lemma nnrc_core_eval_single_context_var_uncons h env n v d:
    lookup equiv_dec env v = Some d ->
    nnrc_core_eval h env n = nnrc_core_eval h ((v, d) :: env) n.
  Proof.
    intros.
    apply nnrc_core_eval_equiv_env.
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

  Lemma nnrc_core_eval_single_context_var h env n v d:
    (forall x, In x (nnrc_free_vars n) -> x = v) ->
    lookup equiv_dec env v = Some d ->
    nnrc_core_eval h ((v, d) :: nil) n = nnrc_core_eval h env n.
  Proof.
    intros.
    rewrite (nnrc_core_eval_single_context_var_uncons h env n v d); try assumption.
    clear H0.
    induction env; try reflexivity.
    destruct a.
    case (string_eqdec v0 v).
    * Case "v0 = v"%string.
      intros Hv; red in Hv; rewrite Hv in *; clear Hv.
      rewrite (nnrc_core_eval_remove_duplicate_env nil v d nil d0 env n).
      simpl. assumption.
    * Case "v0 <> v"%string.
      intros Hv.
      rewrite (nnrc_core_eval_remove_free_env ((v, d)::nil) v0 d0 env n); try solve [ simpl; reflexivity ].
      rewrite IHenv. reflexivity.
      specialize (H v0).
      unfold not.
      intros H'.
      assert (v0 = v); try congruence.
      apply H.
      exact H'.
  Qed.

  Lemma nnrc_core_eval_single_context_var_cons h env n v d:
    (forall x, In x (nnrc_free_vars n) -> x = v) ->
    nnrc_core_eval h ((v, d) :: nil) n = nnrc_core_eval h ((v,d)::env) n.
  Proof.
    intros.
    apply nnrc_core_eval_single_context_var; try assumption.
    simpl.
    match_destr.
    congruence.
  Qed.

  Lemma nnrc_core_eval_single_context_var_cons_keepone h env n v d v1 d1:
    (forall x, In x (nnrc_free_vars n) -> x = v) ->
    nnrc_core_eval h ((v, d) :: (v1, d1) :: nil) n = nnrc_core_eval h ((v,d) :: (v1,d1) :: env) n.
  Proof.
    intros.
    rewrite <- (nnrc_core_eval_single_context_var h ((v,d) :: (v1,d1) :: nil) n v d); try assumption.
    - rewrite <- (nnrc_core_eval_single_context_var h ((v,d) :: (v1,d1) :: env) n v d); try assumption; trivial.
      simpl; match_destr; congruence.
    - simpl; match_destr; congruence.
  Qed.

  Lemma nnrc_core_eval_single_context_var_two_cons h env n v1 d1 v2 d2 :
    (forall x, In x (nnrc_free_vars n) -> x = v1 \/ x = v2) ->
    nnrc_core_eval h ((v1,d1) :: (v2,d2) :: nil) n = nnrc_core_eval h ((v1,d1) :: (v2,d2) :: env) n.
  Proof.
    intros.
    induction env; try reflexivity.
    destruct a.
    case (string_eqdec v1 v); intros.
    red in e; rewrite e in *; clear e.
    rewrite nnrc_core_eval_remove_duplicate_env_weak; assumption.
    case (string_eqdec v2 v); intros.
    red in e; rewrite e in *; clear e.
    rewrite nnrc_core_eval_remove_duplicate_env_weak_cons; assumption.
    rewrite (nnrc_core_eval_remove_free_env ((v1,d1)::(v2,d2)::nil) v d env n).
    assumption.
    specialize (H v).
    unfold not; intros.
    specialize (H H0).
    elim H; intros; congruence.
  Qed.

  Lemma nnrc_core_eval_single_context_var_cons_rmap h env n v l:
    (forall x, In x (nnrc_free_vars n) -> x = v) ->
    rmap (fun d => nnrc_core_eval h ((v, d) :: nil) n) l =
    rmap (fun d => nnrc_core_eval h ((v,d)::env) n) l.
  Proof.
    intros.
    induction l; simpl; try reflexivity.
    rewrite (nnrc_core_eval_single_context_var_cons h env n v a); try assumption.
    destruct (nnrc_core_eval h ((v, a) :: env) n); try reflexivity.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma nnrc_core_eval_single_context_var_cons_keepone_rmap h env n v v1 d1 l:
    (forall x, In x (nnrc_free_vars n) -> x = v) ->
    rmap (fun d => nnrc_core_eval h ((v, d) :: (v1,d1) :: nil) n) l =
    rmap (fun d => nnrc_core_eval h ((v,d) :: (v1,d1) :: env) n) l.
  Proof.
    intros.
    induction l; simpl; try reflexivity.
    rewrite (nnrc_core_eval_single_context_var_cons_keepone h env n v a v1 d1); try assumption.
    destruct (nnrc_core_eval h ((v, a) :: (v1,d1) :: env) n); try reflexivity.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma rmap_skip_free_var h v1 v2 d2 n l:
    ~ In v2 (nnrc_free_vars n) ->
    (rmap (fun d : data => nnrc_core_eval h ((v1, d) :: (v2, d2) :: nil) n) l) =
    (rmap (fun d : data => nnrc_core_eval h ((v1, d) :: nil) n) l).
  Proof.
    intros; induction l; try reflexivity; simpl.
    rewrite nnrc_core_eval_remove_free_env_weak.
    destruct (nnrc_core_eval h ((v1, a) :: nil) n); try reflexivity; rewrite IHl; reflexivity.
    auto.
  Qed.

  Lemma nnrc_core_eval_cons_subst_disjoint {h: list (string*string)} e e' env v d :
    disjoint (nnrc_bound_vars e) (nnrc_free_vars e') ->
         nnrc_core_eval h env e' = Some d ->
         nnrc_core_eval h ((v,d)::env) e = nnrc_core_eval h env (nnrc_subst e v e').
  Proof.
    intros disj eval1.
    revert env e' v d disj eval1.
    nnrc_cases (induction e) Case; simpl in *;
      trivial; intros env e' v' d disj; simpl; intros eval1;
        unfold equiv_dec, olift2, olift in * .
    - Case "NNRCVar"%string.
      match_destr.
      congruence.
    - Case "NNRCBinop"%string.
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      erewrite IHe1 by eauto.
      erewrite IHe2 by eauto.
      trivial.
    - Case "NNRCUnop"%string.
      erewrite IHe by eauto.
      trivial.
    - Case "NNRCLet"%string.
      apply disjoint_cons_inv1 in disj.
      destruct disj as [disj nin].
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      erewrite IHe1 by eauto.
      match_destr.
      match_destr.
      + red in e; subst.
        unfold var in *.
        generalize (nnrc_core_eval_remove_duplicate_env (h:=h) nil v' d0 nil d env e2); simpl; intros re1; rewrite re1; trivial.
      + erewrite <- IHe2; try reflexivity; eauto 2.
        * generalize (nnrc_core_eval_swap_neq (h:=h) nil v d0 v' d); simpl;
          intros re1; rewrite re1; eauto.
        * generalize (nnrc_core_eval_remove_free_env (h:=h) nil v d0 env);
            simpl; intros re1; rewrite re1; eauto.
    - Case "NNRCFor"%string.
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
        generalize (nnrc_core_eval_remove_duplicate_env (h:=h) nil v' x nil d env e2); simpl; congruence.
      + f_equal.
        apply rmap_ext; intros.
        generalize (nnrc_core_eval_swap_neq (h:=h) nil v x v' d); simpl;
          intros re1; rewrite re1; eauto 2.
        erewrite IHe2; try reflexivity; eauto 2.
        generalize (nnrc_core_eval_remove_free_env (h:=h) nil v x env);
            simpl; intros re2; rewrite re2; eauto.
    - Case "NNRCIf"%string.
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
    - Case "NNRCEither"%string.
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
            generalize (nnrc_core_eval_remove_duplicate_env (h:=h) nil v' d0 nil d env e2); simpl; intros re1; rewrite re1; trivial.
          + generalize (nnrc_core_eval_swap_neq (h:=h) nil v d0 v' d); simpl;
                intros re1; rewrite re1; eauto 2.
            erewrite IHe2; try reflexivity; eauto 2.
            generalize (nnrc_core_eval_remove_free_env (h:=h) nil v d0 env);
                simpl; intros re2; rewrite re2; trivial.
        } 
      + {
          match_destr.
          + red in e; subst.
            unfold var in *.
            generalize (nnrc_core_eval_remove_duplicate_env (h:=h) nil v' d0 nil d env e3); simpl; intros re1; rewrite re1; trivial.
          + generalize (nnrc_core_eval_swap_neq (h:=h) nil v0 d0 v' d); simpl;
                intros re1; rewrite re1; eauto 2.
            erewrite IHe3; try reflexivity; eauto 2.
            generalize (nnrc_core_eval_remove_free_env (h:=h) nil v0 d0 env);
                simpl; intros re2; rewrite re2; trivial.
        }
  Qed.

  Lemma nnrc_pick_name_neq_nfree sep renamer avoid v e :
    v =/= nnrc_pick_name sep renamer avoid v e ->
    ~ In (nnrc_pick_name sep renamer avoid v e) (nnrc_free_vars e).
  Proof.
    unfold nnrc_pick_name, pick_same_really_fresh_in, pick_new_really_fresh_in.
    intros eqq.
    match_destr.
    - match_destr.
      + apply really_fresh_from_free.
      + congruence.
    - match_destr.
      + apply really_fresh_from_free.
      + repeat rewrite in_app_iff in n; intuition.
  Qed.

  Lemma nnrc_core_eval_cons_rename_pick h sep renamer avoid v e d env:
    nnrc_core_eval h ((nnrc_pick_name sep renamer avoid v e, d) :: env)
             (nnrc_rename_lazy e v (nnrc_pick_name sep renamer avoid v e)) = 
    nnrc_core_eval h ((v, d) :: env) e.
  Proof.
    unfold nnrc_rename_lazy.
    match_destr.
    - rewrite <- e0.
      trivial.
    - rewrite nnrc_core_eval_cons_subst; trivial.
      + apply nnrc_pick_name_neq_nfree; trivial.
      + apply nnrc_pick_name_bound.
  Qed.

  Theorem unshadow_eval {h:list (string*string)} sep renamer avoid e env :
    nnrc_core_eval h env (unshadow sep renamer avoid e) = nnrc_core_eval h env e.
  Proof.
    revert env.
    induction e; simpl; trivial; intros; try congruence.
    - rewrite IHe1.
      match_destr.
      rewrite nnrc_core_eval_cons_rename_pick.
      trivial.
    - rewrite IHe1.
      match_destr.
      match_destr.
      f_equal.
      apply rmap_ext; intros.
      rewrite <- IHe2.
      apply nnrc_core_eval_cons_rename_pick.
    - rewrite IHe1, IHe2, IHe3; trivial.
    - rewrite IHe1.
      match_destr.
      match_destr.
      + rewrite nnrc_core_eval_cons_rename_pick.
        rewrite IHe2.
        trivial.
      + rewrite nnrc_core_eval_cons_rename_pick.
        rewrite IHe3.
        trivial.
  Qed.

  Lemma nnrc_pick_name_id_nin_eq sep avoid v e :
    ~ In v (nnrc_bound_vars e) ->
    ~ In v avoid ->
    (nnrc_pick_name sep id avoid v e) = v.
  Proof.
    unfold nnrc_pick_name, id.
    intros.
    match_destr; [|congruence].
    unfold pick_same_really_fresh_in.
    match_destr.
    repeat rewrite in_app_iff in i; intuition.
  Qed.

  Lemma nnrc_rename_lazy_eq e v :
    nnrc_rename_lazy e v v = e.
  Proof.
    unfold nnrc_rename_lazy.
    match_destr.
    congruence.
  Qed.

  Lemma shadow_free_unshadow_id sep avoid (e:nnrc) : 
    shadow_free e = true ->
    (forall x, In x avoid -> ~In x (nnrc_bound_vars e)) ->
    unshadow sep id avoid e = e.
  Proof.
    induction e; simpl; trivial; repeat rewrite andb_true_iff;
    intuition;
     try apply in_in_app_false in H0;
     intuition; try congruence.
    - rewrite H1, H4 by (intros ? av; generalize (H0 _ av); intuition).
      match_destr_in H.
      rewrite nnrc_pick_name_id_nin_eq.
      + rewrite nnrc_rename_lazy_eq; trivial.
      + trivial.
      + intros inn; apply (H0 _ inn); intuition.
    - rewrite H1, H4 by (intros ? av; generalize (H0 _ av); intuition).
      match_destr_in H.
      rewrite nnrc_pick_name_id_nin_eq.
      + rewrite nnrc_rename_lazy_eq; trivial.
      + trivial.
      + intros inn; apply (H0 _ inn); intuition.
    - rewrite H0, H1, H5 by (intros ? av; generalize (H7 _ av); intuition).
      trivial.
    - match_destr_in H. match_destr_in H5.
      assert (H0':forall x : var,
       In x avoid ->
       (v = x \/
       v0 = x \/
       In x (nnrc_bound_vars e1) \/
       In x (nnrc_bound_vars e2) \/
       In x (nnrc_bound_vars e3)) -> False)
        by (intros ? av; specialize (H0 _ av);
      intuition; try solve[apply nin_app_or in H11; intuition]).
      rewrite H1, H6, H7; try solve [intros ? av; specialize (H0' _ av); intuition].
      rewrite nnrc_pick_name_id_nin_eq.
      + rewrite nnrc_rename_lazy_eq; trivial.
        rewrite nnrc_pick_name_id_nin_eq.
        * rewrite nnrc_rename_lazy_eq; trivial.
        * trivial.
        * intros inn; apply (H0 _ inn); intuition.
      + trivial.
      + intros inn; apply (H0 _ inn); intuition.
  Qed.

  Lemma unshadow_id_idempotent sep renamer1 avoid (e:nnrc) 
    : unshadow sep id avoid (unshadow sep renamer1 avoid e) = unshadow sep renamer1 avoid e.
  Proof.
    apply shadow_free_unshadow_id.
    - apply unshadow_shadow_free.
    - apply unshadow_avoid.
  Qed.

  (* Java equivalent: inlined in several places *)  
  Definition nnrc_unshadow_sep := "$"%string.
  (* Java equivalent: inlined in several places *)  
  Definition unshadow_simpl := unshadow nnrc_unshadow_sep id.

  (* Java equivalent: MROptimizer.nnrc_subslist_subst *)
  Definition nnrc_substlist_subst (substlist:list (var*var)) (e:nnrc) :=
    List.fold_left
      (fun e (subst: var * var) =>
         let (x, x') := subst in
         nnrc_subst e x (NNRCVar x'))
      substlist e.


  Section core.
    (* Proof for operations that preserve core NNRC property *)
    Lemma nnrc_subst_preserve_core n1 n2 v1 :
      nnrcIsCore n1 -> nnrcIsCore n2 -> nnrcIsCore (nnrc_subst n1 v1 n2).
    Proof.
      induction n1; simpl; intros; intuition;
      try (destruct (equiv_dec v v1); trivial);
      destruct (equiv_dec v0 v1); trivial.
    Qed.

    Lemma nnrc_rename_lazy_preserve_core n v1 v2 :
      nnrcIsCore n -> nnrcIsCore (nnrc_rename_lazy n v1 v2).
    Proof.
      induction n; unfold nnrc_rename_lazy; simpl;
      intros; intuition; destruct (equiv_dec v1 v2); try trivial; simpl; auto.
      - destruct (equiv_dec v v1); trivial.
      - split; apply nnrc_subst_preserve_core; simpl; auto.
      - apply nnrc_subst_preserve_core; simpl; auto.
      - split.
        + apply nnrc_subst_preserve_core; simpl; auto.
        + destruct (equiv_dec v v1); auto.
          apply nnrc_subst_preserve_core; simpl; auto.
      - split.
        + apply nnrc_subst_preserve_core; simpl; auto.
        + destruct (equiv_dec v v1); auto.
          apply nnrc_subst_preserve_core; simpl; auto.
      - split; [|split]; apply nnrc_subst_preserve_core; simpl; auto.
      - split; [|split].
        + apply nnrc_subst_preserve_core; simpl; auto.
        + destruct (equiv_dec v v1); auto.
          apply nnrc_subst_preserve_core; simpl; auto.
        + destruct (equiv_dec v0 v1); auto.
          apply nnrc_subst_preserve_core; simpl; auto.
    Qed.
  
    Lemma unshadow_simpl_preserve_core avoid n :
      nnrcIsCore n -> nnrcIsCore (unshadow_simpl avoid n).
    Proof.
      induction n; simpl; intros; intuition;
      apply nnrc_rename_lazy_preserve_core; auto.
    Qed.
    
    Lemma unshadow_preserve_core sep renamer avoid n :
      nnrcIsCore n -> nnrcIsCore (unshadow sep renamer avoid n).
    Proof.
      induction n; simpl; intros; intuition;
      apply nnrc_rename_lazy_preserve_core; auto.
    Qed.
    
  End core.
End NNRCShadow.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
