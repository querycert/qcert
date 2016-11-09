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

Section NRewUtil.
  Require Import String List Arith.
  Require Import Program.
  Require Import Peano_dec.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.

  Require Import NNRC NNRCEq NNRCShadow.

  Context {fruntime:foreign_runtime}.

  Lemma not_in_over_app {A} (x:A) (l1 l2:list A) :
    ~In x (l1++l2) -> ~In x l1 /\ ~In x l2.
  Proof.
    unfold not; intros.
    split; intros.
    apply H.
    apply in_or_app; left; assumption.
    apply H.
    apply in_or_app; right; assumption.
  Qed.

  Lemma really_fresh_is_really_fresh {sep} {oldvar} (avoid:list var) (e:nrc) (x:var) :
    x = really_fresh_in sep oldvar avoid e ->
    (~In x avoid) /\ (~In x (nrc_free_vars e)) /\ (~In x (nrc_bound_vars e)).
  Proof.
    intros. rewrite H.
    split.
    apply really_fresh_from_avoid.
    split.
    apply really_fresh_from_free.
    apply really_fresh_from_bound.
  Qed.

  Lemma split_really_fresh_app (x:var) l1 l2 l3 l4 :
    ~ False /\
       ~ In x (l1 ++ l2) /\
       ~ In x (l3 ++ l4) ->
    ((~In x l1) /\ (~In x l2)) /\
    ((~In x l3) /\ (~In x l4)).
  Proof.
    intros.
    elim H; clear H; intros; clear H; elim H0; clear H0; intros.
    split.
    apply not_in_over_app; assumption.
    apply not_in_over_app; assumption.
  Qed.
  
  Lemma split_really_fresh_app2 (x:var) l1 l2 l3 l4 :
    ~ False /\
       ~ In x (l1 ++ l2) /\
       ~ In x (l3 ++ l4) ->
    (~ False /\ (~In x l1) /\ (~In x l3)) /\
    (~ False /\ (~In x l2) /\ (~In x l4)).
  Proof.
    intros.
    elim H; clear H; intros; clear H; elim H0; clear H0; intros.
    assert (~ In x l1 /\ ~ In x l2)
      by (apply not_in_over_app; assumption).
    assert (~ In x l3 /\ ~ In x l4)
      by (apply not_in_over_app; assumption).
    clear H0 H; elim H1; clear H1; intros; elim H2; clear H2; intros.
    split; split; auto.
  Qed.

  Lemma dupl_var_ignored {h:list (string*string)} (d1 d2:data) (env:bindings) (v:var) (e:nrc):
    nrc_eval h ((v,d1) :: (v,d2) :: env) e = nrc_eval h ((v,d1)::env) e.
  Proof.
    generalize (@nrc_eval_remove_duplicate_env _ h nil v d1 nil d2 env e); intros.
    rewrite app_nil_l in *.
    rewrite app_nil_l in *.
    rewrite app_nil_l in *.
    rewrite app_nil_l in *.
    assumption.
  Qed.

  Lemma not_or p1 p2:
    ~(p1 \/ p2) -> ~p1 /\ ~p2.
  Proof.
    intros.
    split; unfold not in *; intros.
    elim H; left; assumption.
    elim H; right; assumption.
  Qed.
  
  Lemma remove_in l (x v:var):
    v<>x -> ~ In x (remove equiv_dec v l) ->
    ~ In x l.
  Proof.
    intros.
    induction l; unfold not in *; intros.
    simpl in H1; assumption.
    simpl in *.
    destruct (equiv_dec v a).
    - rewrite e in *; clear e.
      elim H1; intros. apply (H H2).
      apply (IHl H0 H2).
    - simpl in *.
      assert (a <> x /\ ~In x (remove equiv_dec v l)).
      apply not_or; assumption.
      elim H2; intros.
      apply IHl; try auto.
      elim H1; intros.
      congruence.
      assumption.
  Qed.
      
  Lemma split_really_fresh_app3 (v x:var) l1 l2 l3 l4 :
    ~ False /\
       ~
       In x (l1 ++ remove equiv_dec v l2) /\
       ~ (v = x \/ In x (l3 ++ l4)) ->
    (v <> x) /\ (~ False /\ (~In x l1) /\ (~In x l3)) /\
    (~ False /\ (~In x l2) /\ (~In x l4)).
  Proof.
    intros.
    elim H; clear H; intros. clear H; elim H0; clear H0; intros.
    assert (v<>x /\ ~(In x (l3 ++ l4))).
    apply not_or; assumption.
    elim H1; clear H0 H1; intros.
    split; try assumption.
    assert (~ In x l1 /\ ~ In x (remove equiv_dec v l2))
      by (apply not_in_over_app; assumption).
    assert (~ In x l3 /\ ~ In x l4)
      by (apply not_in_over_app; assumption).
    elim H2; clear H2 H1 H; intros.
    elim H3; clear H3; intros.
    split; split; auto.
    split; try assumption.
    apply (remove_in l2 x v).
    assumption.
    assumption.
  Qed.
    
  Lemma nrc_subst_rename {sep} {oldvar} (e1 e2:nrc) (x1 x2:var) :
    x2 = really_fresh_in sep oldvar nil e2 ->
    nnrc_eq (NRCLet x1 e1 e2) (NRCLet x2 e1 (nrc_subst e2 x1 (NRCVar x2))).
  Proof.
    unfold nnrc_eq; simpl; intros ? ? ? _.
    generalize (really_fresh_is_really_fresh nil e2 x2 H); intros. clear H.
    destruct (nrc_eval h env e1); try reflexivity.
    revert env; nrc_cases (induction e2) Case; intros; simpl.
    - Case "NRCVar"%string.
      simpl in * .
      match_destr; unfold Equivalence.equiv in *; subst; match_destr; try congruence; simpl; try congruence; match_destr;
        unfold Equivalence.equiv in *; try congruence.
      intuition.
    - Case "NRCConst"%string.
      reflexivity.
    - Case "NRCBinop"%string.
      simpl in *.
      generalize (split_really_fresh_app2 x2 _ _ _ _ H0); clear H0; intros.
      elim H; clear H; intros.
      specialize (IHe2_1 H); specialize (IHe2_2 H0); clear H H0.
      rewrite IHe2_1; rewrite IHe2_2; reflexivity.
    - Case "NRCUnop"%string.
      specialize (IHe2 H0). rewrite IHe2; reflexivity.
    - Case "NRCLet"%string.
      simpl in *.
      generalize (split_really_fresh_app3 v x2 _ _ _ _ H0); clear H0; intros.
      elim H; clear H; intros; simpl in *.
      elim H0; clear H0; intros; simpl in *.
      specialize (IHe2_1 H0). specialize (IHe2_2 H1).
      rewrite IHe2_1; clear IHe2_1.
      destruct (nrc_eval h ((x2,d) :: env) (nrc_subst e2_1 x1 (NRCVar x2))); try reflexivity.
      match_destr; unfold Equivalence.equiv in *; subst; simpl.
      + (* v === x1 so x1 is ignored and x2 too *)
        rewrite dupl_var_ignored.
        generalize (@nrc_eval_swap_neq _ h nil x1 d0 x2 d env e2_2 H); intros.
        rewrite app_nil_l in H2.
        rewrite app_nil_l in H2.
        unfold var in *.
        rewrite H2; clear H2.
        clear H H0 IHe2_2.
        elim H1 ; clear H1; intros; clear H.
        elim H0; clear H0; intros; clear H0.
        generalize (@nrc_eval_remove_free_env _ h nil x2 d ((x1,d0) :: env) e2_2 H); intros.
        rewrite app_nil_l in H0.
        rewrite app_nil_l in H0.
        unfold var in *.
        rewrite H0; reflexivity.
      + (* v =/= x1 and substitution moves forward *)
        generalize (@nrc_eval_swap_neq _ h nil v d0 x1 d env e2_2); intros.
        assert (v <> x1) by auto.
        specialize (H2 H3); clear H3.
        rewrite app_nil_l in H2.
        rewrite app_nil_l in H2.
        unfold var in *.
        rewrite H2; clear H2.
        generalize (@nrc_eval_swap_neq _ h nil v d0 x2 d env (nrc_subst e2_2 x1 (NRCVar x2)) H); intros.
        rewrite app_nil_l in H2.
        rewrite app_nil_l in H2.
        rewrite H2; clear H2.
        rewrite (IHe2_2 ((v, d0) :: env)).
        reflexivity.
    - Case "NRCFor"%string.
      simpl in *.
      generalize (split_really_fresh_app3 v x2 _ _ _ _ H0); clear H0; intros.
      elim H; clear H; intros; simpl in *.
      elim H0; clear H0; intros; simpl in *.
      specialize (IHe2_1 H0). specialize (IHe2_2 H1).
      rewrite IHe2_1; clear IHe2_1.
      destruct (nrc_eval h ((x2,d) :: env) (nrc_subst e2_1 x1 (NRCVar x2))); try reflexivity.
      destruct (equiv_dec v x1); try reflexivity.
      + (* v === x1 so x1 is ignored and x2 too *)
        rewrite e in *; clear e.
        destruct d0; try reflexivity; simpl.
        induction l; try reflexivity; simpl.
        rewrite dupl_var_ignored.
        generalize (@nrc_eval_swap_neq _ h nil x1 a x2 d env e2_2 H); intros.
        rewrite app_nil_l in H2.
        rewrite app_nil_l in H2.
        unfold var in *.
        rewrite H2; clear H2.
        clear H H0 IHe2_2.
        elim H1 ; clear H1; intros; clear H.
        elim H0; clear H0; intros; clear H0.
        generalize (@nrc_eval_remove_free_env _ h nil x2 d ((x1,a) :: env) e2_2 H); intros.
        rewrite app_nil_l in H0.
        unfold var in *.
        rewrite app_nil_l in H0.
        rewrite H0.
        destruct (nrc_eval h ((x1,a)::env) e2_2); try reflexivity.
        unfold lift in *; simpl in *.
        destruct (rmap (fun d1 : data => nrc_eval h ((x1, d1) :: (x1, d) :: env) e2_2)
            l); destruct (rmap (fun d1 : data => nrc_eval h ((x1, d1) :: (x2, d) :: env) e2_2)
            l); congruence.
      + (* v =/= x1 and substitution moves forward *)
        destruct d0; try reflexivity; simpl.
        induction l; try reflexivity; simpl.
        generalize (@nrc_eval_swap_neq _ h nil v a x1 d env e2_2); intros.
        assert (v <> x1) by auto.
        specialize (H2 H3); clear H3.
        rewrite app_nil_l in H2.
        rewrite app_nil_l in H2.
        unfold var in *.
        rewrite H2; clear H2.
        generalize (@nrc_eval_swap_neq _ h nil v a x2 d env (nrc_subst e2_2 x1 (NRCVar x2)) H); intros.
        rewrite app_nil_l in H2.
        rewrite app_nil_l in H2.
        rewrite H2; clear H2.
        rewrite (IHe2_2 ((v, a) :: env)).
        destruct (nrc_eval h ((x2, d) :: (v, a) :: env) (nrc_subst e2_2 x1 (NRCVar x2))); try reflexivity.
        unfold lift in *; simpl in *.
        destruct (rmap (fun d1 : data => nrc_eval h ((v, d1) :: (x1, d) :: env) e2_2)
            l); destruct (rmap (fun d1 : data => nrc_eval h ((v, d1) :: (x2, d) :: env) (nrc_subst e2_2 x1 (NRCVar x2)))
            l); congruence.
    - Case "NRCIf"%string.
      simpl in *.
      generalize (split_really_fresh_app2 x2 _ _ _ _ H0); clear H0; intros.
      elim H; clear H; intros.
      generalize (split_really_fresh_app2 x2 _ _ _ _ H0); clear H0; intros.
      elim H0; clear H0; intros.
      specialize (IHe2_1 H); specialize (IHe2_2 H0); specialize (IHe2_3 H1); clear H H0 H1.
      rewrite IHe2_1; rewrite IHe2_2; rewrite IHe2_3.
      reflexivity.
    - Case "NRCEither"%string.
      simpl in H0.
      repeat rewrite nin_app_or in H0.
      destruct H0 as [_[[?[??]]?]].
      apply not_or in H2. destruct H2.
      apply not_or in H3. destruct H3.
      repeat rewrite nin_app_or in H4.
      destruct H4 as [?[??]].
      rewrite IHe2_1 by (simpl; intuition).
      rewrite <- remove_in_neq in H0,H1 by congruence.
      match_destr. match_destr.
      + match_destr; unfold equiv, complement in *; subst.
         * generalize (@nrc_eval_remove_duplicate_env _ h nil x1 d0 nil); simpl;
            intros re1; rewrite re1.
            generalize (@nrc_eval_remove_free_env _ h ((x1,d0)::nil)); simpl;
            intros re2; rewrite re2 by trivial.
            trivial.
         * generalize (@nrc_eval_swap_neq _ h nil v d0); simpl;
            intros re1; repeat rewrite re1 by trivial.
            rewrite IHe2_2; trivial.
            simpl; intuition.
      + match_destr; unfold equiv, complement in *; subst.
         * generalize (@nrc_eval_remove_duplicate_env _ h nil x1 d0 nil); simpl;
            intros re1; rewrite re1.
            generalize (@nrc_eval_remove_free_env _ h ((x1,d0)::nil)); simpl;
            intros re2; rewrite re2 by trivial.
            trivial.
         * generalize (@nrc_eval_swap_neq _ h nil v0 d0); simpl;
            intros re1; repeat rewrite re1 by trivial.
            rewrite IHe2_3; trivial.
            simpl; intuition.
  Qed.
  
  (* Java equivalent: NnrcOptimizer.var_use (nested enum) *)
  Inductive var_use :=
  | NotUsed
  | UsedOnce
  | UsedMany.

  (* Java equivalent: NnrcOptimizer.use_sum *)
  Definition use_sum u1 u2 :=
    match (u1,u2) with
      | (UsedMany,_) => UsedMany
      | (_,UsedMany) => UsedMany
      | (UsedOnce,UsedOnce) => UsedMany
      | (UsedOnce,NotUsed) => UsedOnce
      | (NotUsed,UsedOnce) => UsedOnce
      | (NotUsed,NotUsed) => NotUsed
    end.

  Lemma use_sum_once u1 u2:
    use_sum u1 u2 = UsedOnce <->
    ((u1 = UsedOnce) /\ (u2 = NotUsed)) \/
    ((u1 = NotUsed) /\ (u2 = UsedOnce)).
  Proof.    
    split; intros.
    - destruct u1; destruct u2; unfold use_sum in H; simpl in H; try congruence.
      right; split; reflexivity.
      left; split; reflexivity.
    - elim H; intros;
      elim H0; intros; rewrite H1; rewrite H2; reflexivity.
  Qed.
  
  Lemma use_sum_not u1 u2:
    use_sum u1 u2 = NotUsed <->
    (u1 = NotUsed) /\ (u2 = NotUsed).
  Proof.    
    split; intros.
    - destruct u1; destruct u2; unfold use_sum in H; simpl in H; try congruence.
      split; reflexivity.
    - elim H; intros; rewrite H0; rewrite H1; reflexivity.
  Qed.
  
  (* Java equivalent: NnrcOptimizer.use_alt *)
  Definition use_alt u1 u2 :=
    match (u1,u2) with
      | (UsedOnce,UsedOnce) => UsedOnce
      | (NotUsed,NotUsed) => NotUsed
      | _ => UsedMany
    end.

  Lemma use_alt_once u1 u2:
    use_alt u1 u2 = UsedOnce <->
    ((u1 = UsedOnce) /\ (u2 = UsedOnce)).
  Proof.    
    split; intros.
    - destruct u1; destruct u2; unfold use_alt in H; simpl in H; try congruence.
      split; reflexivity.
    - elim H; intros;
      elim H0; rewrite H0; rewrite H1; reflexivity.
  Qed.
  
  Lemma use_alt_not u1 u2:
    use_alt u1 u2 = NotUsed <->
    ((u1 = NotUsed) /\ (u2 = NotUsed)).
  Proof.    
    split; intros.
    - destruct u1; destruct u2; unfold use_alt in H; simpl in H; try congruence.
      split; reflexivity.
    - elim H; intros;
      elim H0; rewrite H0; rewrite H1; reflexivity.
  Qed.
  
  (* Java equivalent: NnrcOptimizer.use_exp *)
  Definition use_exp u1 u2 :=
    match (u1,u2) with
      | (UsedMany,_) => UsedMany
      | (_,UsedMany) => UsedMany
      | (_,UsedOnce) => UsedMany
      | (UsedOnce,NotUsed) => UsedOnce
      | (NotUsed,NotUsed) => NotUsed
    end.
  
  Lemma use_exp_once u1 u2:
    use_exp u1 u2 = UsedOnce <-> (u1 = UsedOnce) /\ (u2 = NotUsed).
  Proof.    
    split; intros.
    - destruct u1; destruct u2; unfold use_exp in H; simpl in H; try congruence.
      split; reflexivity.
    - elim H; intros; rewrite H0; rewrite H1; reflexivity.
  Qed.

  Lemma use_exp_not x y :
    (use_exp x y) = NotUsed <->
    (x = NotUsed /\ y = NotUsed).
  Proof.
    unfold use_exp.
    match_destr; try match_destr; intuition; discriminate.
  Qed.
  
  (* Java equivalent: NnrcOptimizer.use_count *)
  Fixpoint use_count (x:var) (e:nrc) : var_use :=
    match e with
      | NRCVar x' => (if x == x' then UsedOnce else NotUsed)
      | NRCConst _ => NotUsed
      | NRCBinop _ e1 e2 =>
        use_sum (use_count x e1) (use_count x e2)
      | NRCUnop _ e1 => use_count x e1
      | NRCLet x' e1 e2 =>
        if (x == x') then use_count x e1
        else use_sum (use_count x e1) (use_count x e2)
      | NRCFor x' e1 e2 =>
        use_exp (use_count x e1) (if x == x' then NotUsed else  (use_count x e2))
      | NRCIf e1 e2 e3 =>
        use_sum (use_count x e1) (use_alt (use_count x e2) (use_count x e3))
      | NRCEither ed xl el xr er =>
        use_sum
                   (use_count x ed)
                   (use_alt
                      (if x == xl then NotUsed else use_count x el)
                      (if x == xr then NotUsed else use_count x er))
    end.

  Lemma NotUsed_nfree v e :
    use_count v e = NotUsed <-> ~ In v (nrc_free_vars e).
  Proof.
    induction e; simpl; trivial;
    repeat rewrite use_exp_not;
    repeat rewrite use_sum_not;
    repeat rewrite use_alt_not;
    repeat rewrite nin_app_or.
    - match_destr; intuition congruence.
    - intuition.
    - intuition.
    - match_destr; unfold equiv, complement in *; subst.
      + intuition. eapply remove_In; eauto.
      + rewrite use_sum_not.
         rewrite <- remove_in_neq; trivial.
         intuition.
    - match_destr; unfold equiv, complement in *; subst.
      + intuition. eapply remove_In; eauto.
      + rewrite <- remove_in_neq; trivial.
         intuition.
    - intuition.
    - match_destr; match_destr; unfold equiv, complement in *; subst.
      + subst; intuition; eapply remove_In; eauto.
      + rewrite <- (remove_in_neq _ _ v1) by congruence.
         intuition; eapply remove_In; eauto.
      + rewrite <- (remove_in_neq _ _ v0) by congruence.
        intuition; eapply remove_In; eauto.
      + rewrite <- (remove_in_neq _ _ v0) by congruence.
         rewrite <- (remove_in_neq _ _ v1) by congruence.
         intuition.
  Qed.
  
  Lemma not_used_ignored {h:list(string*string)} (d:data) (env:bindings) (v:var) (e:nrc) :
    (use_count v e) = NotUsed -> nrc_eval h ((v,d)::env) e = nrc_eval h env e.
  Proof.
    rewrite NotUsed_nfree.
    generalize (@nrc_eval_remove_free_env _ h nil v d env); simpl; auto.
  Qed.

End NRewUtil.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
