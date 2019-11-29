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
Require Import Program.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNNRCRuntime.
Require Import NNRCRuntime.

Section NNRCRewriteUtil.
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

  Lemma really_fresh_is_really_fresh {sep} {oldvar} (avoid:list var) (e:nnrc) (x:var) :
    x = really_fresh_in sep oldvar avoid e ->
    (~In x avoid) /\ (~In x (nnrc_free_vars e)) /\ (~In x (nnrc_bound_vars e)).
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

  Lemma dupl_var_ignored {h:list (string*string)} {cenv}
        (d1 d2:data) (env:bindings) (v:var) (e:nnrc):
    nnrc_core_eval h cenv ((v,d1) :: (v,d2) :: env) e = nnrc_core_eval h cenv ((v,d1)::env) e.
  Proof.
    generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v d1 nil d2 env e); intros.
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

  Lemma nnrc_subst_rename {sep} {oldvar} (e1 e2:nnrc) (x1 x2:var) :
    x2 = really_fresh_in sep oldvar nil e2 ->
    nnrc_core_eq (NNRCLet x1 e1 e2) (NNRCLet x2 e1 (nnrc_subst e2 x1 (NNRCVar x2))).
  Proof.
    unfold nnrc_core_eq; simpl; intros ? ? ? ? ? _.
    generalize (really_fresh_is_really_fresh nil e2 x2 H); intros. clear H.
    destruct (nnrc_core_eval h cenv env e1); try reflexivity.
    revert env; nnrc_cases (induction e2) Case; intros; simpl.
    - Case "NNRCGetConstant"%string.
      reflexivity.
    - Case "NNRCVar"%string.
      simpl in * .
      match_destr; unfold Equivalence.equiv in *; subst; match_destr; try congruence; simpl; try congruence; match_destr;
        unfold Equivalence.equiv in *; try congruence.
      intuition.
    - Case "NNRCConst"%string.
      reflexivity.
    - Case "NNRCBinop"%string.
      simpl in *.
      generalize (split_really_fresh_app2 x2 _ _ _ _ H1); clear H1; intros.
      elim H; clear H; intros.
      specialize (IHe2_1 H); specialize (IHe2_2 H1); clear H H1.
      rewrite IHe2_1; rewrite IHe2_2; reflexivity.
    - Case "NNRCUnop"%string.
      specialize (IHe2 H1). rewrite IHe2; reflexivity.
    - Case "NNRCLet"%string.
      simpl in *.
      generalize (split_really_fresh_app3 v x2 _ _ _ _ H1); clear H1; intros.
      elim H; clear H; intros; simpl in *.
      elim H1; clear H1; intros; simpl in *.
      specialize (IHe2_1 H1). specialize (IHe2_2 H2).
      rewrite IHe2_1; clear IHe2_1.
      destruct (nnrc_core_eval h cenv ((x2,d) :: env) (nnrc_subst e2_1 x1 (NNRCVar x2))); try reflexivity.
      match_destr; unfold Equivalence.equiv in *; subst; simpl.
      + (* v === x1 so x1 is ignored and x2 too *)
        rewrite dupl_var_ignored.
        generalize (@nnrc_core_eval_swap_neq _ h cenv nil x1 d0 x2 d env e2_2 H); intros.
        rewrite app_nil_l in H3.
        rewrite app_nil_l in H3.
        unfold var in *.
        rewrite H3; clear H3.
        clear H H1 IHe2_2.
        elim H2 ; clear H2; intros; clear H.
        elim H1; clear H1; intros; clear H1.
        generalize (@nnrc_core_eval_remove_free_env _ h cenv nil x2 d ((x1,d0) :: env) e2_2 H); intros.
        rewrite app_nil_l in H1.
        rewrite app_nil_l in H1.
        unfold var in *.
        rewrite H1; reflexivity.
      + (* v =/= x1 and substitution moves forward *)
        generalize (@nnrc_core_eval_swap_neq _ h cenv nil v d0 x1 d env e2_2); intros.
        assert (v <> x1) by auto.
        specialize (H3 H4); clear H4.
        rewrite app_nil_l in H3.
        rewrite app_nil_l in H3.
        unfold var in *.
        rewrite H3; clear H3.
        generalize (@nnrc_core_eval_swap_neq _ h cenv nil v d0 x2 d env (nnrc_subst e2_2 x1 (NNRCVar x2)) H); intros.
        rewrite app_nil_l in H3.
        rewrite app_nil_l in H3.
        rewrite H3; clear H3.
        rewrite (IHe2_2 ((v, d0) :: env)).
        reflexivity.
    - Case "NNRCFor"%string.
      simpl in *.
      generalize (split_really_fresh_app3 v x2 _ _ _ _ H1); clear H1; intros.
      elim H; clear H; intros; simpl in *.
      elim H1; clear H1; intros; simpl in *.
      specialize (IHe2_1 H1). specialize (IHe2_2 H2).
      rewrite IHe2_1; clear IHe2_1.
      destruct (nnrc_core_eval h cenv ((x2,d) :: env) (nnrc_subst e2_1 x1 (NNRCVar x2))); try reflexivity.
      destruct (equiv_dec v x1); try reflexivity.
      + (* v === x1 so x1 is ignored and x2 too *)
        rewrite e in *; clear e.
        destruct d0; try reflexivity; simpl.
        induction l; try reflexivity; simpl.
        rewrite dupl_var_ignored.
        generalize (@nnrc_core_eval_swap_neq _ h cenv nil x1 a x2 d env e2_2 H); intros.
        rewrite app_nil_l in H3.
        rewrite app_nil_l in H3.
        unfold var in *.
        rewrite H3; clear H3.
        clear H H1 IHe2_2.
        elim H2 ; clear H2; intros; clear H.
        elim H1; clear H1; intros; clear H1.
        generalize (@nnrc_core_eval_remove_free_env _ h cenv nil x2 d ((x1,a) :: env) e2_2 H); intros.
        rewrite app_nil_l in H1.
        unfold var in *.
        rewrite app_nil_l in H1.
        rewrite H1.
        destruct (nnrc_core_eval h cenv ((x1,a)::env) e2_2); try reflexivity.
        unfold lift in *; simpl in *.
        destruct (lift_map (fun d1 : data => nnrc_core_eval h cenv ((x1, d1) :: (x1, d) :: env) e2_2)
                           l); destruct (lift_map (fun d1 : data => nnrc_core_eval h cenv ((x1, d1) :: (x2, d) :: env) e2_2)
                                                  l); congruence.
      + (* v =/= x1 and substitution moves forward *)
        destruct d0; try reflexivity; simpl.
        induction l; try reflexivity; simpl.
        generalize (@nnrc_core_eval_swap_neq _ h cenv nil v a x1 d env e2_2); intros.
        assert (v <> x1) by auto.
        specialize (H3 H4); clear H4.
        rewrite app_nil_l in H3.
        rewrite app_nil_l in H3.
        unfold var in *.
        rewrite H3; clear H3.
        generalize (@nnrc_core_eval_swap_neq _ h cenv nil v a x2 d env (nnrc_subst e2_2 x1 (NNRCVar x2)) H); intros.
        rewrite app_nil_l in H3.
        rewrite app_nil_l in H3.
        rewrite H3; clear H3.
        rewrite (IHe2_2 ((v, a) :: env)).
        destruct (nnrc_core_eval h cenv ((x2, d) :: (v, a) :: env) (nnrc_subst e2_2 x1 (NNRCVar x2))); try reflexivity.
        unfold lift in *; simpl in *.
        destruct (lift_map (fun d1 : data => nnrc_core_eval h cenv ((v, d1) :: (x1, d) :: env) e2_2)
                           l); destruct (lift_map (fun d1 : data => nnrc_core_eval h cenv ((v, d1) :: (x2, d) :: env) (nnrc_subst e2_2 x1 (NNRCVar x2)))
                                                  l); congruence.
    - Case "NNRCIf"%string.
      simpl in *.
      generalize (split_really_fresh_app2 x2 _ _ _ _ H1); clear H1; intros.
      elim H; clear H; intros.
      generalize (split_really_fresh_app2 x2 _ _ _ _ H1); clear H1; intros.
      elim H1; clear H1; intros.
      specialize (IHe2_1 H); specialize (IHe2_2 H1); specialize (IHe2_3 H2); clear H H1 H2.
      rewrite IHe2_1; rewrite IHe2_2; rewrite IHe2_3.
      reflexivity.
    - Case "NNRCEither"%string.
      simpl in H1.
      repeat rewrite nin_app_or in H1.
      destruct H1 as [_[[?[??]]?]].
      apply not_or in H3. destruct H3.
      apply not_or in H4. destruct H4.
      repeat rewrite nin_app_or in H5.
      destruct H5 as [?[??]].
      rewrite IHe2_1 by (simpl; intuition).
      rewrite <- remove_in_neq in H1,H2 by congruence.
      match_destr. match_destr.
      + match_destr; unfold equiv, complement in *; subst.
        * generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil x1 d0 nil); simpl;
            intros re1; rewrite re1.
          generalize (@nnrc_core_eval_remove_free_env _ h cenv ((x1,d0)::nil)); simpl;
            intros re2; rewrite re2 by trivial.
          trivial.
        * generalize (@nnrc_core_eval_swap_neq _ h cenv nil v d0); simpl;
            intros re1; repeat rewrite re1 by trivial.
          rewrite IHe2_2; trivial.
          simpl; intuition.
      + match_destr; unfold equiv, complement in *; subst.
        * generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil x1 d0 nil); simpl;
            intros re1; rewrite re1.
          generalize (@nnrc_core_eval_remove_free_env _ h cenv ((x1,d0)::nil)); simpl;
            intros re2; rewrite re2 by trivial.
          trivial.
        * generalize (@nnrc_core_eval_swap_neq _ h cenv nil v0 d0); simpl;
            intros re1; repeat rewrite re1 by trivial.
          rewrite IHe2_3; trivial.
          simpl; intuition.
    - Case "NNRCGroupBy"%string.
      reflexivity.
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
  Fixpoint use_count (x:var) (e:nnrc) : var_use :=
    match e with
    | NNRCGetConstant x' => NotUsed
    | NNRCVar x' => (if x == x' then UsedOnce else NotUsed)
    | NNRCConst _ => NotUsed
    | NNRCBinop _ e1 e2 =>
      use_sum (use_count x e1) (use_count x e2)
    | NNRCUnop _ e1 => use_count x e1
    | NNRCLet x' e1 e2 =>
      if (x == x') then use_count x e1
      else use_sum (use_count x e1) (use_count x e2)
    | NNRCFor x' e1 e2 =>
      use_exp (use_count x e1) (if x == x' then NotUsed else  (use_count x e2))
    | NNRCIf e1 e2 e3 =>
      use_sum (use_count x e1) (use_alt (use_count x e2) (use_count x e3))
    | NNRCEither ed xl el xr er =>
      use_sum
        (use_count x ed)
        (use_alt
           (if x == xl then NotUsed else use_count x el)
           (if x == xr then NotUsed else use_count x er))
    | NNRCGroupBy _ _ e1 => use_count x e1
    end.

  Lemma NotUsed_nfree v e :
    use_count v e = NotUsed <-> ~ In v (nnrc_free_vars e).
  Proof.
    induction e; simpl; trivial;
      repeat rewrite use_exp_not;
      repeat rewrite use_sum_not;
      repeat rewrite use_alt_not;
      repeat rewrite nin_app_or.
    - intuition.
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
  
  Lemma not_used_ignored {h:list(string*string)} {cenv}
        (d:data) (env:bindings) (v:var) (e:nnrc) :
    (use_count v e) = NotUsed ->
    nnrc_core_eval h cenv ((v,d)::env) e = nnrc_core_eval h cenv env e.
  Proof.
    rewrite NotUsed_nfree.
    generalize (@nnrc_core_eval_remove_free_env _ h cenv nil v d env); simpl; auto.
  Qed.

  Fixpoint nnrc_var_must_be_evaluated (e:nnrc) (x:var) : Prop :=
    match e with
    | NNRCGetConstant _ => False
    | NNRCVar v => v = x
    | NNRCConst _ => False
    | NNRCBinop _ e1 e2 =>
      nnrc_var_must_be_evaluated e1 x
      \/ nnrc_var_must_be_evaluated e2 x
    | NNRCUnop u e1 =>
      nnrc_var_must_be_evaluated e1 x
    | NNRCLet v e1 e2 =>
      nnrc_var_must_be_evaluated e1 x
      \/ (v <> x /\ nnrc_var_must_be_evaluated e2 x)
    | NNRCFor v e1 e2 =>
      nnrc_var_must_be_evaluated e1 x
    | NNRCIf e1 e2 e3 =>
      nnrc_var_must_be_evaluated e1 x
    | NNRCEither e1 v2 e2 v3 e3 =>
      nnrc_var_must_be_evaluated e1 x
    | NNRCGroupBy g sl e1 =>
      nnrc_var_must_be_evaluated e1 x
    end.

  Lemma nnrc_var_must_be_evaluated_dec (e:nnrc) (x:var) :
    { nnrc_var_must_be_evaluated e x} + {~  nnrc_var_must_be_evaluated e x}.
  Proof.
    induction e; simpl; eauto 3.
    - destruct (v == x); eauto.
    - destruct IHe1; [ tauto | ].
      destruct IHe2; [ eauto | ].
      right; tauto.
    - destruct IHe1; [ tauto | ].
      destruct (x == v); unfold equiv, complement in *.
      + right.
        subst; intuition.
      + destruct IHe2.
        * left.
          intuition.
        * right; intuition.
  Defined.

  Lemma nnrc_must_use_preserves_failure {h:brand_relation_t} cenv e1 x e2 env :
    disjoint (nnrc_bound_vars e2) (nnrc_free_vars e1) ->
    nnrc_var_must_be_evaluated e2 x ->
    @nnrc_eval _ h cenv env e1 = None ->
    @nnrc_eval _ h cenv env (nnrc_subst e2 x e1) = None.
  Proof.
    revert x env.
    induction e2; simpl; try tauto; intros x env disj me eve
    ; unfold nnrc_eval; simpl
    ; repeat rewrite <- nnrc_to_nnrc_base_eq.
    - match_destr; congruence.
    - rewrite disjoint_app_l in disj.
      destruct disj.
      destruct me.
      + rewrite IHe2_1; simpl; trivial.
      + rewrite IHe2_2; simpl; trivial.
        apply olift2_none_r.
    - rewrite IHe2; simpl; trivial.
    - apply disjoint_cons_inv1 in disj.
      rewrite disjoint_app_l in disj.
      destruct disj as [[??]?].
      destruct me as [me | [neq me]].
      + rewrite IHe2_1; simpl; trivial.
      + match_option.
        match_destr; [congruence | ].
        rewrite <- nnrc_to_nnrc_base_eq.
        apply IHe2_2; trivial.
        specialize (@nnrc_eval_remove_free_env fruntime h cenv nil v d env).
        simpl; intros re.
        rewrite re; trivial.
    - apply disjoint_cons_inv1 in disj.
      rewrite disjoint_app_l in disj.
      destruct disj as [[??]?].
      rewrite IHe2_1; trivial.
    - repeat rewrite disjoint_app_l in disj.
      destruct disj as [?[??]].
      rewrite IHe2_1; trivial.
    - apply disjoint_cons_inv1 in disj.
      destruct disj as [disj ?].
      apply disjoint_cons_inv1 in disj.
      repeat rewrite disjoint_app_l in disj.
      destruct disj as [[?[??]]?].
      rewrite IHe2_1; trivial.
    - rewrite IHe2; trivial.
  Qed.
  
  Lemma let_inline_disjoint_arrow_must_use x e1 e2 :
    disjoint (nnrc_bound_vars e2) (nnrc_free_vars e1) ->
    nnrc_var_must_be_evaluated e2 x ->
    nnrc_eq
      (NNRCLet x e1 e2)
      (nnrc_subst e2 x e1).
  Proof.
    red; simpl; intros.
    unfold nnrc_eval; simpl.
    repeat rewrite <- nnrc_to_nnrc_base_eq.
    match_option.
    - rewrite <- nnrc_to_nnrc_base_eq.
      apply nnrc_eval_cons_subst_disjoint; trivial.
    - rewrite nnrc_must_use_preserves_failure; trivial.
  Qed.
  
End NNRCRewriteUtil.

