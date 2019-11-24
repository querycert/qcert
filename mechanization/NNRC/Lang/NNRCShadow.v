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
Require Import Peano_dec.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNNRC.
Require Import cNNRCShadow.
Require Import NNRC.
Require Import NNRCSize.

Section NNRCShadow.
  Close Scope nnrc_scope.
  
  (* Since we are translating from a language with scoped variables
     (For) to a language without scoping, we need to alpha convert the input
     to ensure that there are no shadowed variable names.
   *)

  Context {fruntime:foreign_runtime}.

  Lemma nnrc_eval_remove_duplicate_env {h:brand_relation_t} {cenv} l v x l' x' l'' e :
    @nnrc_eval _ h cenv (l ++ (v,x)::l' ++ (v,x')::l'') e =
    @nnrc_eval _ h cenv (l ++ (v,x)::l' ++ l'') e.
  Proof.
    rewrite lookup_remove_duplicate; trivial.
  Qed.

  Lemma nnrc_eval_remove_duplicate_env_weak {h:list (string*string)} {cenv} v1 v2 x x' x'' l e :
    @nnrc_eval _ h cenv ((v1,x)::(v2,x')::(v1,x'')::l) e =
    @nnrc_eval _ h cenv ((v1,x)::(v2,x')::l) e.
  Proof.
    apply nnrc_eval_lookup_equiv_prop; trivial.
    red; intros; simpl.
    match_destr.
  Qed.

  Lemma nnrc_eval_remove_duplicate_env_weak_cons {h:list (string*string)} {cenv} v1 v2 x x' x'' l e :
    @nnrc_eval _ h cenv ((v1,x)::(v2,x')::(v2,x'')::l) e =
    @nnrc_eval _ h cenv ((v1,x)::(v2,x')::l) e.
  Proof.
    apply nnrc_eval_lookup_equiv_prop; trivial.
    red; intros; simpl.
    match_destr.
    match_destr.
  Qed.

  Lemma nnrc_eval_remove_free_env {h:list (string*string)} {cenv} l v x l' e :
          ~ In v (nnrc_free_vars e) ->
          @nnrc_eval _ h cenv (l ++ (v,x)::l') e = @nnrc_eval _ h cenv (l ++ l') e.
  Proof.
    revert l v x l'.
    induction e; simpl; intros; trivial; unfold nnrc_eval in *; simpl.
    - intuition. apply lookup_remove_nin; auto.
    - apply nin_app_or in H. rewrite IHe1, IHe2; intuition.
    - rewrite IHe; intuition.
    - apply nin_app_or in H. rewrite IHe1 by intuition.
      destruct (nnrc_core_eval h cenv (l ++ l') (nnrc_to_nnrc_base e1)); trivial. 
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst.
      + generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v0 d l); simpl; auto.
      + generalize (IHe2 ((v,d)::l)); simpl; intros rr; rewrite rr; intuition.
         elim H2. apply remove_in_neq; auto.
    - apply nin_app_or in H. rewrite IHe1 by intuition.
      destruct (nnrc_core_eval h cenv (l ++ l') (nnrc_to_nnrc_base e1)); trivial. destruct d; trivial.
      f_equal. apply lift_map_ext; intros.
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst.
      + generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v0 x0 l); simpl; auto.
      + generalize (IHe2 ((v,x0)::l)); simpl; intros rr; rewrite rr; intuition.
         elim H3. apply remove_in_neq; auto.
    - apply nin_app_or in H; destruct H as [? HH]; apply nin_app_or in HH.
      rewrite IHe1, IHe2, IHe3; intuition.
    - repeat rewrite nin_app_or in H.
      rewrite IHe1 by intuition.
      match_destr. destruct d; trivial.
      + destruct (string_eqdec v v1); unfold Equivalence.equiv in * .
        * subst. generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v1 d l).
          simpl; trivial.
        * generalize (IHe2 ((v,d)::l)); simpl; intros r.
          apply r.
          rewrite <- (remove_in_neq _ v1 v) in H by intuition.
          intuition.
      + destruct (string_eqdec v0 v1); unfold Equivalence.equiv in * .
        * subst. generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v1 d l).
          simpl; trivial.
        * generalize (IHe3 ((v0,d)::l)); simpl; intros r.
          apply r.
          rewrite <- (remove_in_neq _ v1 v0) in H by intuition.
          intuition.
    - rewrite IHe; intuition.
  Qed.

  Lemma nnrc_eval_remove_free_env_weak {h:list (string*string)} {cenv} v1 x1 v x e :
    ~ In v (nnrc_free_vars e) ->
    @nnrc_eval _ h cenv ((v1,x1)::(v,x)::nil) e = @nnrc_eval _ h cenv ((v1,x1)::nil) e.
  Proof.
    assert ((v1,x1)::(v,x)::nil =
            ((v1,x1)::nil) ++ (v,x)::nil).
    reflexivity.
    assert (((v1,x1)::nil) = ((v1,x1)::nil ++ nil)).
    reflexivity.
    rewrite H; rewrite H0.
    apply nnrc_eval_remove_free_env.
  Qed.

  Lemma nnrc_eval_swap_neq {h:list (string*string)} {cenv} l1 v1 x1 v2 x2 l2 e : v1 <> v2 ->
           @nnrc_eval _ h cenv (l1++(v1,x1)::(v2,x2)::l2) e = 
           @nnrc_eval _ h cenv (l1++(v2,x2)::(v1,x1)::l2) e.
  Proof.
    intros.
    rewrite lookup_swap_neq; trivial.
  Qed.

  Lemma nnrc_eval_subst_dunit {h:list (string*string)} {cenv} env e v :
    @nnrc_eval _ h cenv ((v,dunit)::env) e =
    @nnrc_eval _ h cenv env (nnrc_subst e v (NNRCConst dunit)).
  Proof.
    generalize env; clear env.
    nnrc_cases (induction e) Case; unfold nnrc_eval in *; simpl.
    - Case "NNRCGetConstant"%string.
      reflexivity.
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
      destruct (@nnrc_core_eval _ h cenv env (nnrc_to_nnrc_base
                                           (nnrc_subst e1 v (NNRCConst dunit))));
        try reflexivity.
      case (equiv_dec v0 v); unfold Equivalence.equiv in *.
      + SCase "v0 = v"%string.
        intros Hv; rewrite Hv in *; clear Hv.
        generalize (nnrc_core_eval_remove_duplicate_env (h:=h) cenv nil v d nil dunit env (nnrc_to_nnrc_base e2)); intros.
        simpl.
        trivial.
      + SCase "v0 <> v"%string.
        intros Hv.
        generalize (nnrc_core_eval_swap_neq (h:=h) cenv nil); simpl; intros eqq.
        rewrite eqq; auto.
    - Case "NNRCFor"%string.
      intros env.
      simpl.
      rewrite IHe1.
      destruct (@nnrc_core_eval _ h cenv env (nnrc_to_nnrc_base
                                       (nnrc_subst e1 v (NNRCConst dunit)))); try reflexivity.
      destruct d; try reflexivity.
      apply lift_dcoll_inversion.
      apply lift_map_ext.
      intros d Hd.
      match_destr; unfold Equivalence.equiv in * .
      + SCase "v0 = v"%string.
        subst.
        generalize (nnrc_core_eval_remove_duplicate_env
                      (h:=h) cenv nil v d nil dunit env (nnrc_to_nnrc_base e2)); simpl; trivial.
      + SCase "v0 <> v"%string.
        generalize (nnrc_core_eval_swap_neq (h:=h) cenv nil); simpl; intros eqq.
        rewrite eqq; auto.
    - Case "NNRCIf"%string.
      intros env.
      simpl.
      unfold olift.
      rewrite IHe1.
      destruct (@nnrc_core_eval _ h cenv env
                              (nnrc_to_nnrc_base (nnrc_subst e1 v (NNRCConst dunit))));
        try reflexivity.
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
      destruct (@nnrc_core_eval _ h cenv env
                                (nnrc_to_nnrc_base
                                   (nnrc_subst e1 v (NNRCConst dunit))));
        try reflexivity.
      destruct d; try reflexivity.
      + SCase "left"%string.
        match_destr; unfold Equivalence.equiv in * .
        * SSCase "v0 = v"%string.
          subst.
          generalize (nnrc_core_eval_remove_duplicate_env
                        (h:=h) cenv nil v d nil dunit env (nnrc_to_nnrc_base e2)).
          simpl; trivial.
        * SSCase "v0 <> v"%string.
          generalize (nnrc_core_eval_swap_neq (h:=h) cenv nil); simpl; intros eqq.
          rewrite eqq; auto.
      + SCase "right"%string.
        match_destr; unfold Equivalence.equiv in * .
        * SSCase "v0 = v"%string.
          subst.
          generalize (nnrc_core_eval_remove_duplicate_env
                        (h:=h) cenv nil v d nil dunit env (nnrc_to_nnrc_base e3)).
          simpl; trivial.
        * SSCase "v0 <> v"%string.
          generalize (nnrc_core_eval_swap_neq (h:=h) cenv nil); simpl; intros eqq.
          rewrite eqq; auto.
    - Case "NNRCGroupBy"%string.
      intros env.
      simpl.
      rewrite IHe.
      reflexivity.
  Qed.

  Lemma nnrc_eval_cons_subst {h:list (string*string)} {cenv} e env v x v' :
    ~ (In v' (nnrc_free_vars e)) ->
    ~ (In v' (nnrc_bound_vars e)) ->
    @nnrc_eval _ h cenv ((v',x)::env) (nnrc_subst e v (NNRCVar v')) = 
    @nnrc_eval _ h cenv ((v,x)::env) e.
  Proof.
    revert env v x v'.
    nnrc_cases (induction e) Case; simpl; unfold equiv_dec;
    trivial; intros; unfold nnrc_eval in *; simpl.
    - Case "NNRCVar"%string.
      intuition. destruct (string_eqdec v v0); simpl; subst; intuition.
      + match_destr; intuition; simpl; dest_eqdec; intuition.
      + match_destr; subst; simpl; dest_eqdec; intuition.
    - Case "NNRCBinop"%string.
      rewrite nin_app_or in H; f_equal; intuition.
    - Case "NNRCUnop"%string.
      f_equal; intuition.
    - Case "NNRCLet"%string.
      rewrite nin_app_or in H. rewrite IHe1 by intuition.
      case_eq (nnrc_core_eval h cenv ((v0, x) :: env) (nnrc_to_nnrc_base e1));
        trivial; intros d deq.
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst; simpl.
      + generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v0 d nil); 
        simpl; intros rr1; rewrite rr1.
        destruct (string_eqdec v0 v'); unfold Equivalence.equiv in *; subst.
        * generalize (@nnrc_eval_remove_duplicate_env h cenv nil v' d nil); 
          simpl; auto.
        * generalize (@nnrc_eval_remove_free_env h cenv ((v0,d)::nil)); 
          simpl; intros rr2; apply rr2. intuition.
          elim H3. apply remove_in_neq; auto.
      + destruct (string_eqdec v v'); unfold Equivalence.equiv in *; subst; [intuition | ].
        generalize (@nnrc_core_eval_swap_neq _ h cenv nil v d); simpl; intros rr2; 
        repeat rewrite rr2 by trivial.
        apply IHe2.
        * intros nin; intuition. elim H2; apply remove_in_neq; auto.
        * intuition.
    - Case "NNRCFor"%string.
      rewrite nin_app_or in H. rewrite IHe1 by intuition.
      case_eq (nnrc_core_eval h cenv ((v0, x) :: env) (nnrc_to_nnrc_base e1)); trivial; intros d deq.
      destruct d; trivial.
      f_equal.
      apply lift_map_ext; intros.
      destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst; simpl.
      + generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v0 x0 nil); 
        simpl; intros rr1; rewrite rr1.
        destruct (string_eqdec v0 v'); unfold Equivalence.equiv in *; subst.
        * generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v' x0 nil); 
          simpl; auto.
        * generalize (@nnrc_eval_remove_free_env h cenv ((v0,x0)::nil)); 
          simpl; intros rr2; apply rr2. intuition.
          elim H4. apply remove_in_neq; auto.
      + destruct (string_eqdec v v'); unfold Equivalence.equiv in *; subst; [intuition | ].
        generalize (@nnrc_core_eval_swap_neq _ h cenv nil v x0); simpl; intros rr2; 
        repeat rewrite rr2 by trivial.
        apply IHe2.
        * intros nin; intuition. elim H3; apply remove_in_neq; auto.
        * intuition.
    - Case "NNRCIf"%string.
      rewrite nin_app_or in H; destruct H as [? HH]; 
      rewrite nin_app_or in HH, H0.
      rewrite nin_app_or in H0.
      rewrite IHe1, IHe2, IHe3; intuition.
    - Case "NNRCEither"%string.
      apply not_or in H0; destruct H0 as [neq1 neq2].
      apply not_or in neq2; destruct neq2 as [neq2 neq3].
      repeat rewrite nin_app_or in neq3.
      repeat rewrite nin_app_or in H.
      rewrite IHe1 by intuition.
      repeat rewrite <- remove_in_neq in H by congruence.
      match_destr. destruct d; trivial.
      + match_destr; unfold Equivalence.equiv in *; subst.
        * generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v1 d nil); simpl;
          intros re2; rewrite re2 by trivial.
          generalize (@nnrc_core_eval_remove_free_env _ h cenv ((v1,d)::nil)); 
            simpl; intros re3. rewrite re3. intuition.
          rewrite <- nnrc_to_nnrc_base_free_vars_same. intuition.
        * generalize (@nnrc_core_eval_swap_neq _ h cenv nil v d); simpl;
          intros re1; repeat rewrite re1 by trivial.
          rewrite IHe2; intuition.
      +  match_destr; unfold Equivalence.equiv in *; subst.
         * generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v1 d nil); simpl;
           intros re2; rewrite re2 by trivial.
           generalize (@nnrc_core_eval_remove_free_env _ h cenv ((v1,d)::nil)); 
             simpl; intros re3. rewrite re3. intuition.
          rewrite <- nnrc_to_nnrc_base_free_vars_same. intuition.
         * generalize (@nnrc_core_eval_swap_neq _ h cenv nil v0 d); simpl;
           intros re1; repeat rewrite re1 by trivial.
           rewrite IHe3; intuition.
    - Case "NNRCGroupBy"%string.
      rewrite IHe; intuition.
  Qed.

  (* This relation is finer then the Proper relation already shown *)
  Lemma nnrc_eval_equiv_free_in_env {cenv} :
    forall n,
    forall env1 env2,
      (forall x, In x (nnrc_free_vars n) -> lookup equiv_dec env1 x = lookup equiv_dec env2 x) ->
      forall h,
        @nnrc_eval _ h cenv env1 n = @nnrc_eval _ h cenv env2 n.
  Proof.
    intros n.
    nnrc_cases (induction n) Case; intros env1 env2 Henv_eq h;
    unfold nnrc_eval in *; simpl.
    - Case "NNRCGetConstant"%string.
      reflexivity.
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
      destruct (@nnrc_core_eval _ h cenv env2 (nnrc_to_nnrc_base n1)); try congruence.
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
      destruct (@nnrc_core_eval _ h cenv env2 (nnrc_to_nnrc_base n1)); try reflexivity.
      destruct d; try reflexivity.
      unfold lift.
      assert (lift_map (fun d1 : data => @nnrc_core_eval _ h cenv ((v, d1) :: env1) (nnrc_to_nnrc_base n2)) l
              = lift_map (fun d1 : data => @nnrc_core_eval _ h cenv ((v, d1) :: env2) (nnrc_to_nnrc_base n2)) l) as Hfun_eq;
        try solve [rewrite Hfun_eq; reflexivity].
      apply lift_map_ext; intros d ind.
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
      destruct (@nnrc_core_eval _ h cenv env2 (nnrc_to_nnrc_base n1)); try reflexivity.
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
      destruct (@nnrc_core_eval _ h cenv env2 (nnrc_to_nnrc_base n1)); try reflexivity.
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
    - Case "NNRCGroupBy"%string.
      simpl.
      rewrite (IHn env1 env2).
      reflexivity.
      + intros x Hx.
        apply Henv_eq.
        simpl.
        assumption.
  Qed.

  Lemma nnrc_eval_equiv_env {cenv} :
    forall n,
    forall env1 env2,
      (forall x, lookup equiv_dec env1 x = lookup equiv_dec env2 x) ->
      forall h,
        @nnrc_eval _ h cenv env1 n = @nnrc_eval _ h cenv env2 n.
  Proof.
    intros.
    apply nnrc_eval_lookup_equiv_prop; trivial.
  Qed.

  Lemma nnrc_no_free_vars_eval_equiv_env {cenv} :
    forall n,
    forall env1 env2,
      nnrc_free_vars n = nil ->
      forall h,
        @nnrc_eval _ h cenv env1 n = @nnrc_eval _ h cenv env2 n.
  Proof.
    intros.
    apply nnrc_eval_equiv_free_in_env; intros.
    rewrite H in H0; simpl in H0.
    contradiction.
  Qed.

  Lemma nnrc_eval_single_context_var_uncons h cenv env n v d:
    lookup equiv_dec env v = Some d ->
    @nnrc_eval _ h cenv env n = @nnrc_eval _ h cenv ((v, d) :: env) n.
  Proof.
    intros.
    apply nnrc_eval_equiv_env.
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

  Lemma nnrc_eval_single_context_var h cenv env n v d:
    (forall x, In x (nnrc_free_vars n) -> x = v) ->
    lookup equiv_dec env v = Some d ->
    @nnrc_eval _ h cenv ((v, d) :: nil) n = @nnrc_eval _ h cenv env n.
  Proof.
    intros.
    rewrite (nnrc_eval_single_context_var_uncons h cenv env n v d); try assumption.
    clear H0.
    induction env; try reflexivity.
    destruct a.
    case (string_eqdec v0 v).
    * Case "v0 = v"%string.
      intros Hv; red in Hv; rewrite Hv in *; clear Hv.
      rewrite (nnrc_eval_remove_duplicate_env nil v d nil d0 env n).
      simpl. assumption.
    * Case "v0 <> v"%string.
      intros Hv.
      rewrite (nnrc_eval_remove_free_env ((v, d)::nil) v0 d0 env n); try solve [ simpl; reflexivity ].
      rewrite IHenv. reflexivity.
      specialize (H v0).
      unfold not.
      intros H'.
      assert (v0 = v); try congruence.
      apply H.
      exact H'.
  Qed.

  Lemma nnrc_eval_single_context_var_cons h cenv env n v d:
    (forall x, In x (nnrc_free_vars n) -> x = v) ->
    @nnrc_eval _ h cenv ((v, d) :: nil) n = @nnrc_eval _ h cenv ((v,d)::env) n.
  Proof.
    intros.
    apply nnrc_eval_single_context_var; try assumption.
    simpl.
    match_destr.
    congruence.
  Qed.

  Lemma nnrc_eval_single_context_var_cons_keepone h cenv env n v d v1 d1:
    (forall x, In x (nnrc_free_vars n) -> x = v) ->
    @nnrc_eval _ h cenv ((v, d) :: (v1, d1) :: nil) n =
    @nnrc_eval _ h cenv ((v,d) :: (v1,d1) :: env) n.
  Proof.
    intros.
    rewrite <- (nnrc_eval_single_context_var h cenv ((v,d) :: (v1,d1) :: nil) n v d); try assumption.
    - rewrite <- (nnrc_eval_single_context_var h cenv ((v,d) :: (v1,d1) :: env) n v d); try assumption; trivial.
      simpl; match_destr; congruence.
    - simpl; match_destr; congruence.
  Qed.

  Lemma nnrc_eval_single_context_var_two_cons h cenv env n v1 d1 v2 d2 :
    (forall x, In x (nnrc_free_vars n) -> x = v1 \/ x = v2) ->
    @nnrc_eval _ h cenv ((v1,d1) :: (v2,d2) :: nil) n =
    @nnrc_eval _ h cenv ((v1,d1) :: (v2,d2) :: env) n.
  Proof.
    intros.
    induction env; try reflexivity.
    destruct a.
    case (string_eqdec v1 v); intros.
    red in e; rewrite e in *; clear e.
    rewrite nnrc_eval_remove_duplicate_env_weak; assumption.
    case (string_eqdec v2 v); intros.
    red in e; rewrite e in *; clear e.
    rewrite nnrc_eval_remove_duplicate_env_weak_cons; assumption.
    rewrite (nnrc_eval_remove_free_env ((v1,d1)::(v2,d2)::nil) v d env n).
    assumption.
    specialize (H v).
    unfold not; intros.
    specialize (H H0).
    elim H; intros; congruence.
  Qed.

  Lemma nnrc_eval_single_context_var_cons_lift_map h cenv env n v l:
    (forall x, In x (nnrc_free_vars n) -> x = v) ->
    lift_map (fun d => @nnrc_eval _ h cenv ((v, d) :: nil) n) l =
    lift_map (fun d => @nnrc_eval _ h cenv ((v,d)::env) n) l.
  Proof.
    intros.
    induction l; simpl; try reflexivity.
    rewrite (nnrc_eval_single_context_var_cons h cenv env n v a); try assumption.
    destruct (@nnrc_eval _ h cenv ((v, a) :: env) n); try reflexivity.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma nnrc_eval_single_context_var_cons_keepone_lift_map h cenv env n v v1 d1 l:
    (forall x, In x (nnrc_free_vars n) -> x = v) ->
    lift_map (fun d => @nnrc_eval _ h cenv ((v, d) :: (v1,d1) :: nil) n) l =
    lift_map (fun d => @nnrc_eval _ h cenv ((v,d) :: (v1,d1) :: env) n) l.
  Proof.
    intros.
    induction l; simpl; try reflexivity.
    rewrite (nnrc_eval_single_context_var_cons_keepone h cenv env n v a v1 d1); try assumption.
    destruct (@nnrc_eval _ h cenv ((v, a) :: (v1,d1) :: env) n); try reflexivity.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma lift_map_skip_free_var h cenv v1 v2 d2 n l:
    ~ In v2 (nnrc_free_vars n) ->
    (lift_map (fun d : data => @nnrc_eval _ h cenv ((v1, d) :: (v2, d2) :: nil) n) l) =
    (lift_map (fun d : data => @nnrc_eval _ h cenv ((v1, d) :: nil) n) l).
  Proof.
    intros; induction l; try reflexivity; simpl.
    rewrite nnrc_eval_remove_free_env_weak.
    destruct (@nnrc_eval _ h cenv ((v1, a) :: nil) n); try reflexivity; rewrite IHl; reflexivity.
    auto.
  Qed.

  Lemma nnrc_eval_cons_subst_disjoint {h: list (string*string)} {cenv} e e' env v d :
    disjoint (nnrc_bound_vars e) (nnrc_free_vars e') ->
         @nnrc_eval _ h cenv env e' = Some d ->
         @nnrc_eval _ h cenv ((v,d)::env) e = @nnrc_eval _ h cenv env (nnrc_subst e v e').
  Proof.
    intros disj eval1.
    revert env e' v d disj eval1.
    nnrc_cases (induction e) Case; simpl in *;
      trivial; intros env e' v' d disj; simpl; intros eval1;
        unfold equiv_dec, olift2, olift in *;
    unfold nnrc_eval in *; simpl; unfold var in *; unfold equiv_dec in *.
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
        generalize (nnrc_core_eval_remove_duplicate_env (h:=h) cenv nil v' d0 nil d env (nnrc_to_nnrc_base e2));
          simpl; intros re1; rewrite re1; trivial.
      + erewrite <- IHe2; try reflexivity; eauto 2.
        * generalize (nnrc_core_eval_swap_neq (h:=h) cenv nil v d0 v' d); simpl;
          intros re1; rewrite re1; eauto.
        * generalize (nnrc_core_eval_remove_free_env (h:=h) cenv nil v d0 env);
          simpl; intros re1; rewrite re1; eauto.
          rewrite <- nnrc_to_nnrc_base_free_vars_same; auto.
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
        apply lift_map_ext; intros.
        generalize (nnrc_core_eval_remove_duplicate_env (h:=h) cenv nil v' x nil d env (nnrc_to_nnrc_base e2));
          simpl; congruence.
      + f_equal.
        apply lift_map_ext; intros.
        generalize (nnrc_core_eval_swap_neq (h:=h) cenv nil v x v' d); simpl;
          intros re1; rewrite re1; eauto 2.
        erewrite IHe2; try reflexivity; eauto 2.
        generalize (nnrc_core_eval_remove_free_env (h:=h) cenv nil v x env);
            simpl; intros re2; rewrite re2; eauto.
        rewrite <- nnrc_to_nnrc_base_free_vars_same; auto.
    - Case "NNRCIf"%string.
      apply disjoint_app_l in disj.
      destruct disj as [disj1 disj2].
      apply disjoint_app_l in disj2.
      destruct disj2 as [disj2 disj3].
      erewrite IHe1; eauto 2.
      destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base (nnrc_subst e1 v' e'))); try reflexivity;
      simpl.
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
      destruct (nnrc_core_eval h cenv env (nnrc_to_nnrc_base (nnrc_subst e1 v' e'))); try reflexivity;
      simpl.
      match_destr.
      + {
          match_destr.
          + red in e; subst.
            unfold var in *.
            generalize (nnrc_core_eval_remove_duplicate_env (h:=h) cenv nil v' d0 nil d env (nnrc_to_nnrc_base e2));
              simpl; intros re1; rewrite re1; trivial.
          + generalize (nnrc_core_eval_swap_neq (h:=h) cenv nil v d0 v' d); simpl;
                intros re1; rewrite re1; eauto 2.
            erewrite IHe2; try reflexivity; eauto 2.
            generalize (nnrc_core_eval_remove_free_env (h:=h) cenv nil v d0 env);
                simpl; intros re2; rewrite re2; trivial.
            rewrite <- nnrc_to_nnrc_base_free_vars_same; auto.
        } 
      + {
          match_destr.
          + red in e; subst.
            unfold var in *.
            generalize (nnrc_core_eval_remove_duplicate_env (h:=h) cenv nil v' d0 nil d env (nnrc_to_nnrc_base e3)); simpl; intros re1; rewrite re1; trivial.
          + generalize (nnrc_core_eval_swap_neq (h:=h) cenv nil v0 d0 v' d); simpl;
                intros re1; rewrite re1; eauto 2.
            erewrite IHe3; try reflexivity; eauto 2.
            generalize (nnrc_core_eval_remove_free_env (h:=h) cenv nil v0 d0 env);
                simpl; intros re2; rewrite re2; trivial.
            rewrite <- nnrc_to_nnrc_base_free_vars_same; auto.
        }
    - Case "NNRCGroupBy"%string.
      rewrite (IHe _ e').
      reflexivity.
      assumption.
      assumption.
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

  Lemma nnrc_eval_cons_rename_pick h cenv sep renamer avoid v e d env:
    @nnrc_eval _ h cenv ((nnrc_pick_name sep renamer avoid v e, d) :: env)
             (nnrc_rename_lazy e v (nnrc_pick_name sep renamer avoid v e)) = 
    @nnrc_eval _ h cenv ((v, d) :: env) e.
  Proof.
    unfold nnrc_rename_lazy.
    match_destr.
    - rewrite <- e0.
      trivial.
    - rewrite nnrc_eval_cons_subst; trivial.
      + apply nnrc_pick_name_neq_nfree; trivial.
      + apply nnrc_pick_name_bound.
  Qed.

  Theorem nnrc_unshadow_eval {h:list (string*string)} {cenv} sep renamer avoid e env :
    @nnrc_eval _ h cenv env (unshadow sep renamer avoid e) = @nnrc_eval _ h cenv env e.
  Proof.
    revert env.
    generalize nnrc_eval_cons_rename_pick; intros Hpick.
    induction e; unfold nnrc_eval in *; simpl;
    trivial; intros; try congruence.
    - rewrite IHe1.
      match_destr.
      rewrite Hpick.
      trivial.
    - rewrite IHe1.
      match_destr.
      match_destr.
      f_equal.
      apply lift_map_ext; intros.
      rewrite <- IHe2.
      apply Hpick.
    - rewrite IHe1, IHe2, IHe3; trivial.
    - rewrite IHe1.
      match_destr.
      match_destr.
      + rewrite Hpick.
        rewrite IHe2.
        trivial.
      + rewrite Hpick.
        rewrite IHe3.
        trivial.
    - rewrite IHe.
      reflexivity.
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

End NNRCShadow.

