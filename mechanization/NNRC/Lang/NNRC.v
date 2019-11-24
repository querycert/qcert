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

(** NNRC is the named nested relational calculus. It serves as an
intermediate language to facilitate code generation for non-functional
targets. *)

(** NNRC is a thin layer over the core language cNNRC. As cNNRC, NNRC
  is evaluated within a local environment. *)

(** Additional operators in NNRC can be easily expressed in terms of
  the core cNNRC, but are useful for optimization purposes. The main
  such operator is group-by. *)

(** Summary:
- Language: NNRC (Named Nested Relational Calculus)
- Based on: "Polymorphic type inference for the named nested
  relational calculus." Jan Van den Bussche, and Stijn
  Vansummeren. ACM Transactions on Computational Logic (TOCL) 9.1
  (2007): 3.
- translating to NNRC: NRAEnv, cNNRC
- translating from NNRC: cNNRC, NNRCMR, DNNRC, Java, JavaScript *)

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
Require Import cNNRCRuntime.

Section NNRC.
  Context {fruntime:foreign_runtime}.

  (** * Abstract Syntax *)
  
  (** The full abstract syntax for NNRC is already defined in core cNNRC. *)

  Definition nnrc := nnrc.

  (** * Macros *)
  
  (** All the additional operators are defined in terms of the core cNNRC. *)
  
  Section Macros.
    Context {h:brand_relation_t}.

    (** The following macro defines group-by in terms of existing cNNRC expressions. *)

    (** <<e groupby[g,keys] ==
         let $group0 := e
         in { $group2 × [ g: ♯flatten({ $group3 = π[keys] ? {$group3} {}
                            | $group3 ∈ $group0 }) ]
            | $group2 ∈ ♯distinct({ π[keys]($group1)
                                  | $group1 ∈ $group0 }) }>>
     *)

    Definition nnrc_group_by (g:string) (sl:list string) (e:nnrc) : nnrc :=
      let t0 := "$group0"%string in
      let t1 := "$group1"%string in
      let t2 := "$group2"%string in
      let t3 := "$group3"%string in
      NNRCLet
        t0 e
        (NNRCFor t2
                 (NNRCUnop OpDistinct
                           (NNRCFor t1 (NNRCVar t0) (NNRCUnop (OpRecProject sl) (NNRCVar t1))))
                 (NNRCBinop OpRecConcat
                            (NNRCVar t2)
                            (NNRCUnop (OpRec g)
                                      (NNRCUnop OpFlatten
                                                (NNRCFor t3 (NNRCVar t0)
                                                         (NNRCIf (NNRCBinop OpEqual
                                                                            (NNRCUnop (OpRecProject sl)
                                                                                      (NNRCVar t3))
                                                                            (NNRCVar t2))
                                                                 (NNRCUnop OpBag (NNRCVar t3))
                                                                 (NNRCConst (dcoll nil)))))))).

    (** This definition is equivalent to a nested evaluation group by algorithm. *)

    Lemma nnrc_group_by_correct cenv env
          (g:string) (sl:list string)
          (e:nnrc)
          (incoll:list data):
      nnrc_core_eval h cenv env e = Some (dcoll incoll) ->
      nnrc_core_eval h cenv env (nnrc_group_by g sl e) = lift dcoll (group_by_nested_eval_table g sl incoll).
    Proof.
      intros.
      rewrite <- (group_by_table_correct g sl incoll); simpl.
      rewrite H; trivial.
    Qed.
    
    Lemma nnrc_group_by_correct_some cenv env
          (g:string) (sl:list string)
          (e:nnrc)
          (incoll outcoll:list data):
      nnrc_core_eval h cenv env e = Some (dcoll incoll) ->
      group_by_nested_eval_table g sl incoll = Some outcoll -> 
      nnrc_core_eval h cenv env (nnrc_group_by g sl e) = Some (dcoll outcoll).
    Proof.
      intros.
      unfold nnrc_group_by; simpl.
      rewrite H; simpl; clear H.
      apply (group_by_table_correct_some g sl incoll outcoll H0).
    Qed.

    Lemma nnrc_group_by_correct_none cenv env
          (g:string) (sl:list string)
          (e:nnrc) :
      nnrc_core_eval h cenv env e = None ->
      nnrc_core_eval h cenv env (nnrc_group_by g sl e) = None.
    Proof.
      intros.
      unfold nnrc_group_by; simpl.
      rewrite H; simpl; clear H.
      trivial.
    Qed.

    Lemma nnrc_group_by_correct_some_ncoll cenv env
          (g:string) (sl:list string)
          (e:nnrc) d :
      (forall x, d <> dcoll x) ->
      nnrc_core_eval h cenv env e = Some d ->
      nnrc_core_eval h cenv env (nnrc_group_by g sl e) = None.
    Proof.
      intros.
      unfold nnrc_group_by; simpl.
      rewrite H0; simpl; clear H0.
      destruct d; simpl; trivial.
      eelim H; eauto.
    Qed.

  End Macros.

  (** * Evaluation Semantics *)

  Section Semantics.
    Context {h:brand_relation_t}.
    Context {cenv:bindings}.

    Fixpoint nnrc_to_nnrc_base (e:nnrc) : nnrc :=
      match e with
      | NNRCGetConstant v => NNRCGetConstant v
      | NNRCVar v => NNRCVar v
      | NNRCConst d => NNRCConst d
      | NNRCBinop b e1 e2 =>
        NNRCBinop b (nnrc_to_nnrc_base e1) (nnrc_to_nnrc_base e2)
      | NNRCUnop u e1 =>
        NNRCUnop u (nnrc_to_nnrc_base e1)
      | NNRCLet v e1 e2 =>
        NNRCLet v (nnrc_to_nnrc_base e1) (nnrc_to_nnrc_base e2)
      | NNRCFor v e1 e2 =>
        NNRCFor v (nnrc_to_nnrc_base e1) (nnrc_to_nnrc_base e2)
      | NNRCIf e1 e2 e3 =>
        NNRCIf (nnrc_to_nnrc_base e1) (nnrc_to_nnrc_base e2) (nnrc_to_nnrc_base e3)
      | NNRCEither e1 v2 e2 v3 e3 =>
        NNRCEither (nnrc_to_nnrc_base e1) v2 (nnrc_to_nnrc_base e2) v3 (nnrc_to_nnrc_base e3)
      | NNRCGroupBy g sl e1 =>
        nnrc_group_by g sl (nnrc_to_nnrc_base e1)
      end.

    Definition nnrc_eval (env:bindings) (e:nnrc) : option data :=
      nnrc_core_eval h cenv env (nnrc_to_nnrc_base e).

    Remark nnrc_to_nnrc_base_eq (e:nnrc):
      forall env,
        nnrc_eval env e = nnrc_core_eval h cenv env (nnrc_to_nnrc_base e).
    Proof.
      intros; reflexivity.
    Qed.

    (** Since we rely on cNNRC abstract syntax for the whole NNRC, it is important to check that translating to the core does not reuse the additional operations only present in NNRC. *)
    
    Lemma nnrc_to_nnrc_base_is_core (e:nnrc) :
      nnrcIsCore (nnrc_to_nnrc_base e).
    Proof.
      induction e; intros; simpl in *; auto.
      repeat (split; auto).
    Qed.

    (** The following function effectively returns an abstract syntax
    tree with the right type for cNNRC. *)
    
    Program Definition nnrc_to_nnrc_core (e:nnrc) : nnrc_core :=
      nnrc_to_nnrc_base e.
    Next Obligation.
      apply nnrc_to_nnrc_base_is_core.
    Defined.

    (** Additional properties of the translation from NNRC to cNNRC. *)
    
    Lemma core_nnrc_to_nnrc_ext_id (e:nnrc) :
      nnrcIsCore e ->
      (nnrc_to_nnrc_base e) = e.
    Proof.
      intros.
      induction e; simpl in *.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - elim H; intros.
        rewrite IHe1; auto; rewrite IHe2; auto.
      - rewrite IHe; auto.
      - elim H; intros.
        rewrite IHe1; auto; rewrite IHe2; auto.
      - elim H; intros.
        rewrite IHe1; auto; rewrite IHe2; auto.
      - elim H; intros.
        elim H1; intros.
        rewrite IHe1; auto; rewrite IHe2; auto; rewrite IHe3; auto.
      - elim H; intros.
        elim H1; intros.
        rewrite IHe1; auto; rewrite IHe2; auto; rewrite IHe3; auto.
      - contradiction. (* GroupBy case *)
    Qed.
    
    Lemma core_nnrc_to_nnrc_ext_idempotent (e1 e2:nnrc) :
      e1 = nnrc_to_nnrc_base e2 ->
      nnrc_to_nnrc_base e1 = e1.
    Proof.
      intros.
      apply core_nnrc_to_nnrc_ext_id.
      rewrite H.
      apply nnrc_to_nnrc_base_is_core.
    Qed.

    Corollary core_nnrc_to_nnrc_ext_idempotent_corr (e:nnrc) :
      nnrc_to_nnrc_base (nnrc_to_nnrc_base e) = (nnrc_to_nnrc_base e).
    Proof.
      apply (core_nnrc_to_nnrc_ext_idempotent _ e).
      reflexivity.
    Qed.

    Remark nnrc_to_nnrc_ext_eq (e:nnrc):
      nnrcIsCore e ->
      forall env,
        nnrc_core_eval h cenv env e = nnrc_eval env e.
    Proof.
      intros.
      unfold nnrc_eval.
      rewrite core_nnrc_to_nnrc_ext_id.
      reflexivity.
      assumption.
    Qed.
    
    (** we are only sensitive to the environment up to lookup *)
    Global Instance nnrc_eval_lookup_equiv_prop :
      Proper (lookup_equiv ==> eq ==> eq) nnrc_eval.
    Proof.
      generalize nnrc_core_eval_lookup_equiv_prop; intros.
      unfold Proper, respectful, lookup_equiv in *; intros; subst.
      unfold nnrc_eval.
      rewrite (H h cenv x y H0 (nnrc_to_nnrc_base y0) (nnrc_to_nnrc_base y0)).
      reflexivity.
      reflexivity.
    Qed.
    
  End Semantics.

  (** * Additional Properties *)

  (** Most of the following properties are useful for shadowing and variable substitution on the full NNRC. *)
  
  Section Properties.
    Context {h:brand_relation_t}.
    
    Lemma nnrc_to_nnrc_base_free_vars_same e:
      nnrc_free_vars e = nnrc_free_vars (nnrc_to_nnrc_base e).
    Proof.
      induction e; simpl; try reflexivity.
      - rewrite IHe1; rewrite IHe2; reflexivity.
      - assumption.
      - rewrite IHe1; rewrite IHe2; reflexivity.
      - rewrite IHe1; rewrite IHe2; reflexivity.
      - rewrite IHe1; rewrite IHe2; rewrite IHe3; reflexivity.
      - rewrite IHe1; rewrite IHe2; rewrite IHe3; reflexivity.
      - rewrite app_nil_r.
        assumption.
    Qed.

    Lemma nnrc_to_nnrc_base_bound_vars_impl x e:
      In x (nnrc_bound_vars e) -> In x (nnrc_bound_vars (nnrc_to_nnrc_base e)).
    Proof.
      induction e; simpl; unfold not in *; intros.
      - auto.
      - auto.
      - auto.
      - intuition.
        rewrite in_app_iff in H.
        rewrite in_app_iff.
        elim H; intros; auto.
      - intuition.
      - intuition.
        rewrite in_app_iff in H0.
        rewrite in_app_iff.
        elim H0; intros; auto.
      - intuition.
        rewrite in_app_iff in H0.
        rewrite in_app_iff.
        elim H0; intros; auto.
      - rewrite in_app_iff in H.
        rewrite in_app_iff in H.
        rewrite in_app_iff.
        rewrite in_app_iff.
        elim H; clear H; intros; auto.
        elim H; clear H; intros; auto.
      - rewrite in_app_iff in H.
        rewrite in_app_iff in H.
        rewrite in_app_iff.
        rewrite in_app_iff.
        elim H; clear H; intros; auto.
        elim H; clear H; intros; auto.
        elim H; clear H; intros; auto.
        elim H; clear H; intros; auto.
        right. right. auto.
        right. right. auto.
      - specialize (IHe H).
        right.
        rewrite in_app_iff.
        auto.
    Qed.

    Lemma nnrc_to_nnrc_base_bound_vars_impl_not x e:
      ~ In x (nnrc_bound_vars (nnrc_to_nnrc_base e)) -> ~ In x (nnrc_bound_vars e).
    Proof.
      unfold not.
      intros.
      apply H.
      apply nnrc_to_nnrc_base_bound_vars_impl.
      assumption.
    Qed.

    Definition really_fresh_in_ext sep oldvar avoid e :=
      really_fresh_in sep oldvar avoid (nnrc_to_nnrc_base e).
    
    Lemma really_fresh_from_free_ext sep old avoid (e:nnrc) :
      ~ In (really_fresh_in_ext sep old avoid e) (nnrc_free_vars (nnrc_to_nnrc_base e)).
    Proof.
      unfold really_fresh_in_ext.
      intros inn1.
      apply (really_fresh_in_fresh sep old avoid (nnrc_to_nnrc_base e)).
      repeat rewrite in_app_iff; intuition.
    Qed.

    Lemma nnrc_to_nnrc_base_subst_comm e1 v1 e2:
      nnrc_subst (nnrc_to_nnrc_base e1) v1 (nnrc_to_nnrc_base e2) =
      nnrc_to_nnrc_base (nnrc_subst e1 v1 e2).
    Proof.
      induction e1; simpl; try reflexivity.
      - destruct (equiv_dec v v1); reflexivity.
      - rewrite IHe1_1; rewrite IHe1_2; reflexivity.
      - rewrite IHe1; reflexivity.
      - rewrite IHe1_1.
        destruct (equiv_dec v v1); try reflexivity.
        rewrite IHe1_2; reflexivity.
      - rewrite IHe1_1.
        destruct (equiv_dec v v1); try reflexivity.
        rewrite IHe1_2; reflexivity.
      - rewrite IHe1_1; rewrite IHe1_2; rewrite IHe1_3; reflexivity.
      - rewrite IHe1_1.
        destruct (equiv_dec v v1);
          destruct (equiv_dec v0 v1);
          try reflexivity.
        rewrite IHe1_3; reflexivity.
        rewrite IHe1_2; reflexivity.
        rewrite IHe1_2; rewrite IHe1_3; reflexivity.
      - unfold nnrc_group_by.
        rewrite IHe1.
        unfold var in *.
        destruct (equiv_dec "$group0"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group1"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group2"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group3"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group2"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group3"%string v1); try congruence; try reflexivity.
    Qed.

    Lemma nnrc_to_nnrc_base_rename_lazy_comm e v1 v2:
      nnrc_rename_lazy (nnrc_to_nnrc_base e) v1 v2 =
      nnrc_to_nnrc_base (nnrc_rename_lazy e v1 v2).
    Proof.
      induction e; unfold nnrc_rename_lazy in *; simpl; try reflexivity.
      - destruct (equiv_dec v1 v2); reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        destruct (equiv_dec v v1); try reflexivity.
      - destruct (equiv_dec v1 v2); reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        simpl. rewrite <- IHe1; rewrite <- IHe2; reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        simpl. rewrite <- IHe; reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        rewrite IHe1.
        rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
        destruct (equiv_dec v v1); try reflexivity.
        rewrite <- IHe1; reflexivity.
        rewrite <- IHe1; rewrite <- IHe2; simpl; reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        rewrite IHe1.
        rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
        destruct (equiv_dec v v1); try reflexivity.
        rewrite <- IHe1; reflexivity.
        rewrite <- IHe1; rewrite <- IHe2; simpl; reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        simpl; rewrite <- IHe1; rewrite <- IHe2; rewrite <- IHe3.
        reflexivity.
      - destruct (equiv_dec v1 v2); try reflexivity.
        rewrite IHe1.
        destruct (equiv_dec v v1); try reflexivity.
        destruct (equiv_dec v0 v1); try reflexivity.
        rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
        rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
        rewrite <- IHe3.
        reflexivity.
        destruct (equiv_dec v0 v1); try reflexivity.
        rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
        rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
        rewrite <- IHe2.
        reflexivity.
        rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
        rewrite <- nnrc_to_nnrc_base_subst_comm; simpl.
        rewrite <- IHe2.
        rewrite <- IHe3.
        reflexivity.
      - simpl.
        unfold nnrc_group_by.
        destruct (equiv_dec v1 v2); try reflexivity.
        rewrite IHe.
        simpl; unfold nnrc_group_by.
        unfold var in *.
        destruct (equiv_dec "$group0"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group1"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group2"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group3"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group2"%string v1); try congruence; try reflexivity.
        destruct (equiv_dec "$group3"%string v1); try congruence; try reflexivity.
    Qed.

    (** Unshadow properties for the full NNRC. *)
    Lemma unshadow_over_nnrc_ext_idem sep renamer avoid e:
      (nnrc_to_nnrc_base (unshadow sep renamer avoid (nnrc_to_nnrc_base e))) =
      (unshadow sep renamer avoid (nnrc_to_nnrc_base e)).
    Proof.
      generalize (unshadow_preserve_core sep renamer avoid (nnrc_to_nnrc_base e)); intros.
      rewrite core_nnrc_to_nnrc_ext_id.
      reflexivity.
      apply H.
      apply nnrc_to_nnrc_base_is_core.
    Qed.

    Lemma nnrc_eval_cons_subst {cenv} e env v x v' :
      ~ (In v' (nnrc_free_vars e)) ->
      ~ (In v' (nnrc_bound_vars e)) ->
      @nnrc_eval h cenv ((v',x)::env) (nnrc_subst e v (NNRCVar v')) = 
      @nnrc_eval h cenv ((v,x)::env) e.
    Proof.
      revert env v x v'.
      nnrc_cases (induction e) Case; simpl; unfold equiv_dec;
        unfold nnrc_eval in *; unfold var in *; trivial; intros; simpl.
      - Case "NNRCVar"%string.
        intuition. destruct (string_eqdec v0 v); simpl; subst; intuition.
        + match_destr; intuition. simpl. dest_eqdec; intuition.
          destruct (equiv_dec v v); try congruence.
        + match_destr; subst; simpl; dest_eqdec; intuition.
          destruct (equiv_dec v v0); try congruence.
      - Case "NNRCBinop"%string.
        rewrite nin_app_or in H. f_equal; intuition.
      - f_equal; intuition.
      - rewrite nin_app_or in H. rewrite IHe1 by intuition.
        case_eq (nnrc_core_eval h cenv ((v0, x) :: env) (nnrc_to_nnrc_base e1)); trivial; intros d deq.
        destruct (string_eqdec v v0); unfold Equivalence.equiv in *; subst; simpl.
        + generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v0 d nil); 
            simpl; intros rr1; rewrite rr1.
          destruct (string_eqdec v0 v'); unfold Equivalence.equiv in *; subst.
          * generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v' d nil); 
              simpl; auto.
          * generalize (@nnrc_core_eval_remove_free_env _ h cenv ((v0,d)::nil)); 
              simpl; intros rr2; apply rr2. intuition.
            elim H3. apply remove_in_neq; auto.
            rewrite nnrc_to_nnrc_base_free_vars_same; auto.
        + destruct (string_eqdec v v'); unfold Equivalence.equiv in *; subst; [intuition | ].
          generalize (@nnrc_core_eval_swap_neq _ h cenv nil v d); simpl; intros rr2; 
            repeat rewrite rr2 by trivial.
          apply IHe2.
          * intros nin; intuition. elim H2; apply remove_in_neq; auto.
          * intuition.
      - rewrite nin_app_or in H. rewrite IHe1 by intuition.
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
          * generalize (@nnrc_core_eval_remove_free_env _ h cenv ((v0,x0)::nil)); 
              simpl; intros rr2; apply rr2. intuition.
            elim H4. apply remove_in_neq; auto.
            rewrite nnrc_to_nnrc_base_free_vars_same; auto.
        + destruct (string_eqdec v v'); unfold Equivalence.equiv in *; subst; [intuition | ].
          generalize (@nnrc_core_eval_swap_neq _ h cenv nil v x0); simpl; intros rr2; 
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
          * generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v1 d nil); simpl;
              intros re2; rewrite re2 by trivial.
            generalize (@nnrc_core_eval_remove_free_env _ h cenv ((v1,d)::nil)); 
              simpl; intros re3. rewrite re3. intuition.
            rewrite <- nnrc_to_nnrc_base_free_vars_same; intuition.
          * generalize (@nnrc_core_eval_swap_neq _ h cenv nil v d); simpl;
              intros re1; repeat rewrite re1 by trivial.
            rewrite IHe2; intuition.
        + match_destr; unfold Equivalence.equiv in *; subst.
          * generalize (@nnrc_core_eval_remove_duplicate_env _ h cenv nil v1 d nil); simpl;
              intros re2; rewrite re2 by trivial.
            generalize (@nnrc_core_eval_remove_free_env _ h cenv ((v1,d)::nil)); 
              simpl; intros re3. rewrite re3. intuition.
            rewrite <- nnrc_to_nnrc_base_free_vars_same; intuition.
          * generalize (@nnrc_core_eval_swap_neq _ h cenv nil v0 d); simpl;
              intros re1; repeat rewrite re1 by trivial.
            rewrite IHe3; intuition.
      - rewrite IHe; try assumption.
        reflexivity.
    Qed.

  End Properties.

  (** * Toplevel *)
  
  (** Top-level evaluation is used externally by the Q*cert
  compiler. It takes an NNRC expression and a global environment as
  input. *)

  Section Top.
    Context (h:brand_relation_t).
    Definition nnrc_eval_top (q:nnrc) (cenv:bindings) : option data :=
      @nnrc_eval h (rec_sort cenv) nil q.
  End Top.
  
End NNRC.

