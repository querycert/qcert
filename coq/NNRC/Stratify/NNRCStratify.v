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

(* NNRC is an expression oriented language.  
   We want to be able to compile it to statement oriented languages like
   nnrc_imp.  As an inbetween step, we can stratify the language, 
   separating expressions and statements.
 *)

Section Stratify.
  Require Import String.
  Require Import List.
  Require Import Bool.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Morphisms.
  Require Import Permutation.
  Require Import Eqdep_dec.
  Require Import Utils.
  Require Import CommonRuntime.
  Require Import cNNRC.
  Require Import NNRC.
  Require Import cNNRCNorm.
  Require Import cNNRCVars.

  
  Context {fruntime:foreign_runtime}.

  Section Stratified.
    
    Inductive nnrcKind :=
    | nnrcExpr
    | nnrcStmt.

    Global Instance nnrcKind_eqdec : EqDec nnrcKind eq.
    Proof.
      red.
      change (forall x y:nnrcKind, {x = y} + {x <> y}).
      decide equality.
    Defined.
    
    Inductive stratifiedLevel_spec : nnrcKind -> nnrc -> Prop
      :=
      | StratifiedGetConstant_level c : stratifiedLevel_spec nnrcExpr (NNRCGetConstant c)
      | StratifiedVar_level v : stratifiedLevel_spec nnrcExpr (NNRCVar v)
      | StratifiedConst_level c : stratifiedLevel_spec nnrcExpr (NNRCConst c)
      | StratifiedBinop_level b e1 e2 : 
          stratifiedLevel_spec nnrcExpr e1 ->
          stratifiedLevel_spec nnrcExpr e2 ->
          stratifiedLevel_spec nnrcExpr (NNRCBinop b e1 e2)
      | StratifiedUnop_level u e :
          stratifiedLevel_spec nnrcExpr e ->
          stratifiedLevel_spec nnrcExpr (NNRCUnop u e)
      | StratifiedLet_level v s1 s2 :
          stratifiedLevel_spec nnrcStmt s1 ->
          stratifiedLevel_spec nnrcStmt s2 ->
          stratifiedLevel_spec nnrcStmt (NNRCLet v s1 s2)
      | StratifiedFor_level v e s :
          stratifiedLevel_spec nnrcExpr e ->
          stratifiedLevel_spec nnrcStmt s ->
          stratifiedLevel_spec nnrcStmt (NNRCFor v e s)
      | StratifiedIf_level e s1 s2 :
          stratifiedLevel_spec nnrcExpr e ->
          stratifiedLevel_spec nnrcStmt s1 ->
          stratifiedLevel_spec nnrcStmt s2 ->
          stratifiedLevel_spec nnrcStmt (NNRCIf e s1 s2)
      | StratifiedEither_level e x1 s1 x2 s2 :
          stratifiedLevel_spec nnrcExpr e ->
          stratifiedLevel_spec nnrcStmt s1 ->
          stratifiedLevel_spec nnrcStmt s2 ->
          stratifiedLevel_spec nnrcStmt (NNRCEither e x1 s1 x2 s2)
      | StratifiedGroupBy_level s ls e :
          stratifiedLevel_spec nnrcExpr e ->
          stratifiedLevel_spec nnrcStmt (NNRCGroupBy s ls e)
      | StratifiedLift_level e : stratifiedLevel_spec nnrcExpr e -> stratifiedLevel_spec nnrcStmt e
    .

    Fixpoint stratifiedLevel (kind:nnrcKind) (e:nnrc) : Prop
      := match e with
         | NNRCGetConstant _ => True
         | NNRCVar _ => True
         | NNRCConst _ => True
         | NNRCBinop _ e1 e2 =>
           stratifiedLevel nnrcExpr e1
           /\ stratifiedLevel nnrcExpr e2
         | NNRCUnop _ e1 => stratifiedLevel nnrcExpr e1
         | NNRCLet _ e1 e2 =>
           kind = nnrcStmt
           /\ stratifiedLevel nnrcStmt e1
           /\ stratifiedLevel nnrcStmt e2
         | NNRCFor _ e1 e2 =>
           kind = nnrcStmt
           /\ stratifiedLevel nnrcExpr e1
           /\ stratifiedLevel nnrcStmt e2
         | NNRCIf e1 e2 e3 =>
           kind = nnrcStmt
           /\ stratifiedLevel nnrcExpr e1
           /\ stratifiedLevel nnrcStmt e2
           /\ stratifiedLevel nnrcStmt e3
         | NNRCEither e1 _ e2 _ e3 =>
           kind = nnrcStmt
           /\ stratifiedLevel nnrcExpr e1
           /\ stratifiedLevel nnrcStmt e2
           /\ stratifiedLevel nnrcStmt e3
         | NNRCGroupBy _ _ e =>
           kind = nnrcStmt
           /\ stratifiedLevel nnrcExpr e
         end.

    Definition stratified := stratifiedLevel nnrcStmt.
    Definition stratified_spec := stratifiedLevel_spec nnrcStmt.

    Lemma stratifiedLevel_lift k e :
      stratifiedLevel k e -> stratifiedLevel nnrcStmt e.
    Proof.
      revert k.
      induction e; destruct k; simpl; intuition discriminate.
    Qed.

    Lemma stratifiedLevel_stratified k (e:nnrc) :
      stratifiedLevel k e -> stratified e.
    Proof.
      unfold stratified; intros.
      eapply stratifiedLevel_lift; eauto.
    Qed.

    Lemma stratifiedLevel_spec_lifts k e :
      stratifiedLevel_spec k e -> stratifiedLevel_spec nnrcStmt e.
    Proof.
      Hint Constructors stratifiedLevel_spec.
      destruct k; eauto.
    Qed.

    Lemma stratifiedLevel_spec_lifte k e :
      stratifiedLevel_spec nnrcExpr e -> stratifiedLevel_spec k e.
    Proof.
      Hint Constructors stratifiedLevel_spec.
      destruct k; eauto.
    Qed.

    Lemma stratifiedLevel_spec_stratified k (e:nnrc) :
      stratifiedLevel_spec k e -> stratified_spec e.
    Proof.
      unfold stratified; intros.
      eapply stratifiedLevel_spec_lifts; eauto.
    Qed.

    Lemma stratifiedLevel_correct k e:
      stratifiedLevel k e <-> stratifiedLevel_spec k e.
    Proof.
      Hint Constructors stratifiedLevel_spec.
      Hint Resolve stratifiedLevel_spec_lifts stratifiedLevel_spec_lifte.
      split; revert k.
      - induction e; simpl; destruct k; simpl; intros; intuition (eauto; try discriminate).
      - induction e; simpl; intros k; intros HH; invcs HH; simpl; eauto 3;
          try (invcs H; eauto); intuition eauto.
    Qed.

    Corollary stratified_correct e:
      stratified e <-> stratified_spec e.
    Proof.
      apply stratifiedLevel_correct.
    Qed.

    Section dec.
      Lemma stratifiedLevel_dec k (e:nnrc):
        {stratifiedLevel k e} + {~ stratifiedLevel k e}.
    Proof.
      revert k.
      induction e; intros k; simpl; try tauto;
        repeat apply sumbool_and; try auto 2; try tauto
        ; try solve [
                apply nnrcKind_eqdec
              |  apply eqdec_neq].
    Defined.

    Lemma stratifiedLevel_spec_dec k (e:nnrc):
      {stratifiedLevel_spec k e} + {~ stratifiedLevel_spec k e}.
    Proof.
      destruct (stratifiedLevel_dec k e);
        [left|right]; rewrite <- stratifiedLevel_correct; trivial.
    Defined.

    Theorem stratified_dec (e:nnrc) :
      {stratified e} + {~ stratified e}.
    Proof.
      apply stratifiedLevel_dec.
    Defined.

    Theorem stratified_spec_dec (e:nnrc) :
      {stratified_spec e} + {~ stratified_spec e}.
    Proof.
      apply stratifiedLevel_spec_dec.
    Defined.

    End dec.

  End Stratified.
  
  (* given an nnrc expression that may not be an expression, adds 
      a let binding and turns it into a variable if the context demands an expression 
   *)

  Section stratify.

    Definition nnrc_with_substs : Type := nnrc*list (var*nnrc).

    Definition mk_expr_from_vars (nws:nnrc_with_substs)
      := fold_right (fun sdef accum => NNRCLet (fst sdef) (snd sdef) accum) (fst nws) (snd nws).

    Lemma mk_expr_from_vars_eq e sdefs :
      fold_right (fun sdef accum => NNRCLet (fst sdef) (snd sdef) accum) e sdefs = mk_expr_from_vars (e, sdefs).
    Proof.
      reflexivity.
    Qed.
    
    Definition stratify1_aux
               (body:nnrc)
               (required_kind:nnrcKind)
               (bound_vars:list var)
               (sdefs:list (var*nnrc))
      : nnrc_with_substs
      := match required_kind with
         | nnrcExpr =>
           let fvar := fresh_var "stratify" bound_vars in
           (NNRCVar fvar, sdefs++((fvar, body)::nil))
         | _ => (body, sdefs)
         end.

    Fixpoint stratify_aux (e: nnrc) (required_kind:nnrcKind) (bound_vars:list var): nnrc_with_substs
      := match e with
         | NNRCGetConstant c => (e, nil)
         | NNRCVar _ => (e, nil)
         | NNRCConst _ => (e, nil)
         | NNRCBinop b e1 e2 =>
           let (e1', sdefs1) := stratify_aux e1 nnrcExpr bound_vars in
           let bound_vars2 := (domain sdefs1) ++ bound_vars in 
           let (e2', sdefs2) := stratify_aux e2 nnrcExpr (bound_vars2) in
           ((NNRCBinop b e1' e2'), sdefs1++sdefs2)
         | NNRCUnop u e1 =>
           let (e1', sdefs1) := stratify_aux e1 nnrcExpr bound_vars in
           ((NNRCUnop u e1'), sdefs1)
         | NNRCLet x e1 e2 =>
           let e1'ws := stratify_aux e1 nnrcStmt bound_vars in
           let e1' := mk_expr_from_vars e1'ws in
           let e2'ws := stratify_aux e2 nnrcStmt (x::bound_vars) in
           let e2' := mk_expr_from_vars e2'ws in
           stratify1_aux (NNRCLet x e1' e2') required_kind bound_vars nil
         | NNRCFor x e1 e2 =>
           let (e1', sdefs1) := stratify_aux e1 nnrcExpr bound_vars in
           let bound_vars2 := (domain sdefs1) ++ x::bound_vars in
           let e2'ws := stratify_aux e2 nnrcStmt (x::bound_vars) in
           let e2' := mk_expr_from_vars e2'ws in
           stratify1_aux (NNRCFor x e1' e2') required_kind bound_vars2 sdefs1
         | NNRCIf e1 e2 e3 => 
           let (e1', sdefs1) := stratify_aux e1 nnrcExpr bound_vars in
           let bound_vars2 := (domain sdefs1) ++ bound_vars in
           let e2'ws := stratify_aux e2 nnrcStmt bound_vars in
           let e2' := mk_expr_from_vars e2'ws in
           let e3'ws := stratify_aux e3 nnrcStmt bound_vars in
           let e3' := mk_expr_from_vars e3'ws in
           stratify1_aux (NNRCIf e1' e2' e3') required_kind bound_vars2 sdefs1
         | NNRCEither e1 x2 e2 x3 e3 => 
           let (e1', sdefs1) := stratify_aux e1 nnrcExpr bound_vars in
           let bound_vars2 := (domain sdefs1) ++ bound_vars in
           let e2'ws := stratify_aux e2 nnrcStmt (x2::bound_vars) in
           let e2' := mk_expr_from_vars e2'ws in
           let e3'ws := stratify_aux e3 nnrcStmt (x3::bound_vars) in
           let e3' := mk_expr_from_vars e3'ws in
           stratify1_aux (NNRCEither e1' x2 e2' x3 e3') required_kind (x2::x3::bound_vars2) sdefs1
         | NNRCGroupBy s ls e1 =>
           let (e1', sdefs1) := stratify_aux e1 nnrcExpr bound_vars in
           stratify1_aux (NNRCGroupBy s ls e1') required_kind bound_vars sdefs1
         end.

    Definition stratify (e: nnrc) : nnrc
      := mk_expr_from_vars (stratify_aux e nnrcStmt (nnrc_free_vars e)).

  End stratify.
  Section tests.
    Local Open Scope nnrc_scope.
    Local Open Scope string_scope.

    Example nnrc1 := (‵abs ‵ (dnat 3) ‵+ ‵(dnat 5)) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3)).
(*    Eval vm_compute in (stratify nnrc1). *)

    Example nnrc2 := NNRCLet "x" nnrc1 (NNRCVar "x").
(*    Eval vm_compute in (stratify nnrc2). *)

    Example nnrc3 := (‵abs (NNRCLet "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8)))) ‵+ ‵(dnat 5)) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))).
(*    Eval vm_compute in (stratify nnrc3). *)

    Example nnrc4 := (‵abs (NNRCFor "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8)))) ‵+ ‵(dnat 5)) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))).
(*    Eval vm_compute in (stratify nnrc4). *)

    Example nnrc5 := (‵abs (NNRCLet "z" (NNRCFor "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8)))) ‵+ ‵(dnat 5)) (NNRCVar "z")) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))).
(*    Eval vm_compute in (stratify nnrc5). *)

    Example nnrc6 := (‵abs (NNRCLet "z" (NNRCFor "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8))))) (NNRCVar "z")) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))).
(*    Eval vm_compute in (stratify nnrc6). *)

    Example nnrc7 := NNRCLet "x" (NNRCLet "y" ‵(dnat 3) (‵(dnat 8) ‵+ (NNRCVar "y"))) (NNRCVar "x").
    
(*    Eval vm_compute in (stratify nnrc7). *)

    Example nnrc8 := NNRCLet "x" (NNRCLet "x" ‵(dnat 3) (‵(dnat 8) ‵+ (NNRCVar "x"))) (NNRCVar "x").
    
(*    Eval vm_compute in (stratify nnrc8). *)

  End tests.

  Section aux.
    
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

        Require Import NNRCEq.
    Require Import NNRCShadow.

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

    Lemma incl_app_iff {A:Type} (l m n : list A) :
      incl l n /\ incl m n <-> incl (l ++ m) n.
    Proof.
      unfold incl; intuition.
      rewrite in_app_iff in H.
      intuition.
    Qed.

    Lemma disjoint_with_exclusion {A:Type} (l l1 l2:list A) :
      disjoint l1 l2 ->
      (forall x,
          In x l -> In x (l1 ++ l2) -> In x l1) ->
      disjoint l l2.
    Proof.
      unfold disjoint; intros disj excl x inn1 inn2.
      specialize (excl x inn1).
      rewrite in_app_iff in excl.
      intuition; eauto.
    Qed.
  
    Lemma codomain_length  {A B:Type} (l:list (A*B)) :
      length (codomain l) = length l.
    Proof.
      apply map_length.
    Qed.
    
    Lemma codomain_app {A B:Type} (l₁ l₂:list (A*B)) :
      codomain (l₁ ++ l₂) = codomain l₁ ++ codomain l₂.
    Proof.
      unfold codomain. rewrite map_app; trivial.
    Qed.

    Lemma app_inv_self {A:Type} (l l2:list A) :
      l = l ++ l2 -> l2 = nil.
    Proof.
      intros eqq1.
      assert (eqq2:l ++ nil = l ++ l2) by (rewrite app_nil_r; trivial).
      apply app_inv_head in eqq2.
      congruence.
    Qed.
  End aux.


    Ltac list_simpler :=
      repeat progress (
      try match goal with
      | [H: ?l  = ?l ++ _ |- _ ] => apply app_inv_self in H; try subst
      | [H: ?l ++ _ = ?l ++ _ |- _ ] => apply app_inv_head in H; try subst
      | [H: In _ (remove _ _ _) |- _] => apply remove_inv in H; destruct H
      | [H: ?a <> ?v |- context [In ?a (remove _ ?v _)]] => rewrite <- (remove_in_neq _ _ _ H)
      | [H: ?v <> ?a |- context [In ?a (remove _ ?v _)]] => rewrite <- (remove_in_neq _ a v ) by congruence
      | [H: ?a = ?v -> False |- context [In ?a (remove _ ?v _)]] => rewrite <- (remove_in_neq _ _ _ H)
      | [H: ?v = ?a -> False |- context [In ?a (remove _ ?v _)]] => rewrite <- (remove_in_neq _ a v) by congruence
      end
      ; repeat rewrite domain_app in *
      ; repeat rewrite codomain_app in *
      ; repeat rewrite map_app in *
      ; repeat rewrite concat_app in *
      ; repeat rewrite in_app_iff in *).
      
  Section Effective.

    Lemma stratify1_aux_stratified {body required_level bv sdefs1 n sdefs2} :
      stratify1_aux body required_level bv sdefs1 = (n,sdefs2) ->
      stratifiedLevel nnrcStmt body ->
      Forall (stratifiedLevel nnrcStmt) (codomain sdefs1) ->
      stratifiedLevel required_level n /\
      Forall (stratifiedLevel nnrcStmt) (codomain sdefs2).
    Proof.
      unfold stratified, stratify1_aux.
      destruct required_level; simpl; intros eqq; invcs eqq; simpl; intuition.
      rewrite codomain_app; simpl.
      apply Forall_app; intuition.
    Qed.

    Lemma mk_expr_from_vars_stratified {e sdefs} :
      stratifiedLevel nnrcStmt e ->
      Forall (stratifiedLevel nnrcStmt) (codomain sdefs) ->
      stratifiedLevel nnrcStmt (mk_expr_from_vars (e, sdefs)).
    Proof.
      unfold mk_expr_from_vars.
      revert e; induction sdefs; intros e ste stf; simpl in *; trivial.
      invcs stf.
      intuition.
    Qed.
    
    Lemma stratify_aux_stratified {e required_level bound_vars n sdefs} :
      stratify_aux e required_level bound_vars = (n, sdefs) ->
      stratifiedLevel required_level n /\
      Forall (stratifiedLevel nnrcStmt) (codomain sdefs).
    Proof.
      Hint Resolve Forall_nil Forall_app.
      revert required_level bound_vars n sdefs.
      induction e; intros required_level bound_vars n sdefs eqq
      ; invcs eqq; simpl in *; eauto 2; simpl.
      - match_case_in H0;  intros ? ? eqq1; rewrite eqq1 in *.
        match_case_in H0; intros ? ? eqq2; rewrite eqq2 in *; simpl in *.
        invcs H0; simpl in *.
        rewrite codomain_app.
        destruct (IHe1 _ _ _ _ eqq1).
        destruct (IHe2 _ _ _ _ eqq2).
        intuition eauto.
      - match_case_in H0;  intros ? ? eqq1; rewrite eqq1 in *; simpl in *.
        invcs H0; simpl in *.
        destruct (IHe _ _ _ _ eqq1).
        intuition eauto.
      - apply (stratify1_aux_stratified H0); simpl; eauto 2.
        intuition.
        + case_eq (stratify_aux e1 nnrcStmt bound_vars); intros ? ? eqq1.
          destruct (IHe1 _ _ _ _ eqq1); simpl in *.
          apply mk_expr_from_vars_stratified; intuition.
        + case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2.
          destruct (IHe2 _ _ _ _ eqq2); simpl in *.
          apply mk_expr_from_vars_stratified; intuition.
      - match_case_in H0;  intros ? ? eqq1; rewrite eqq1 in *; simpl in *.
        destruct (IHe1 _ _ _ _ eqq1).
        apply (stratify1_aux_stratified H0); simpl; eauto 2.
        intuition.
        case_eq ( (stratify_aux e2 nnrcStmt (v::bound_vars))); intros ? ? eqq2.
        destruct (IHe2 _ _ _ _ eqq2).
        apply mk_expr_from_vars_stratified; intuition.
      - match_case_in H0;  intros ? ? eqq1; rewrite eqq1 in *; simpl in *.
        destruct (IHe1 _ _ _ _ eqq1).
        apply (stratify1_aux_stratified H0); simpl; eauto 2.
        intuition.
        + case_eq ( (stratify_aux e2 nnrcStmt bound_vars)); intros ? ? eqq2.
          destruct (IHe2 _ _ _ _ eqq2).
          apply mk_expr_from_vars_stratified; intuition.
        + case_eq ( (stratify_aux e3 nnrcStmt bound_vars)); intros ? ? eqq3.
          destruct (IHe3 _ _ _ _ eqq3).
          apply mk_expr_from_vars_stratified; intuition.
      - match_case_in H0;  intros ? ? eqq1; rewrite eqq1 in *; simpl in *.
        destruct (IHe1 _ _ _ _ eqq1).
        apply (stratify1_aux_stratified H0); simpl; eauto 2.
        intuition.
        + case_eq ( (stratify_aux e2 nnrcStmt (v::bound_vars))); intros ? ? eqq2.
          destruct (IHe2 _ _ _ _ eqq2).
          apply mk_expr_from_vars_stratified; intuition.
        + case_eq ( (stratify_aux e3 nnrcStmt (v0::bound_vars))); intros ? ? eqq3.
          destruct (IHe3 _ _ _ _ eqq3).
          apply mk_expr_from_vars_stratified; intuition.
      - match_case_in H0;  intros ? ? eqq1; rewrite eqq1 in *; simpl in *.
        invcs H0; simpl in *.
        destruct (IHe _ _ _ _ eqq1).
        apply (stratify1_aux_stratified H1); simpl; eauto 2.
      Qed.

    Theorem stratify_stratified (e: nnrc) : stratified (stratify e).
    Proof.
      unfold stratify.
      case_eq (stratify_aux e nnrcStmt (nnrc_free_vars e)); intros ? ? eqq1.
      destruct (stratify_aux_stratified eqq1).
      apply mk_expr_from_vars_stratified; simpl; eauto.
    Qed.

    Corollary stratify_stratified_spec (e: nnrc) : stratified_spec (stratify e).
    Proof.
      apply stratified_correct.
      apply stratify_stratified.
    Qed.

  End Effective.

  Section Idempotent.

    Lemma mk_expr_from_vars_nil e : 
      mk_expr_from_vars (e, nil) = e.
    Proof.
      reflexivity.
    Qed.
    
    Lemma stratify_aux_stratify_id
          (e: nnrc)
          (required_level:nnrcKind)
          (bound_vars:list var) :
      stratifiedLevel required_level e -> 
      stratify_aux e required_level bound_vars = (e, nil).
    Proof.
      revert required_level bound_vars.
      induction e; intros required_level bound_vars stratify_levelc; simpl in *; trivial.
      - rewrite IHe1, IHe2 by tauto.
        simpl; trivial.
      - rewrite IHe by tauto.
        simpl; trivial.
      - rewrite IHe1, IHe2 by tauto; simpl.
        repeat rewrite mk_expr_from_vars_nil.
        intuition; subst; simpl; trivial.
      - rewrite IHe1, IHe2 by tauto; simpl.
        repeat rewrite mk_expr_from_vars_nil.
        intuition; subst; simpl; trivial.
      - rewrite IHe1, IHe2, IHe3 by tauto; simpl.
        repeat rewrite mk_expr_from_vars_nil.
        intuition; subst; simpl; trivial.
      - rewrite IHe1, IHe2, IHe3 by tauto; simpl.
        repeat rewrite mk_expr_from_vars_nil.
        intuition; subst; simpl; trivial.
      - rewrite IHe by tauto.
        intuition; subst; simpl; trivial.
    Qed.

    Theorem stratify_stratify_id (e: nnrc) :
      stratified e ->              
      stratify e = e.
    Proof.
      unfold stratify.
      intros stratifye.
      rewrite (stratify_aux_stratify_id _ _ _ stratifye).
      rewrite mk_expr_from_vars_nil.
      trivial.
    Qed.

    Corollary stratify_idem (e: nnrc) :
      stratify (stratify e) = stratify e.
    Proof.
      apply stratify_stratify_id.
      apply stratify_stratified.
    Qed.

  End Idempotent.

  Section BoundVars.

    Lemma stratify1_aux_nbound_vars {e required_kind bound_vars n l sdefs} :
      stratify1_aux e required_kind bound_vars sdefs = (n,l) ->
      forall x, In x (domain l) -> In x bound_vars -> In x (domain sdefs).
    Proof.
      destruct required_kind; simpl; trivial; intros eqq ? inn; invcs eqq; trivial.
      intros.
      rewrite domain_app, in_app_iff in inn.
      destruct inn; trivial.
      - simpl in *.
        destruct H0; try tauto.
        subst.
        apply fresh_var_fresh in H.
        tauto.
    Qed.

    Lemma stratify_aux_nbound_vars {e required_kind bound_vars n sdefs} :
      stratify_aux e required_kind bound_vars = (n,sdefs) ->
      disjoint (domain sdefs) bound_vars.
    Proof.
      revert required_kind bound_vars sdefs n; induction e; intros required_kind bound_vars sdefs n eqq; simpl in eqq; invcs eqq; simpl
      ; try apply disjoint_nil_l.
      - match_case_in H0; intros ? ? eqq1
        ; rewrite eqq1 in H0.
         match_case_in H0; intros ? ? eqq2
         ; rewrite eqq2 in H0.
         invcs H0.
         rewrite domain_app, disjoint_app_l.
         split; eauto.
         specialize (IHe2 _ _ _ _ eqq2).
         rewrite disjoint_app_r in IHe2.
         intuition.
      -  match_case_in H0; intros ? ? eqq1
         ; rewrite eqq1 in H0.
         invcs H0.
         eauto.
      - specialize (stratify1_aux_nbound_vars H0); intros HH.
        eauto.
      - match_case_in H0; intros ? ? eqq1
        ; rewrite eqq1 in H0.
        specialize (IHe1 _ _ _ _ eqq1).
        specialize (stratify1_aux_nbound_vars H0); intros HH.
        eapply disjoint_with_exclusion; eauto.
        intuition; list_simpler; intuition.
      - match_case_in H0; intros ? ? eqq1
        ; rewrite eqq1 in H0.
        specialize (IHe1 _ _ _ _ eqq1).
        specialize (stratify1_aux_nbound_vars H0); intros HH.
        eapply disjoint_with_exclusion; eauto.
      - match_case_in H0; intros ? ? eqq1
        ; rewrite eqq1 in H0.
        specialize (IHe1 _ _ _ _ eqq1).
        specialize (stratify1_aux_nbound_vars H0); intros HH.
        eapply disjoint_with_exclusion; eauto.
        intuition; list_simpler; intuition.
      - match_case_in H0; intros ? ? eqq1
         ; rewrite eqq1 in H0.
        invcs H0.
        specialize (stratify1_aux_nbound_vars H1); intros HH.
        eapply disjoint_with_exclusion; eauto.
        intuition; list_simpler; intuition.
    Qed.

  End BoundVars.

  Section FreeVars.

    Fixpoint growing_fv_ctxt (l:list (var*nnrc)) (ctxt:list var) : Prop
      := match l with
         | nil => True
         | (v,e)::lx =>
           incl (nnrc_free_vars e) ctxt
           /\ growing_fv_ctxt lx (v::ctxt)
         end.

    Require Import Program.Basics.
    
    Global Instance growing_fv_ctxt_incl :
      Proper (eq ==> (@incl var) ==> impl) growing_fv_ctxt.
    Proof.
      unfold Proper, respectful, flip, impl. intros ? sdefs ? ctxt1 ctxt2; subst.
      revert ctxt1 ctxt2.
      induction sdefs; simpl; trivial; intros.
      destruct a; simpl.
      intuition.
      - rewrite H1; trivial.
      - eapply IHsdefs; eauto.
        red; simpl; intuition.
    Qed.

    Global Instance growing_fv_ctxt_equiv :
      Proper (eq ==> (@equivlist var) ==> iff) growing_fv_ctxt.
    Proof.
      unfold Proper, respectful, flip, impl. intros ? sdefs ? ctxt1 ctxt2; subst; intros eqq.
      apply equivlist_incls in eqq.
      destruct eqq.
      split; intro HH; eapply growing_fv_ctxt_incl; eauto.
    Qed.

    Lemma growing_fv_ctxt_app sdefs1 sdefs2 ctxt :
          growing_fv_ctxt (sdefs1 ++ sdefs2) ctxt <->
          (growing_fv_ctxt sdefs1 ctxt /\ growing_fv_ctxt sdefs2 (ctxt ++ domain sdefs1)).
    Proof.
      revert ctxt sdefs2; induction sdefs1; intros ctxt sdefs2; simpl.
      - rewrite app_nil_r. intuition.
      - destruct a; simpl.
        rewrite IHsdefs1; simpl.
        assert (eqv: equivlist (v :: ctxt ++ domain sdefs1) (ctxt ++ v :: domain sdefs1))
          by (intro; simpl; repeat rewrite in_app_iff; simpl; intuition).
        rewrite eqv.
        intuition.
    Qed.

        Lemma mk_expr_from_vars_growing_fv_free_fw {sdefs ctxt} :
      growing_fv_ctxt sdefs ctxt ->
      forall e x,
        In x (nnrc_free_vars (mk_expr_from_vars (e, sdefs))) ->
        ((In x (nnrc_free_vars e) /\ ~ In x (domain sdefs)) \/ In x ctxt).
    Proof.
      revert ctxt ; induction sdefs; intros ctxt gfc e x inn; [intuition | ].
      destruct a.
      simpl in *; rewrite mk_expr_from_vars_eq in inn.
      destruct gfc as [incln gfc].
      rewrite in_app_iff in inn.
      destruct inn as [inn|inn]; [intuition | ].
      apply remove_inv in inn.
      destruct inn as [inn neq].
      specialize (IHsdefs _ gfc _ _ inn).
      destruct IHsdefs as [[inn2 inn3] | inn2]; simpl in *; intuition. 
    Qed.

    Lemma mk_expr_from_vars_growing_fv_free_fw_codomain {sdefs e x} :
        In x (nnrc_free_vars (mk_expr_from_vars (e, sdefs))) ->
        ((In x (nnrc_free_vars e) \/ In x (concat (map nnrc_free_vars (codomain sdefs))))).
    Proof.
      revert e x ; induction sdefs; intros e x inn; [intuition | ].
      destruct a.
      simpl in *; rewrite mk_expr_from_vars_eq in inn.
      list_simpler.
      intuition.
      list_simpler.
      apply IHsdefs in H.
      intuition.
    Qed.

    Lemma mk_expr_from_vars_growing_fv_free_bk e sdefs x :
        ((In x (nnrc_free_vars e) \/ In x (concat (map nnrc_free_vars (codomain sdefs)))) /\ ~ In x (domain sdefs)) ->
        In x (nnrc_free_vars (mk_expr_from_vars (e, sdefs))).
    Proof.
      unfold mk_expr_from_vars.
      revert e x; induction sdefs; intros e x inn; [intuition | ].
      destruct a.
      simpl in *; rewrite mk_expr_from_vars_eq in *.
      list_simpler.
      specialize (IHsdefs e x); intuition.
      rewrite mk_expr_from_vars_eq in *.
      list_simpler.
      intuition.
      rewrite mk_expr_from_vars_eq in *.
      list_simpler.
      intuition.
    Qed.

    Lemma stratify1_aux_free_vars_incl {e required_level bound_vars n sdefs1 sdefs2} :
      stratify1_aux e required_level bound_vars sdefs1 = (n, sdefs2) ->
      incl (nnrc_free_vars n) (nnrc_free_vars e ++ (domain sdefs2)).
    Proof.
      destruct required_level; simpl; intros eqq; invcs eqq; simpl.
      - intros ? inn; simpl in inn; intuition.
        subst.
        rewrite domain_app.
        repeat rewrite in_app_iff; simpl; intuition.
      - apply incl_appl; reflexivity.
    Qed.

    Lemma stratify1_aux_sdefs_app {e required_level bound_vars n sdefs1 sdefs2} :
      stratify1_aux e required_level bound_vars sdefs1 = (n, sdefs2) ->
      { l | sdefs2 = sdefs1++l}.
    Proof.
      destruct required_level; simpl; intros eqq; invcs eqq; simpl.
      - eauto.
      - exists nil.
        rewrite app_nil_r; trivial.
    Defined.

    Lemma stratify1_aux_gfc {e required_level bound_vars n sdefs1 sdefs2} :
      stratify1_aux e required_level bound_vars sdefs1 = (n, sdefs2) ->
      forall ctxt,
      growing_fv_ctxt sdefs1 ctxt ->
      growing_fv_ctxt sdefs2 (ctxt++nnrc_free_vars e).
    Proof.
      destruct required_level; simpl; intros HH gfc; invcs HH.
      - rewrite growing_fv_ctxt_app; simpl.
        intuition.
        eapply growing_fv_ctxt_incl; eauto
        ; intros ?; repeat rewrite in_app_iff; intuition.
      - eapply growing_fv_ctxt_incl; eauto
        ; intros ?; repeat rewrite in_app_iff; intuition.
    Qed.

    Lemma stratify1_aux_gfc_weak {e required_level bound_vars n sdefs1 sdefs2} :
      stratify1_aux e required_level bound_vars sdefs1 = (n, sdefs2) ->
      growing_fv_ctxt sdefs1 (nnrc_free_vars e) ->
      growing_fv_ctxt sdefs2 (nnrc_free_vars e).
    Proof.
      intros gfc eqq.
      generalize (stratify1_aux_gfc gfc _ eqq); intros HH.
      - eapply growing_fv_ctxt_incl; eauto
        ; intros ?; repeat rewrite in_app_iff; intuition.
    Qed.

    Lemma stratify1_aux_gfc_app {e required_level bound_vars n sdefs1 sdefs2} :
      stratify1_aux e required_level bound_vars sdefs1 = (n, sdefs1++sdefs2) ->
      forall ctxt,
      growing_fv_ctxt sdefs1 ctxt ->
      growing_fv_ctxt sdefs2 (ctxt++nnrc_free_vars e).
    Proof.
      destruct required_level; simpl; intros HH gfc; invcs HH.
      - apply app_inv_head in H1.
        invcs H1; simpl.
        split; trivial.
        intros ?; repeat rewrite in_app_iff; intuition.
      - assert (mknil:sdefs1++nil = sdefs1++sdefs2) by (rewrite app_nil_r; trivial).
        apply app_inv_head in mknil; subst.
        simpl; trivial.
    Qed.

    Lemma stratify1_aux_gfc_app_weak {e required_level bound_vars n sdefs1 sdefs2} :
      stratify1_aux e required_level bound_vars sdefs1 = (n, sdefs1++sdefs2) ->
      growing_fv_ctxt sdefs1 (nnrc_free_vars e) ->
      growing_fv_ctxt sdefs2 (nnrc_free_vars e).
    Proof.
      intros eqq gfc.
      generalize (stratify1_aux_gfc_app eqq _ gfc); intros HH.
      - eapply growing_fv_ctxt_incl; eauto
        ; intros ?; repeat rewrite in_app_iff; intuition.
    Qed.

    Lemma mk_expr_from_vars_has_codomain_vars a l n :
      In a (concat (map nnrc_free_vars (codomain l))) ->
         ~ In a (domain l) ->
         In a (nnrc_free_vars (mk_expr_from_vars (n, l))).
    Proof.
      unfold mk_expr_from_vars.
      revert a n.
      induction l; simpl; intuition.
      simpl in *.
      list_simpler.
      intuition.
    Qed.

    Lemma stratify1_aux_free_vars {e required_level bound_vars n}
                                     {sdefs1 sdefs2:list (var*nnrc)} :
      stratify1_aux e required_level bound_vars sdefs1 = (n, sdefs1++sdefs2) ->
      equivlist (nnrc_free_vars n ++ (concat (map nnrc_free_vars (codomain sdefs2)))) (nnrc_free_vars e ++ (domain sdefs2)).
    Proof.
      destruct required_level; simpl; intros eqq; invcs eqq; simpl
      ; list_simpler; simpl in *.
      - red; split; simpl; list_simpler; simpl; eauto; intuition.
      - reflexivity.
    Qed.

    Lemma stratify_aux_free_vars_and_growing
          {e required_level bound_vars n sdefs} :
      stratify_aux e required_level bound_vars = (n,sdefs) ->
      incl (nnrc_free_vars e) bound_vars ->
      equivlist (nnrc_free_vars n ++ (concat (map nnrc_free_vars (codomain sdefs)))) (nnrc_free_vars e ++ domain sdefs)
      /\ growing_fv_ctxt sdefs (nnrc_free_vars e).
    Proof.
      unfold equivlist.
      revert required_level bound_vars sdefs n.
      induction e; intros required_level bound_vars sdefs n eqq inclb
      ; simpl in *; invcs eqq; simpl; unfold incl; try tauto.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        match_case_in H0; intros ? ? eqq2; rewrite eqq2 in H0.
        invcs H0; simpl.
        apply incl_app_iff in inclb.
        destruct inclb as [inclb1 inclb2].
        destruct (IHe1 _ _ _ _ eqq1 inclb1) as [IHe1i IHe1g].
        assert (inclb2':incl (nnrc_free_vars e2) (domain l ++ bound_vars))
               by (intros ? inn; list_simpler; intuition).
        specialize (IHe2 _ _ _ _ eqq2 inclb2') as [IHe2i IHe2g].
        list_simpler.
        split. 
        + intros a. specialize (IHe1i a). specialize (IHe2i a).
          repeat rewrite in_app_iff in *.
          intuition.
        + rewrite growing_fv_ctxt_app; split.
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        invcs H0; simpl.
        destruct (IHe _ _ _ _ eqq1 inclb) as [IHe1i IHe1g].
        intuition.
      - destruct (stratify1_aux_sdefs_app H0) as [sdefs' ?]; subst.
        generalize (stratify1_aux_free_vars H0); simpl; intros HH.
        case_eq (stratify_aux e1 nnrcStmt bound_vars); intros ? ? eqq1.
        case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2.
        rewrite eqq1 in *; rewrite eqq2 in *.
        destruct (IHe1 _ _ _ _ eqq1) as [IHe1i IHe1g].
        { intros a; specialize (inclb a); list_simpler; intuition. }
        destruct (IHe2 _ _ _ _ eqq2) as [IHe2i IHe2g].
        { intros a; specialize (inclb a); simpl; list_simpler.
          destruct (v == a); unfold equiv, complement in *.
          - subst; eauto.
          - intros inn; right; apply inclb.
            list_simpler; tauto.
        }
        split. 
        + intros a; rewrite (HH a); clear HH.
          specialize (IHe1i a); specialize (IHe2i a).
          list_simpler.
          split; intros inn.
          * { intuition.
              - generalize (mk_expr_from_vars_growing_fv_free_fw IHe1g _ _ H5)
                ; intros HH.
                intuition.
              - list_simpler.
                generalize (mk_expr_from_vars_growing_fv_free_fw IHe2g _ _ H3)
                ; intros HH.
                intuition.
            }
          * { destruct inn as [inn|inn]; try tauto.
              destruct inn as [inn|inn].
              - assert (adisj:~ In a (domain l)).
                { generalize (stratify_aux_nbound_vars eqq1); intros disj.
                  specialize (disj a).
                  intros innd; apply (disj innd).
                  apply inclb; list_simpler; tauto.
                } 
                generalize (mk_expr_from_vars_growing_fv_free_bk n0 l a); intros HH.
                destruct IHe1i as [IHe1if IHe1ib].
                cut_to IHe1ib; try tauto.
              - list_simpler.
                assert (adisj:~ In a (domain l0)).
                { generalize (stratify_aux_nbound_vars eqq2); intros disj.
                  specialize (disj a).
                  intros innd; apply (disj innd).
                  simpl; right.
                  apply inclb; list_simpler; tauto.
                } 
                generalize (mk_expr_from_vars_growing_fv_free_bk n1 l0 a); intros HH.
                destruct IHe2i as [IHe2if IHe2ib].
                cut_to IHe2ib; try tauto.
            }
        + generalize (stratify1_aux_gfc_app_weak H0); simpl; intros HH2.
          specialize (HH2 I).
          * { eapply growing_fv_ctxt_incl; eauto
              ; intros ?; repeat rewrite in_app_iff; intuition.
              -
                generalize (mk_expr_from_vars_growing_fv_free_fw IHe1g _ _ H1)
                ; intros HH3.
                specialize (IHe1i a).
                list_simpler.
                intuition.
              - list_simpler.
                generalize (mk_expr_from_vars_growing_fv_free_fw IHe2g _ _ H)
                ; intros HH3.
                specialize (IHe2i a).
                list_simpler.
                intuition.
            }
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        destruct (stratify1_aux_sdefs_app H0) as [sdefs' ?]; subst.
        generalize (stratify1_aux_free_vars H0); simpl; intros HH.
        case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2.
        rewrite eqq2 in *.
        destruct (IHe1 _ _ _ _ eqq1) as [IHe1i IHe1g].
        { intros a; specialize (inclb a); list_simpler; intuition. }
        destruct (IHe2 _ _ _ _ eqq2) as [IHe2i IHe2g].
        { intros a; specialize (inclb a); simpl; list_simpler.
          destruct (v == a); unfold equiv, complement in *.
          - subst; eauto.
          - intros inn; right; apply inclb.
            list_simpler; tauto.
        }
        split. 
        + intros a; specialize (HH a).
          specialize (IHe1i a); specialize (IHe2i a).
          list_simpler.
          split; intros inn.
          * { destruct inn as [inn|[inn|inn]].
              - destruct HH as [HHf _].
                cut_to HHf; [ | tauto].
                destruct HHf; [ | tauto].
                destruct H; [tauto | ].
                list_simpler.
                generalize (mk_expr_from_vars_growing_fv_free_fw IHe2g _ _ H)
                ; intros HH.
                intuition.
              - revert IHe1i inn; clear; intuition.
              - destruct HH as [HHf _].
                cut_to HHf; [ | tauto].
                destruct HHf; [ | tauto].
                destruct H; [tauto | ].
                list_simpler.
                generalize (mk_expr_from_vars_growing_fv_free_fw IHe2g _ _ H)
                ; intros HH.
                intuition.
            } 
          * { destruct inn as [inn|inn]; [ | tauto ].
              destruct inn as [inn|inn]; [ tauto | ].
              - list_simpler.
                assert (adisj:~ In a (domain l0)).
                { generalize (stratify_aux_nbound_vars eqq2); intros disj.
                  specialize (disj a).
                  intros innd; apply (disj innd).
                  simpl; right.
                  apply inclb; list_simpler; tauto.
                } 
                destruct IHe2i as [IHe2if IHe2ib].
                cut_to IHe2ib; try tauto.
                generalize (mk_expr_from_vars_growing_fv_free_bk n1 l0 a); intros HH2.
                cut_to HH2; [ | tauto].
                destruct HH as [HHf HHb].
                cut_to HHb; [ | list_simpler; tauto].
                tauto.
            }
        + rewrite growing_fv_ctxt_app; split.
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
          * generalize (stratify1_aux_gfc_app H0 _ IHe1g); intros HH2.
            simpl in HH2.
            eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff.
            intros inn.
            destruct inn as [?|inn]; [tauto | ].
            { destruct inn.
              - specialize (IHe1i a); list_simpler; tauto.
              - list_simpler.
                generalize (mk_expr_from_vars_growing_fv_free_fw IHe2g _ _ H)
                ; intros HH3.
                specialize (IHe2i a).
                list_simpler.
                intuition.
            }
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        destruct (stratify1_aux_sdefs_app H0) as [sdefs' ?]; subst.
        generalize (stratify1_aux_free_vars H0); simpl; intros HH.
        case_eq (stratify_aux e2 nnrcStmt bound_vars); intros ? ? eqq2.
        rewrite eqq2 in *.
        case_eq (stratify_aux e3 nnrcStmt bound_vars); intros ? ? eqq3.
        rewrite eqq3 in *.
        destruct (IHe1 _ _ _ _ eqq1) as [IHe1i IHe1g].
        { intros a; specialize (inclb a); list_simpler; intuition. }
        destruct (IHe2 _ _ _ _ eqq2) as [IHe2i IHe2g].
        { intros a; specialize (inclb a); simpl; list_simpler; intuition. }
        destruct (IHe3 _ _ _ _ eqq3) as [IHe3i IHe3g].
        { intros a; specialize (inclb a); simpl; list_simpler; intuition. }
        split. 
        + intros a; specialize (HH a).
          specialize (IHe1i a); specialize (IHe2i a); specialize (IHe3i a).
          list_simpler.
          split; intros inn.
          * { destruct inn as [inn|[inn|inn]].
              - destruct HH as [HHf _].
                cut_to HHf; [ | tauto].
                destruct HHf; [ | tauto].
                destruct H; [tauto | ].
                list_simpler.
                destruct H.
                + generalize (mk_expr_from_vars_growing_fv_free_fw IHe2g _ _ H)
                  ; intuition.
                + generalize (mk_expr_from_vars_growing_fv_free_fw IHe3g _ _ H)
                  ; intuition.
              - revert IHe1i inn; clear; intuition.
              - destruct HH as [HHf _].
                cut_to HHf; [ | tauto].
                destruct HHf; [ | tauto].
                destruct H; [tauto | ].
                list_simpler.
                destruct H.
                + generalize (mk_expr_from_vars_growing_fv_free_fw IHe2g _ _ H)
                  ; intuition.
                + generalize (mk_expr_from_vars_growing_fv_free_fw IHe3g _ _ H)
                  ; intuition.
            } 
          * { destruct inn as [inn|inn]; [ | tauto ].
              destruct inn as [inn|inn]; [ tauto | ].
              - list_simpler.
                destruct inn as [inn|inn].
                + assert (adisj:~ In a (domain l0)).
                  { generalize (stratify_aux_nbound_vars eqq2); intros disj.
                    specialize (disj a).
                    intros innd; apply (disj innd).
                    apply inclb; list_simpler.
                    revert inn; clear; tauto.
                  }
                destruct IHe2i as [IHe2if IHe2ib].
                cut_to IHe2ib; try tauto.
                generalize (mk_expr_from_vars_growing_fv_free_bk n1 l0 a); intros HH2.
                cut_to HH2; [ | revert IHe2ib adisj; clear; tauto].
                destruct HH as [HHf HHb].
                cut_to HHb; [ | list_simpler].
                * revert HHb; clear; tauto.
                * revert HH2; clear; tauto.
                + assert (adisj:~ In a (domain l1)).
                  { generalize (stratify_aux_nbound_vars eqq3); intros disj.
                    specialize (disj a).
                    intros innd; apply (disj innd).
                    apply inclb; list_simpler.
                    revert inn; clear; tauto.
                  }
                destruct IHe3i as [IHe3if IHe3ib].
                cut_to IHe3ib; try tauto.
                generalize (mk_expr_from_vars_growing_fv_free_bk n2 l1 a); intros HH3.
                cut_to HH3; [ | revert IHe3ib adisj; clear; tauto].
                destruct HH as [HHf HHb].
                cut_to HHb; [ | list_simpler].
                * revert HHb; clear; tauto.
                * revert HH3; clear; tauto.
            }
        + rewrite growing_fv_ctxt_app; split.
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
          * generalize (stratify1_aux_gfc_app H0 _ IHe1g); intros HH2.
            simpl in HH2.
            eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff.
            intros inn.
            destruct inn as [?|inn]; [tauto | ].
            { destruct inn as [inn|[inn|inn]].
              - specialize (IHe1i a); list_simpler; tauto.
              - list_simpler.
                generalize (mk_expr_from_vars_growing_fv_free_fw IHe2g _ _ inn)
                ; intros HH3.
                specialize (IHe2i a).
                list_simpler.
                intuition.
              - list_simpler.
                generalize (mk_expr_from_vars_growing_fv_free_fw IHe3g _ _ inn)
                ; intros HH3.
                specialize (IHe3i a).
                list_simpler.
                intuition.
            }
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        destruct (stratify1_aux_sdefs_app H0) as [sdefs' ?]; subst.
        generalize (stratify1_aux_free_vars H0); simpl; intros HH.
        case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2.
        rewrite eqq2 in *.
        case_eq (stratify_aux e3 nnrcStmt (v0::bound_vars)); intros ? ? eqq3.
        rewrite eqq3 in *.
        destruct (IHe1 _ _ _ _ eqq1) as [IHe1i IHe1g].
        { intros a; specialize (inclb a); list_simpler; intuition. }
        destruct (IHe2 _ _ _ _ eqq2) as [IHe2i IHe2g].
        { intros a; specialize (inclb a); simpl; list_simpler.
          destruct (v == a); unfold equiv, complement in *.
          - subst; eauto.
          - intros inn; right; apply inclb.
            list_simpler; tauto.
        }
        destruct (IHe3 _ _ _ _ eqq3) as [IHe3i IHe3g].
        { intros a; specialize (inclb a); simpl; list_simpler.
          destruct (v0 == a); unfold equiv, complement in *.
          - subst; eauto.
          - intros inn; right; apply inclb.
            list_simpler; tauto.
        }
        split. 
        + intros a; specialize (HH a).
          specialize (IHe1i a); specialize (IHe2i a); specialize (IHe3i a).
          list_simpler.
          split; intros inn.
          * { destruct inn as [inn|[inn|inn]].
              - destruct HH as [HHf _].
                cut_to HHf; [ | tauto].
                destruct HHf; [ | tauto].
                destruct H; [tauto | ].
                destruct H; list_simpler.
                + generalize (mk_expr_from_vars_growing_fv_free_fw IHe2g _ _ H)
                  ; intuition.
                + generalize (mk_expr_from_vars_growing_fv_free_fw IHe3g _ _ H)
                  ; intuition.
              - revert IHe1i inn; clear; intuition.
              - destruct HH as [HHf _].
                cut_to HHf; [ | tauto].
                destruct HHf; [ | tauto].
                destruct H; [tauto | ].
                destruct H; list_simpler.
                + generalize (mk_expr_from_vars_growing_fv_free_fw IHe2g _ _ H)
                  ; intuition.
                + generalize (mk_expr_from_vars_growing_fv_free_fw IHe3g _ _ H)
                  ; intuition.
            } 
          * { destruct inn as [inn|inn]; [ | tauto ].
              destruct inn as [inn|inn]; [ tauto | ].
              - list_simpler.
                destruct inn as [inn|inn].
                + assert (adisj:~ In a (domain l0)).
                  { generalize (stratify_aux_nbound_vars eqq2); intros disj.
                    specialize (disj a).
                    intros innd; apply (disj innd).
                    simpl; right.
                    apply inclb; list_simpler.
                    revert H; clear; tauto.
                  }
                destruct IHe2i as [IHe2if IHe2ib].
                cut_to IHe2ib; try tauto.
                generalize (mk_expr_from_vars_growing_fv_free_bk n1 l0 a); intros HH2.
                cut_to HH2; [ | revert IHe2ib adisj; clear; tauto].
                destruct HH as [HHf HHb].
                cut_to HHb; [ | list_simpler].
                * revert HHb; clear; tauto.
                * revert HH2; clear; tauto.
                * list_simpler; revert H; clear; tauto.
                + assert (adisj:~ In a (domain l1)).
                  { generalize (stratify_aux_nbound_vars eqq3); intros disj.
                    specialize (disj a).
                    intros innd; apply (disj innd).
                    simpl; right.
                    apply inclb; list_simpler.
                    revert H; clear; tauto.
                  }
                destruct IHe3i as [IHe3if IHe3ib].
                cut_to IHe3ib; try tauto.
                generalize (mk_expr_from_vars_growing_fv_free_bk n2 l1 a); intros HH3.
                cut_to HH3; [ | revert IHe3ib adisj; clear; tauto].
                destruct HH as [HHf HHb].
                cut_to HHb; [ | list_simpler].
                * revert HHb; clear; tauto.
                * revert HH3; clear; tauto.
                * list_simpler; revert H; clear; tauto.
            }
        + rewrite growing_fv_ctxt_app; split.
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
          * generalize (stratify1_aux_gfc_app H0 _ IHe1g); intros HH2.
            simpl in HH2.
            eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff.
            intros inn.
            destruct inn as [?|inn]; [tauto | ].
            { destruct inn as [inn|[inn|inn]].
              - specialize (IHe1i a); list_simpler; tauto.
              - list_simpler.
                generalize (mk_expr_from_vars_growing_fv_free_fw IHe2g _ _ H)
                ; intros HH3.
                specialize (IHe2i a).
                list_simpler.
                intuition.
              - list_simpler.
                generalize (mk_expr_from_vars_growing_fv_free_fw IHe3g _ _ H)
                ; intros HH3.
                specialize (IHe3i a).
                list_simpler.
                intuition.
            }
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        destruct (stratify1_aux_sdefs_app H0) as [sdefs' ?]; subst.
        generalize (stratify1_aux_free_vars H0); simpl; intros HH.
        destruct (IHe _ _ _ _ eqq1) as [IHe1i IHe1g].
        { intros a; specialize (inclb a); list_simpler; intuition. }
        split. 
        + intros a; specialize (HH a).
          specialize (IHe1i a).
          list_simpler.
          tauto.
        + rewrite growing_fv_ctxt_app; split.
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
          * generalize (stratify1_aux_gfc_app H0 _ IHe1g); intros HH2.
            simpl in HH2.
            eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff.
            intros inn.
            destruct inn as [?|inn]; [tauto | ].
            specialize (IHe1i a); list_simpler; tauto.
    Qed.

    Corollary stratify_aux_free_vars
          {e required_level bound_vars n sdefs} :
      stratify_aux e required_level bound_vars = (n,sdefs) ->
      incl (nnrc_free_vars e) bound_vars ->
      equivlist (nnrc_free_vars n ++ (concat (map nnrc_free_vars (codomain sdefs)))) (nnrc_free_vars e ++ domain sdefs).
    Proof.
      apply stratify_aux_free_vars_and_growing.
    Qed.

    Corollary stratify_aux_free_vars_gfc
          {e required_level bound_vars n sdefs} :
      stratify_aux e required_level bound_vars = (n,sdefs) ->
      incl (nnrc_free_vars e) bound_vars ->
      growing_fv_ctxt sdefs (nnrc_free_vars e).
    Proof.
      apply stratify_aux_free_vars_and_growing.
    Qed.
    
    Theorem stratify_free_vars e :
      equivlist (nnrc_free_vars (stratify e)) (nnrc_free_vars e).
    Proof.
      unfold stratify.
      case_eq (stratify_aux e nnrcStmt (nnrc_free_vars e)); intros n sdefs eqq1.
      destruct (stratify_aux_free_vars_and_growing eqq1 (incl_refl _))
        as [equiv1 gfc1].
      intros x.
      specialize (equiv1 x).
      list_simpler.
      split; intros inn.
      - generalize (mk_expr_from_vars_growing_fv_free_fw gfc1 _ _ inn).
        intuition.
      - apply (mk_expr_from_vars_growing_fv_free_bk). 
        destruct equiv1 as [_ equiv1b].
        cut_to equiv1b; [ | tauto].
        split; [tauto | ].
        generalize (stratify_aux_nbound_vars eqq1); intros disj.
        specialize (disj x); tauto.
    Qed.

  End FreeVars.
  
  Section Correct.

    Opaque fresh_var.


    Require Import cNNRCEq.

    Lemma mk_expr_from_vars_binop b e1 e2 sdefs :
      nnrc_core_eq
        (mk_expr_from_vars (NNRCBinop b e1 e2, sdefs))
        (NNRCBinop b (mk_expr_from_vars (e1, sdefs)) (mk_expr_from_vars (e2, sdefs))).
    Proof.
      unfold mk_expr_from_vars.
      induction sdefs; simpl.
      - reflexivity.
      - rewrite IHsdefs; simpl.
        red; simpl; intros.
        match_case.
    Qed.


    Lemma stratify_aux_correct h cenv env e bound_vars required_kind :
      incl (nnrc_free_vars e) bound_vars ->
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      @nnrc_core_eval _ h cenv env (mk_expr_from_vars (stratify_aux e required_kind bound_vars)) =
      @nnrc_core_eval _ h cenv env e.
    Proof.
      revert required_kind bound_vars env.
      induction e; intros required_kind bound_vars env fbincl Fde FDce; simpl; trivial.
      - repeat (match_case; intros).
        rewrite mk_expr_from_vars_binop; trivial.
        simpl in *.
        apply incl_app_iff in fbincl.
        destruct fbincl as [fbincl1 fbincl2].
        generalize (stratify_aux_nbound_vars H); intros nb1.
        generalize (stratify_aux_nbound_vars H0); intros nb2.
        specialize (IHe1 nnrcExpr bound_vars env).
        cut_to IHe1; trivial.
        rewrite H in IHe1.
        rewrite <- IHe1.
        specialize (IHe2 nnrcExpr (domain l ++ bound_vars) env).
        cut_to IHe2; trivial; try (apply incl_appr; trivial).
        rewrite H0 in IHe2.
        rewrite <- IHe2.
        repeat rewrite mk_expr_from_vars_app.
        f_equal.
        +
    


    Lemma mk_expr_from_vars_app e l1 l2 :
      mk_expr_from_vars (e, (l1 ++ l2)) =
      mk_expr_from_vars ((mk_expr_from_vars (e, l2)), l1).
    Proof.
      unfold mk_expr_from_vars; simpl.
      rewrite fold_right_app.
      trivial.
    Qed.


    



    Lemma stratify_aux_free_vars {e required_level bound_vars n sdefs} :
      incl (nnrc_free_vars e) bound_vars ->
      stratify_aux e required_level bound_vars = (n,sdefs) ->
      equivlist (nnrc_free_vars n ++ (concat (map nnrc_free_vars (codomain sdefs)))) (nnrc_free_vars e ++ domain sdefs).
    Proof.
      unfold equivlist.
      revert required_level bound_vars sdefs n.
      induction e; intros required_level bound_vars sdefs n inclb eqq
      ; simpl in *; invcs eqq; simpl; unfold incl; try tauto.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        match_case_in H0; intros ? ? eqq2; rewrite eqq2 in H0.
        invcs H0; simpl.
        apply incl_app_iff in inclb.
        destruct inclb as [inclb1 inclb2].
        specialize (IHe1 _ _ _ _ inclb1 eqq1).
        assert (inclb2':incl (nnrc_free_vars e2) (domain l ++ bound_vars))
               by (intros ? inn; list_simpler; intuition).
        specialize (IHe2 _ _ _ _ inclb2' eqq2).
        list_simpler.
        intros a. specialize (IHe1 a); specialize (IHe2 a).
        repeat rewrite in_app_iff in *.
        intuition.
      - admit.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        apply incl_app_iff in inclb.
        destruct inclb as [inclb1 inclb2].
        specialize (IHe1 _ _ _ _ inclb1 eqq1).
        destruct (stratify1_aux_sdefs_app H0) as [sdefs' ?]; subst.
        case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros nn ll eqq2.
        rewrite eqq2 in *.
        assert (inclb2':incl (nnrc_free_vars e2) (v::bound_vars)).
        { unfold incl in *; intros ? inn; simpl.
          destruct (v == a); unfold equiv, complement in *.
          - eauto.
          - right; apply inclb2.
            list_simpler; trivial.
        } 
        specialize (IHe2 _ _ _ _ inclb2' eqq2).
        intros a.
        specialize (IHe1 a); specialize (IHe2 a).
        list_simpler.
        split; intros inn.
        * { intuition.
              - generalize (stratify1_aux_free_vars_incl H0 _ H4); intros inn2.
                simpl in inn2.
                repeat rewrite domain_app in inn2.
                repeat rewrite in_app_iff in inn2.
                intuition.
                list_simpler.
                destruct required_level
                ; simpl in H0; invcs H0
                ; (repeat (list_simpler; simpl in *)); intuition.
                   list_simpler.
                   generalize (mk_expr_from_vars_growing_fv_free_fw_codomain H0); intros HH2.
                   destruct HH2.
                   + revert H1 H11; clear; intuition. apply H1 in H11.
                     revert H11; clear; intuition.
                   generalize (mk_expr_from_vars_growing_fv_free_fw gfc2 _ _ H0)
                   ; intuition.
             }

                generalize (mk_expr_from_vars_growing_fv_free_fw gfc2 _ _ H3); intros HH.
                intuition.
              - destruct required_level
                ; simpl in H0; invcs H0
                ; (repeat (list_simpler; simpl in *)); intuition.
                   list_simpler.
                   generalize (mk_expr_from_vars_growing_fv_free_fw gfc2 _ _ H0)
                   ; intuition.
             }
             * { 
                 generalize (stratify_aux_nbound_vars eqq2); intros disj.
                 apply disjoint_cons_inv2 in disj.
                 destruct disj as [disj vnin].
                 destruct required_level
                ; simpl in H0; invcs H0
                ; (repeat (list_simpler; simpl in *)); intuition; list_simpler.
                   - specialize (H H2).
                     generalize (mk_expr_from_vars_growing_fv_free_bk nn ll a)
                     ; intros HH.
                     specialize (inclb2' _ H2).
                     simpl in inclb2'; destruct inclb2'; [congruence | ].
                     symmetry in disj.
                     specialize (disj _ H9).
                     destruct H.
                     + intuition.
                     + generalize (mk_expr_from_vars_has_codomain_vars a ll)
                       ; intuition.
                   - specialize (H H2).
                     generalize (mk_expr_from_vars_growing_fv_free_bk nn ll a)
                     ; intros HH.
                     specialize (inclb2' _ H2).
                     simpl in inclb2'; destruct inclb2'; [congruence | ].
                     symmetry in disj.
                     specialize (disj _ H9).
                     destruct H.
                     + intuition.
                     + generalize (mk_expr_from_vars_has_codomain_vars a ll)
                       ; intuition.
                    }
          + rewrite growing_fv_ctxt_app; simpl; split.
            * eapply growing_fv_ctxt_incl; eauto
              ; intros ?; repeat rewrite in_app_iff; intuition.
            * generalize (stratify1_aux_gfc_app_weak H0); intros HH.
              simpl in HH.
              { cut_to HH.
                -
                  generalize (mk_expr_from_vars_growing_fv_free_fw gfc1); intros HH2.
                  eapply growing_fv_ctxt_incl; eauto
                  ; intros ?; repeat rewrite in_app_iff; intuition.
                  + specialize (incl1 a).
                    list_simpler.
                    intuition.
                  + list_simpler.
                    admit.
                - eapply growing_fv_ctxt_incl; eauto
                  ; intros ?; repeat rewrite in_app_iff; intuition.
                  specialize (incl1 a).
                  list_simpler.
                  destruct incl1 as [incl11 incl12].
                  cut_to incl12; [ | intuition].
                  destruct incl12; [intuition | ].
                  
                  
                  destruct required_level; simpl in H0.
                  invcs H0.
                ; simpl in H0; invcs H0
                ; (repeat (list_simpler; simpl in *)).
                  


    Lemma stratify_aux_free_vars {e required_level bound_vars n sdefs} :
      incl (nnrc_free_vars e) bound_vars ->
      stratify_aux e required_level bound_vars = (n,sdefs) ->
      (equivlist (nnrc_free_vars n ++ (concat (map nnrc_free_vars (codomain sdefs)))) (nnrc_free_vars e ++ domain sdefs)
      /\ growing_fv_ctxt sdefs (nnrc_free_vars e)).
    Proof.
      unfold equivlist.
      revert required_level bound_vars sdefs n.
      induction e; intros required_level bound_vars sdefs n inclb eqq
      ; simpl in *; invcs eqq; simpl; unfold incl; try tauto.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        match_case_in H0; intros ? ? eqq2; rewrite eqq2 in H0.
        invcs H0; simpl.
        apply incl_app_iff in inclb.
        destruct inclb as [inclb1 inclb2].
        destruct (IHe1 _ _ _ _ inclb1 eqq1) as [incl1 gfc1].
        assert (inclb2':incl (nnrc_free_vars e2) (domain l ++ bound_vars))
               by (intros ? inn; list_simpler; intuition).
        destruct (IHe2 _ _ _ _ inclb2' eqq2) as [incl2 gfc2].
        list_simpler.
        split.
        + intros a. specialize (incl1 a); specialize (incl2 a).
          repeat rewrite in_app_iff in *.
          intuition.
        + rewrite growing_fv_ctxt_app; simpl; split.
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
      - admit.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        apply incl_app_iff in inclb.
        destruct inclb as [inclb1 inclb2].
        destruct (IHe1 _ _ _ _ inclb1 eqq1) as [incl1 gfc1].
        destruct (stratify1_aux_sdefs_app H0) as [sdefs' ?]; subst.
        case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros nn ll eqq2.
        rewrite eqq2 in *.
        assert (inclb2':incl (nnrc_free_vars e2) (v::bound_vars)).
        { unfold incl in *; intros ? inn; simpl.
          destruct (v == a); unfold equiv, complement in *.
          - eauto.
          - right; apply inclb2.
            list_simpler; trivial.
        } 
        specialize (IHe2 _ _ _ _ inclb2' eqq2).
        destruct IHe2 as [incl2 gfc2].
        split.
        + intros a.
          specialize (incl1 a); specialize (incl2 a).
          list_simpler.
          split; intros inn.
          * { intuition.
              - generalize (stratify1_aux_free_vars_incl H0 _ H4); intros inn2.
                simpl in inn2.
                repeat rewrite domain_app in inn2.
                repeat rewrite in_app_iff in inn2.
                intuition.
                list_simpler.
                generalize (mk_expr_from_vars_growing_fv_free_fw gfc2 _ _ H3); intros HH.
                intuition.
              - destruct required_level
                ; simpl in H0; invcs H0
                ; (repeat (list_simpler; simpl in *)); intuition.
                   list_simpler.
                   generalize (mk_expr_from_vars_growing_fv_free_fw gfc2 _ _ H0)
                   ; intuition.
             }
             * { 
                 generalize (stratify_aux_nbound_vars eqq2); intros disj.
                 apply disjoint_cons_inv2 in disj.
                 destruct disj as [disj vnin].
                 destruct required_level
                ; simpl in H0; invcs H0
                ; (repeat (list_simpler; simpl in *)); intuition; list_simpler.
                   - specialize (H H2).
                     generalize (mk_expr_from_vars_growing_fv_free_bk nn ll a)
                     ; intros HH.
                     specialize (inclb2' _ H2).
                     simpl in inclb2'; destruct inclb2'; [congruence | ].
                     symmetry in disj.
                     specialize (disj _ H9).
                     destruct H.
                     + intuition.
                     + generalize (mk_expr_from_vars_has_codomain_vars a ll)
                       ; intuition.
                   - specialize (H H2).
                     generalize (mk_expr_from_vars_growing_fv_free_bk nn ll a)
                     ; intros HH.
                     specialize (inclb2' _ H2).
                     simpl in inclb2'; destruct inclb2'; [congruence | ].
                     symmetry in disj.
                     specialize (disj _ H9).
                     destruct H.
                     + intuition.
                     + generalize (mk_expr_from_vars_has_codomain_vars a ll)
                       ; intuition.
                    }
          + rewrite growing_fv_ctxt_app; simpl; split.
            * eapply growing_fv_ctxt_incl; eauto
              ; intros ?; repeat rewrite in_app_iff; intuition.
            * generalize (stratify1_aux_gfc_app_weak H0); intros HH.
              simpl in HH.
              { cut_to HH.
                -
                  generalize (mk_expr_from_vars_growing_fv_free_fw gfc1); intros HH2.
                  eapply growing_fv_ctxt_incl; eauto
                  ; intros ?; repeat rewrite in_app_iff; intuition.
                  + specialize (incl1 a).
                    list_simpler.
                    intuition.
                  + list_simpler.
                    admit.
                - eapply growing_fv_ctxt_incl; eauto
                  ; intros ?; repeat rewrite in_app_iff; intuition.
                  specialize (incl1 a).
                  list_simpler.
                  destruct incl1 as [incl11 incl12].
                  cut_to incl12; [ | intuition].
                  destruct incl12; [intuition | ].
                  
                  
                  destruct required_level; simpl in H0.
                  invcs H0.
                ; simpl in H0; invcs H0
                ; (repeat (list_simpler; simpl in *)).
                  
                 
            

                 
    
    Lemma stratify_aux_free_vars {e required_level bound_vars n sdefs} :
      stratify_aux e required_level bound_vars = (n,sdefs) ->
      (incl (nnrc_free_vars n) (nnrc_free_vars e ++ domain sdefs)
      /\ growing_fv_ctxt sdefs (nnrc_free_vars e)).
    Proof.
      unfold incl.
      revert required_level bound_vars sdefs n.
      induction e; intros required_level bound_vars sdefs n eqq
      ; simpl in *; invcs eqq; simpl; unfold incl; try tauto.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        match_case_in H0; intros ? ? eqq2; rewrite eqq2 in H0.
        invcs H0; simpl.
        destruct (IHe1 _ _ _ _ eqq1) as [incl1 gfc1].
        destruct (IHe2 _ _ _ _ eqq2) as [incl2 gfc2].
        repeat rewrite domain_app in *.
        split.
        + intros a inn. specialize (incl1 a); specialize (incl2 a).
          repeat rewrite in_app_iff in *.
          intuition.
        + rewrite growing_fv_ctxt_app; simpl; split.
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
      - admit.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        destruct (IHe1 _ _ _ _ eqq1) as [incl1 gfc1].
        destruct (stratify1_aux_sdefs_app H0) as [sdefs' ?]; subst.
        case_eq (stratify_aux e2 nnrcStmt bound_vars); intros nn ll eqq2.
        rewrite eqq2 in *.
        specialize (IHe2 _ _ _ _ eqq2).
        destruct IHe2 as [incl2 gfc2].
        split.
        + intros ? inn.
          generalize (stratify1_aux_free_vars_incl H0 _ inn); intros inn2.
          simpl in inn2.
          specialize (incl1 a).
          repeat rewrite domain_app in *.
          repeat rewrite in_app_iff in *.
          intuition.
          apply remove_inv in H1.
          destruct H1 as [inn2 neq].
          rewrite <- (remove_in_neq _ _ _ neq).
          generalize (mk_expr_from_vars_growing_fv_free_fw gfc2 _ _ inn2); intros HH.
          specialize (incl2 a).
          repeat rewrite in_app_iff in *; intuition.
        + rewrite growing_fv_ctxt_app; simpl; split.
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
          * generalize (stratify1_aux_gfc_app_weak H0); intros HH.
            simpl in HH.
            { cut_to HH.
              - admit.
              -  eapply growing_fv_ctxt_incl; eauto
                 ; intros ?; repeat rewrite in_app_iff; intuition.
                 
            
            
          * eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.
          * 
            eapply growing_fv_ctxt_incl; eauto
            ; intros ?; repeat rewrite in_app_iff; intuition.

    Qed.
            
    Lemma stratify_aux_growing_fv_ctxt {e required_level bound_vars n sdefs} :
      stratify_aux e required_level bound_vars = (n,sdefs) ->
      growing_fv_ctxt sdefs (nnrc_free_vars e).
    Proof.
      revert required_level bound_vars sdefs n.
      induction e; intros required_level bound_vars sdefs n eqq
      ; simpl in *; invcs eqq; simpl; trivial.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        match_case_in H0; intros ? ? eqq2; rewrite eqq2 in H0.
        invcs  H0.
        apply growing_fv_ctxt_app.
        apply IHe1 in eqq1.
        apply IHe2 in eqq2.
        split.
        + eapply growing_fv_ctxt_incl; eauto; intro; rewrite in_app_iff; intuition.
        + eapply growing_fv_ctxt_incl; eauto; intro; rewrite in_app_iff; intuition.
      - admit.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        specialize (IHe1 _ _ _ _ eqq1).
        destruct required_level; simpl in H0; invcs H0.
        + apply growing_fv_ctxt_app.
          split.
          * eapply growing_fv_ctxt_incl; eauto; intro; rewrite in_app_iff; intuition.
          * simpl.
            generalize (mk_expr_from_vars_growing_fv_free_fw IHe1); intros HH.
            split; trivial.
            intros ? inn.
            repeat rewrite in_app_iff in *.
            
            
            
        match_case_in H0; intros ? ? eqq2; rewrite eqq2 in H0.

        


    Lemma mk_expr_from_vars_growing_fv_free e sdefs ctxt :
      disjoint (domain sdefs) (ctxt++nnrc_free_vars e) ->
      growing_fv_ctxt sdefs (ctxt++(nnrc_free_vars e)) ->
      forall x,
        In x (ctxt++nnrc_free_vars (mk_expr_from_vars (e, sdefs))) <->
        ((In x (ctxt++(nnrc_free_vars e))) /\ ~ In x (domain sdefs)).
    Proof.
      unfold mk_expr_from_vars.
      revert e ctxt; induction sdefs; intros e ctxt disj gfc; simpl; [intuition | ].
      intros; destruct a; simpl in *.
      destruct gfc as [incln gfc].
      apply disjoint_cons_inv1 in disj.
      destruct disj as [disj nin].
      repeat rewrite in_app_iff in *.
      split; intros inn.
      - destruct inn as [inn|[inn|inn]]; [intuition | .. ].
        + subst; intuition.
        + eapply disj; eauto.
          rewrite in_app_iff; eauto.
        + intuition; subst.
          * apply incln in inn.
            rewrite in_app_iff in inn; intuition.
          * apply incln in inn.
            eapply disj; eauto.
        + apply remove_inv in inn.
          destruct inn as [inn neq].
          
          
      - subst; intuition.
      - admit.
      - admit.
      - admit.
      - apply remove_inv in H.
        destruct H as [inn neq].
        rewrite mk_expr_from_vars_eq in *.
        admit.
      - apply remove_inv in H.
        destruct H as [inn neq].
        rewrite mk_expr_from_vars_eq in *.
        admit.
        
        

    Lemma mk_expr_from_vars_preserves_same_free e sdefs :
          (forall x y, In (x,y) sdefs -> incl (nnrc_free_vars y) (nnrc_free_vars e)) ->
          incl (nnrc_free_vars (mk_expr_from_vars (e, sdefs)))
               (nnrc_free_vars e).
    Proof.
      unfold mk_expr_from_vars.
      induction sdefs; simpl; intros incls; [reflexivity | ].
      red; intros ? inn.
      rewrite in_app_iff in inn.
      destruct inn as [inn|inn].
      - specialize (incls (fst a) (snd a)).
        destruct a; simpl in *.
        intuition.
      - apply remove_inv in inn.
        destruct inn as [inn Hneq].
        apply IHsdefs in inn; trivial.
        eauto.
    Qed.

    (* critical condition *)
    Lemma stratify1_aux_correct h cenv env e bound_vars required_kind sdefs :
      incl (nnrc_free_vars e) bound_vars ->
      disjoint bound_vars (domain sdefs) ->
      (forall x y, In (x,y) sdefs -> incl (nnrc_free_vars y) (nnrc_free_vars e)) ->
      @nnrc_core_eval _ h cenv env (mk_expr_from_vars (stratify1_aux e required_kind bound_vars sdefs)) =
      @nnrc_core_eval _ h cenv env (mk_expr_from_vars (e,sdefs)).
    Proof.
      destruct required_kind; simpl; trivial.
      unfold mk_expr_from_vars; simpl.
      rewrite fold_right_app; simpl.
      revert e.
      induction sdefs; simpl; intros e inbfv disj same_free.
      - match_option.
        match_destr; try congruence.
      - match_option.
        specialize (IHsdefs e).
        repeat rewrite mk_expr_from_vars_eq in *.
        generalize (@cNNRCShadow.nnrc_core_eval_remove_free_env _ h cenv
                                                                nil); simpl; intros HH.
        repeat rewrite HH.
        + apply IHsdefs; intuition.
          * apply disjoint_cons_inv2 in disj.
            intuition.
          * eapply same_free; right; eauto.
        + intro inn.
          apply mk_expr_from_vars_preserves_same_free in inn.
          * apply inbfv in inn.
            apply disjoint_cons_inv2 in disj.
            intuition.
          * intuition; eauto.
        + intro inn.
          apply mk_expr_from_vars_preserves_same_free in inn.
          * simpl in inn.
            match_destr_in inn; try congruence.
            rewrite app_nil_r in inn.
            apply inbfv in inn.
            apply disjoint_cons_inv2 in disj.
            intuition.
          * intros ? ? inn2.
            simpl; match_destr; try congruence.
            rewrite app_nil_r.
            eapply same_free; eauto.
    Qed.





    (*

    Lemma stratify1_aux_free_vars {e required_kind bound_vars sdefs n l} :
      stratify1_aux e required_kind bound_vars sdefs = (n,l) ->
      bound_vars ++ (domain sdefs)
      equivlist (nnrc_free_vars e ++ domain sdefs) (nnrc_free_vars n ++ domain l).
    Proof.
      destruct required_kind; simpl; trivial; intros eqq; invcs eqq; simpl; trivial.
      - rewrite domain_app.
      - reflexivity.
      intros.
      rewrite domain_app, in_app_iff in inn.
      destruct inn; trivial.
      - simpl in *.
        destruct H0; try tauto.
        subst.
        apply fresh_var_fresh in H.
        tauto.

    Qed.
      
    Lemma stratify_aux_free_vars {e required_kind bound_vars n l} :
      stratify_aux e required_kind bound_vars = (n,l) ->
      equivlist (nnrc_free_vars n) (nnrc_free_vars e ++ domain l).
*)






    Lemma stratify_aux_free_vars_incl {fe n sdefs} :
      incl (nnrc_free_vars n) (fe ++ (domain sdefs)) ->
      (forall x y, In (x,y) sdefs -> incl (nnrc_free_vars y) fe) ->
      incl (nnrc_free_vars (mk_expr_from_vars (n,sdefs))) fe.
    Proof.
      unfold mk_expr_from_vars.
      revert fe n.
      induction sdefs; intros fe n incl1 incl2; simpl in *.
      - rewrite app_nil_r in incl1; trivial.
      - intros ? inn.
        rewrite in_app_iff in inn.
        destruct inn as [inn|inn].
        + destruct a as [aa ab].
          specialize (incl2 aa ab); intuition.
        + apply remove_inv in inn.
          destruct inn as [inn neq].
          eapply IHsdefs; try eapply inn; eauto.
          intros ? inn2.
          specialize (incl1 _ inn2).
          rewrite in_app_iff in incl1; simpl in incl1.
          rewrite in_app_iff.
          intuition.
          subst.
          

          
    In a (nnrc_free_vars (mk_expr_from_vars (stratify_aux e nnrcStmt bound_vars))) = nnrc_free_vars e

    
    Lemma stratify_aux_free_vars_incl {e required_level bound_vars n sdefs} :
      stratify_aux e required_level bound_vars = (n, sdefs) ->
      (incl (nnrc_free_vars n) (nnrc_free_vars e ++ (domain sdefs))
    /\ (forall x y, In (x,y) sdefs -> incl (nnrc_free_vars y) (nnrc_free_vars e))).
    Proof.
      revert required_level bound_vars sdefs n.
      induction e; intros required_level bound_vars sdefs n eqq
      ; simpl in *; invcs eqq; simpl.
      - intuition.
      - intuition.
      - intuition.
      - match_case_in H0; intros ? ? eqq1
        ; rewrite eqq1 in H0.
         match_case_in H0; intros ? ? eqq2
         ; rewrite eqq2 in H0.
         invcs H0; simpl.
         destruct (IHe1 _ _ _ _ eqq1) as [IHe11 IHe12].
         destruct (IHe2 _ _ _ _ eqq2) as [IHe21 IHe22].
         split
         ; unfold incl in *; [intros ? inn | intros ? ? inn1 ? inn2]
          ; repeat rewrite domain_app in *
          ; repeat rewrite in_app_iff in *.
        + destruct inn as [inn|inn].
          * specialize (IHe11 _ inn).
            rewrite in_app_iff in IHe11.
            intuition.
          * specialize (IHe21 _ inn).
            rewrite in_app_iff in IHe21.
            intuition.
        + intuition eauto.
      -  match_case_in H0; intros ? ? eqq1
         ; rewrite eqq1 in H0.
         invcs H0; simpl.
         eauto.
      - match_case_in H0; intros ? ? eqq1
        ; rewrite eqq1 in H0; simpl.
        specialize (IHe1 _ _ _ _ eqq1).
        destruct IHe1 as [IHe11 IHe12].
        destruct (stratify1_aux_sdefs_app H0); subst.
        apply stratify1_aux_free_vars_incl in H0.
        simpl in H0.
        split; [intros ? inn | intros ? ? inn1 ? inn2]
        ; repeat rewrite domain_app
        ; repeat rewrite in_app_iff.
        + specialize (H0 _ inn).
          rewrite domain_app in H0.
          repeat rewrite in_app_iff in H0.
          intuition.
          * specialize (IHe11 _ H0).
            rewrite in_app_iff in IHe11.
            intuition.
          *  apply remove_inv in H0.
             destruct H0 as [inn2 neq].
             rewrite <- remove_in_neq by trivial.


             case_eq ((stratify_aux e2 nnrcStmt bound_vars)); intros ? ? eqq2
             ; rewrite eqq2 in *.
             specialize (IHe2 _ _ _ _ eqq2).
             destruct IHe2 as [IHe21 IHe22].
             
             
             specialize (mk_expr_from_vars_preserves_same_free n1 l0)
             ; intros incl2.
             { cut_to incl2.
               - admit.
               - intros ? ? inn3 ? inn4.
                 specialize (IHe22 _ _ inn3 _ inn4).
             
             
          
          generalize (
          
SearchAbout remove.
          

          
          
          generalize (mk_expr_from_vars_preserves_same_free 
          
              
        specialize (stratify1_aux_nbound_vars H0); intros HH.
        eapply disjoint_with_exclusion; eauto.
      - match_case_in H0; intros ? ? eqq1
        ; rewrite eqq1 in H0.
        specialize (IHe1 _ _ _ _ eqq1).
        specialize (stratify1_aux_nbound_vars H0); intros HH.
        eapply disjoint_with_exclusion; eauto.
      - match_case_in H0; intros ? ? eqq1
        ; rewrite eqq1 in H0.
        specialize (IHe1 _ _ _ _ eqq1).
        specialize (stratify1_aux_nbound_vars H0); intros HH.
        eapply disjoint_with_exclusion; eauto.
      - match_case_in H0; intros ? ? eqq1
        ; rewrite eqq1 in H0.
        specialize (IHe1 _ _ _ _ eqq1).
        specialize (stratify1_aux_nbound_vars H0); intros HH.
        eapply disjoint_with_exclusion; eauto.
      - match_case_in H0; intros ? ? eqq1
         ; rewrite eqq1 in H0.
         invcs H0.
         eauto.
    Qed.
    Lemma stratify_aux_correct h cenv env e bound_vars required_kind :
      incl (nnrc_free_vars e) bound_vars ->
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      @nnrc_core_eval _ h cenv env (mk_expr_from_vars (stratify_aux e required_kind bound_vars)) =
      @nnrc_core_eval _ h cenv env e.
    Proof.
      revert required_kind bound_vars env.
      induction e; intros required_kind bound_vars env fbincl Fde FDce; simpl; trivial.
      - repeat (match_case; intros).
        rewrite mk_expr_from_vars_binop; trivial.
        simpl in *.
        apply incl_app_iff in fbincl.
        destruct fbincl as [fbincl1 fbincl2].
        generalize (stratify_aux_nbound_vars H); intros nb1.
        generalize (stratify_aux_nbound_vars H0); intros nb2.
        specialize (IHe1 nnrcExpr bound_vars env).
        cut_to IHe1; trivial.
        rewrite H in IHe1.
        rewrite <- IHe1.
        specialize (IHe2 nnrcExpr (domain l ++ bound_vars) env).
        cut_to IHe2; trivial; try (apply incl_appr; trivial).
        rewrite H0 in IHe2.
        rewrite <- IHe2.
        repeat rewrite mk_expr_from_vars_app.
        f_equal.
        +

          


          
          
        + 

          
          
        + 
        
        SearchAbout fold_right.
            Definition mk_expr_from_vars (nws:nnrc_with_substs)
      := fold_right (fun sdef accum => NNRCLet (fst sdef) (snd sdef) accum) (fst nws) (snd nws).

      - 

        Lemma nnrc_core_eval_remove_free_env {h:list (string*string)} c l v x l' e :
          disjoint (domain l3) (nnrc_free_vars e) ->
          nnrc_core_eval h c (l ++ l3 ++ l') e = nnrc_core_eval h c (l ++ l') e.
  Proof.

        
        
        rewrite IHe1.
        
        
        rewrite IHe1.
        


      
    Section tests.
    Local Open Scope nnrc_scope.
    Local Open Scope string_scope.

    Eval vm_compute in (stratify nnrc1).

    Eval vm_compute in (stratify nnrc2).
    Eval vm_compute in (stratify nnrc2).

    Example nnrcC1 := (NNRCFor "x"%string ‵(dnat 1) ‵(dnat 2)) ‵+ (NNRCFor "y"%string ‵(dnat 3) ‵(dnat 4)).
    Eval vm_compute in (stratify nnrcC1).
    
(*    Example nnrc3 := (‵abs (NNRCLet "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8)))) ‵+ ‵(dnat 5)) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))). *)
    Eval vm_compute in (stratify nnrc3). 

    Example nnrc4 := (‵abs (NNRCFor "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8)))) ‵+ ‵(dnat 5)) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))).
(*    Eval vm_compute in (stratify nnrc4). *)

    Example nnrc5 := (‵abs (NNRCLet "z" (NNRCFor "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8)))) ‵+ ‵(dnat 5)) (NNRCVar "z")) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))).
(*    Eval vm_compute in (stratify nnrc5). *)

    Example nnrc6 := (‵abs (NNRCLet "z" (NNRCFor "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8))))) (NNRCVar "z")) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))).
(*    Eval vm_compute in (stratify nnrc6). *)

    Example nnrc7 := NNRCLet "x" (NNRCLet "y" ‵(dnat 3) (‵(dnat 8) ‵+ (NNRCVar "y"))) (NNRCVar "x").
    
(*    Eval vm_compute in (stratify nnrc7). *)

    Example nnrc8 := NNRCLet "x" (NNRCLet "x" ‵(dnat 3) (‵(dnat 8) ‵+ (NNRCVar "x"))) (NNRCVar "x").
    
(*    Eval vm_compute in (stratify nnrc8). *)

  End tests.
        Definition stratify1_aux
               (body:nnrc)
               (required_kind:nnrcKind)
               (bound_vars:list var)
               (sdefs:list (var*nnrc))
      : nnrc_with_substs
      := match required_kind with
         | nnrcExpr =>
           let fvar := fresh_var "stratify" bound_vars in
           (NNRCVar fvar, (fvar, body)::sdefs)
         | _ => (body, sdefs)
         end.
    
    Fixpoint stratify_aux (e: nnrc) (required_kind:nnrcKind) (bound_vars:list var): nnrc_with_substs
      := match e with
         | NNRCG
                    
    
         





        Definition stratify1_aux
               (body:nnrc)
               (required_kind:nnrcKind)
               (bindings:list var)
               (holey_expr:nnrc->list var->nnrc) :=
      match required_kind with
      | nnrcExpr =>
        let fvar := fresh_var "stratify" bindings in
        let bindings1 := fvar::bindings in
        NNRCLet fvar body (holey_expr (NNRCVar fvar) bindings1)
      | _ => holey_expr body bindings
      end.
    
    (* stratify that produces a given type *)
    (* holey_expr : {n:nnrc | stratifiedLevel_spec required_kind n} -> list var -> nnrc *)
    Fixpoint stratify_aux (e: nnrc) (required_kind:nnrcKind) (bound_vars:list var) (holey_expr:nnrc->list var->nnrc): nnrc
      := match e with
         | NNRCGetConstant c =>
           (holey_expr (NNRCGetConstant c) bound_vars)
         | NNRCVar _ => holey_expr e bound_vars
         | NNRCConst _ => holey_expr e bound_vars
         | NNRCBinop b e1 e2 =>
           stratify_aux e1 nnrcExpr bound_vars
                        (fun e1n bound_vars1 =>
                           stratify_aux e2 nnrcExpr bound_vars1
                                        (fun e2n bound_vars2 =>
                                           (holey_expr (NNRCBinop b e1n e2n) bound_vars2)))
         | NNRCUnop u e1 =>
           stratify_aux e1 nnrcExpr bound_vars
                        (fun e1n bound_vars1 => 
                           (holey_expr (NNRCUnop u e1n) bound_vars1))
         | NNRCLet x e1 e2 =>
           stratify_aux e1 nnrcStmt bound_vars
                        (fun e1n bound_vars1 =>
                           let body := NNRCLet x e1n
                                               (stratify_aux e2 nnrcStmt (x::bound_vars1) (fun e _ => e)) in
                           stratify1_aux body required_kind bound_vars1 holey_expr)
         | NNRCFor x e1 e2 => 
           stratify_aux e1 nnrcExpr bound_vars
                        (fun e1n bound_vars1 =>
                           let body := NNRCFor x e1n
                                               (stratify_aux e2 nnrcStmt (x::bound_vars1) (fun e _ => e ))
                           in
                           stratify1_aux body required_kind bound_vars1 holey_expr)
         | NNRCIf e1 e2 e3 => 
           stratify_aux e1 nnrcExpr bound_vars
                        (fun e1n bound_vars1 =>
                           let body := (NNRCIf e1n
                                               (stratify_aux e2 nnrcStmt bound_vars1 (fun e _ => e ))
                                               (stratify_aux e3 nnrcStmt bound_vars1 (fun e _ => e ))) in
                           stratify1_aux body required_kind bound_vars1 holey_expr)
         | NNRCEither e1 x2 e2 x3 e3 => 
           stratify_aux e1 nnrcExpr bound_vars
                        (fun e1n bound_vars1 =>
                           let body := NNRCEither e1n
                                                  x2 (stratify_aux e2 nnrcStmt (x2::bound_vars1) (fun e _ => e ))
                                                  x3 (stratify_aux e3 nnrcStmt (x3::bound_vars1) (fun e _ => e )) in
                           stratify1_aux body required_kind bound_vars1 holey_expr)
         | NNRCGroupBy s ls e1 =>
           stratify_aux e1 nnrcExpr bound_vars
                        (fun e1n bound_vars1 =>
                           let body := (NNRCGroupBy s ls e1n) in
                           stratify1_aux body required_kind bound_vars1 holey_expr)
         end.

    (*
    Definition holey_preserver
               h cenv (holey_expr:nnrc->list var -> nnrc) 
      := forall moreenv e e' env,
        Forall (data_normalized h) (map snd env) ->
        Forall (data_normalized h) (map snd moreenv) ->
        incl (nnrc_free_vars e) (domain env) ->
        nnrc_core_eval h cenv env e = nnrc_core_eval h cenv env e' ->
        disjoint moreenv env ->
        nnrc_core_eval h cenv (moreenv++env) (holey_expr e (domain env))
        = nnrc_core_eval h cenv (moreenv++env) (holey_expr e' (domain moreenv++(domain env))).
*)

    Inductive holey_some_preserver h cenv : (nnrc->list var -> nnrc) -> Prop
      :=
      | holey_some_preserver_base holey_expr v d e env :
           Forall (data_normalized h) (map snd env) ->
           incl (nnrc_free_vars e) (domain env) ->
           ~ In v (domain env) ->
           nnrc_core_eval h cenv env e = Some d ->
           nnrc_core_eval h cenv env (holey_expr e (domain env))
           = nnrc_core_eval h cenv ((v,d)::env) (holey_expr (NNRCVar v) (v::(domain env))) -> holey_some_preserver h cenv holey_expr
      | holey_some_preserver_ind
          holey_expr
    .
    
    Definition holey_some_preserver
               h cenv (holey_expr:nnrc->list var -> nnrc) 
      := forall v d e env,
        Forall (data_normalized h) (map snd env) ->
        incl (nnrc_free_vars e) (domain env) ->
        ~ In v (domain env) ->
        nnrc_core_eval h cenv env e = Some d ->
        nnrc_core_eval h cenv env (holey_expr e (domain env))
        = nnrc_core_eval h cenv ((v,d)::env) (holey_expr (NNRCVar v) (v::(domain env)))
    .

    Definition holey_none_preserver
               h cenv (holey_expr:nnrc->list var -> nnrc) 
      := forall e env,
        Forall (data_normalized h) (map snd env)
        -> nnrc_core_eval h cenv env e = None
        -> nnrc_core_eval h cenv env (holey_expr e (domain env)) = None.

(*
    

    Definition holey_preserver
               h cenv (holey_expr:nnrc->list var -> nnrc)
      := forall e env,
        Forall (data_normalized h) (map snd env) ->        
        match nnrc_core_eval h cenv env e with
        | Some d =>
          forall moreenv e',
            Forall (data_normalized h) (map snd moreenv) ->
            nnrc_core_eval h cenv (moreenv++env) e' = Some d ->
            disjoint (domain moreenv) (domain env) ->
            nnrc_core_eval h cenv env (holey_expr e (domain env))
            = nnrc_core_eval h cenv (moreenv++env) (holey_expr e' (domain moreenv++(domain env)))
        | None => nnrc_core_eval h cenv env (holey_expr e (domain env)) = None
        end.
     *)

    Lemma stratify1_aux_core_correct
          h cenv (env:bindings)
          (e:nnrc) (required_level:nnrcKind)
          (holey_expr:nnrc->list var->nnrc) :
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      incl (nnrc_free_vars e) (domain env) ->
      holey_some_preserver h cenv holey_expr ->
      holey_none_preserver h cenv holey_expr ->
      nnrc_core_eval h cenv env (stratify1_aux e required_level (domain env) holey_expr) =
      nnrc_core_eval h cenv env (holey_expr e (domain env)).
    Proof.
      intros cenv_normalized env_normalized inclfe hsp hnp.
      destruct required_level; simpl; trivial.
      symmetry.
      match_option.
      - apply hsp; trivial.
        eapply fresh_var_fresh; eauto.
      - apply hnp; trivial.
    Qed.
    
    Lemma holey_preserver_binop1 h cenv b e1 holey_expr :
          holey_some_preserver h cenv holey_expr ->
          holey_some_preserver h cenv
          (fun (e2n : nnrc) (bound_vars2 : list var) =>
             holey_expr (NNRCBinop b e1 e2n) bound_vars2).
    Proof.
      unfold holey_some_preserver; intros hsp; intros.
      apply hsp.
      
(*      

      generalize (hp e env H); intros hp1.
      generalize (hp ((NNRCBinop b e1 e)) env H); intros hp2.
      match_option; intros.
      - rewrite eqq in *.
        match_option_in hp2.
        + apply hp2; trivial.
          simpl in eqq0.
          apply some_olift2 in eqq0.
          destruct eqq0 as [? [??[??]]].
          simpl.
          eapply nnrc_core_eval_some_env_extend_disjoint in e0; eauto.
          rewrite e0.
          rewrite H1; simpl.
          rewrite H3 in eqq; invcs eqq.
          congruence.
        + rewrite hp2.
          simpl in eqq0.
          rewrite eqq in eqq0.
          unfold olift2 in eqq0.
          match_option_in eqq0.
          * admit.
          * specialize (hp (NNRCBinop b e1 e') (moreenv++env)).
            simpl in hp.

            eapply (nnrc_core_eval_some_env_extend_disjoint in eqq1; eauto.

            rewrite eqq1 in hp.
          
          generalize (hp ((NNRCBinop b e1 e')) (moreenv++env)); intros hp3.
          match_case_in hp3.
          simpl in hp3.
          rewrite eqq in eqq0.
          

          

      - 
    Qed.
 *)
    Admitted.
    
    Lemma stratify_aux_core_correct
          h cenv (env:bindings)
          (e:nnrc) (required_level:nnrcKind)
          (holey_expr:nnrc->list var->nnrc) :
      holey_preserver h cenv holey_expr ->
      nnrc_eq (stratify_aux e required_level (domain env) holey_expr)
              (holey_expr e (domain env)).
              
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      holey_preserver h cenv holey_expr ->
      nnrc_core_eval h cenv env (stratify_aux e required_level (domain env) holey_expr) =
      nnrc_core_eval h cenv env (holey_expr e (domain env)).
    Proof.
      revert required_level env holey_expr.
      nnrc_cases (induction e) Case; intros required_level env holey_expr cenv_normalized env_normalize hp; simpl; trivial.
      - Case "NNRCBinop"%string.
        admit.
        (*
        rewrite IHe1; trivial.
        + rewrite IHe2; trivial.
          * red; intros.
            { specialize (hp e env).
              match_option; intros.
              - 
admit. (*            
            apply (hsp moreenv).
            apply hsp; trivial.
            simpl.
            rewrite H0; trivial.
          * 
        + red; intros.
          repeat rewrite IHe2; trivial.
          * apply hp; simpl; trivial.
            rewrite H0; trivial.
          * red; intros.
            apply hp; trivial.
            simpl; rewrite H2; trivial.
          * red; intros.
            apply hp; trivial.
            simpl; rewrite H2; trivial. *)
*)
      - Case "NNRCUnop"%string.
        admit.
      - Case "NNRCLet"%string.
        rewrite IHe1; trivial.
        + rewrite stratify1_aux_core_correct; trivial.
           generalize (hp (NNRCLet v e1
                                   (stratify_aux e2 nnrcStmt (v :: domain env) (fun (e : nnrc) (_ : list var) => e))) env env_normalize); intros hp1.
           generalize (hp (NNRCLet v e1 e2) env env_normalize); intros hp2.
           match_option_in hp2; match_option_in hp1.
          * admit.
          * rewrite hp1.
            admit.
          * rewrite hp2.
            admit.
          * rewrite hp1, hp2; trivial.
        + red; unfold stratify1_aux; intros.
          destruct required_level; simpl.
          match_option; intros.
          * rewrite H1.
            {  rewrite IHe2; trivial.
              - specialize (IHe2 nnrcStmt (((v, d) :: moreenv ++ env0))).
                simpl in IHe2.
                repeat rewrite domain_app in IHe2.
                rewrite IHe2; trivial.
                replace (((v, d) :: moreenv ++ env)) with (((v, d) :: nil ++ moreenv ++ env)) by (simpl; trivial).
                rewrite <- nnrc_core_eval_some_env_extend_disjoint.
                + 
              repeat match_option.
              - 
            
          * simpl.
    Qed.

    Lemma stratify_aux_core_correct
          h cenv (env:bindings)
          (e:nnrc) (required_level:nnrcKind)
          (holey_bindings:list var) (holey_expr:nnrc->list var->nnrc) :
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      holey_preserver h cenv holey_expr holey_bindings ->
      nnrc_core_eval h cenv env (stratify_aux e required_level holey_bindings holey_expr) =
      nnrc_core_eval h cenv env (holey_expr e holey_bindings).
    Proof.
      revert required_level env holey_bindings holey_expr.
      induction e; intros required_level env holey_bindings holey_expr cenv_normalized env_normalize hp; simpl; trivial.
      - admit.
      - apply IHe; trivial.
        repeat red; intros.
        apply hp; trivial.
        simpl; rewrite H; trivial.
      - rewrite IHe1; trivial.
        + { destruct required_level.
            - simpl.
              case_eq (nnrc_core_eval h cenv env e1); intros.
              + admit.
              + 
              
              rewrite hp; trivial.
              

    
    (* our holey contexts preserve contextual equivalence *)
    Definition holey_preserver
               h cenv (holey_expr:nnrc->list var -> nnrc) (holey_bindings:list var)
      :=
        forall e env d ,
          incl (domain env) holey_bindings ->
          nnrc_core_eval h cenv env e = Some d ->
        forall holey_bindings',
          incl holey_bindings holey_bindings' ->
          nnrc_core_eval h cenv env (holey_expr e holey_bindings) =
          nnrc_core_eval h cenv env (holey_expr (NNRCConst d) holey_bindings).

    Lemma stratify_aux_core_correct
          h cenv (env:bindings)
          (e:nnrc) (required_level:nnrcKind)
          (holey_bindings:list var) (holey_expr:nnrc->list var->nnrc) d :
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      holey_preserver h cenv holey_expr holey_bindings ->
      nnrc_core_eval h cenv env e = Some d ->
      nnrc_core_eval h cenv env (stratify_aux e required_level holey_bindings holey_expr) =
      nnrc_core_eval h cenv env (holey_expr (NNRCConst d) holey_bindings).
    Proof.
      revert required_level d env holey_bindings holey_expr.
      induction e; intros required_level dd env holey_bindings holey_expr cenv_normalized env_normalized holey_preserver evale; simpl in *.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - match_case_in evale; [ intros ? eqq | intros eqq]; rewrite eqq in evale; try discriminate.
        rewrite IHe1 with (d:=d); trivial.
        + destruct required_level; simpl.
          * {
              match_case; intros; trivial.
              - admit.
              - rewrite (IHe2 _ dd) in H; trivial.
                + simpl in H; discriminate.
                + admit.
                + repeat red; intros.
                  apply (holey_preserver _ env0).
                case_eq (nnrc_core_eval h cenv env (holey_expr (NNRCConst dd) holey_bindings)); trivial; intros.
                
              simpl in H.
              apply h
              apply (holey_preserver _ env _ ((fresh_var "stratify" holey_bindings, d0) :: env)).
            } 
        eapply IHe1.
        rewrite IHe1.
        apply (holey_preserver env).
        
        
    Definition holey_preserver
               h cenv holey_expr (holey_bindings:list var) :=
      forall env e e',
        Forall (data_normalized h) (map snd env) ->
        incl (nnrc_vars e) holey_bindings ->
        nnrc_core_eval h cenv env e =
        nnrc_core_eval h cenv env e' ->
        forall holey_bindings', sublist holey_bindings holey_bindings' ->
                                nnrc_core_eval h cenv env (holey_expr e holey_bindings') =
                                nnrc_core_eval h cenv env (holey_expr e' holey_bindings').

    Lemma holey_preserver_unop h cenv holey_expr u holey_bindings :
      holey_preserver h cenv holey_expr holey_bindings ->
      holey_preserver h cenv
                      (fun (e1n : nnrc) (bindings1 : list var) => holey_expr (NNRCUnop u e1n) bindings1)
                      holey_bindings.
    Proof.
      intros hp.
      red; intros.
      rewrite hp; trivial.
      simpl.
      rewrite H1; trivial.
    Qed.

    (*
    Lemma holey_preserver_bindings_cons h cenv holey_expr holey_bindings v :
      holey_preserver h cenv holey_expr holey_bindings ->
      holey_preserver h cenv holey_expr (v :: holey_bindings).
    Proof.
      intros hp.
      red; intros.
      rewrite hp; trivial.
      - 
      rewrite <- H2.
      constructor; reflexivity.
    Qed.

    Lemma holey_preserver_bindings_app h cenv holey_expr holey_bindings morebindings :
      holey_preserver h cenv holey_expr holey_bindings ->
      holey_preserver h cenv holey_expr (morebindings ++ holey_bindings).
    Proof.
      revert holey_bindings.
      induction morebindings; intros holey_bindings H; simpl; trivial.
      apply holey_preserver_bindings_cons; auto.
    Qed.

    Lemma holey_preserver_bindings_sublist h cenv holey_expr holey_bindings holey_bindings' :
      sublist holey_bindings holey_bindings' ->
      holey_preserver h cenv holey_expr holey_bindings ->
      holey_preserver h cenv holey_expr holey_bindings'.
    Proof.
      red; intros.
      apply H0; trivial.
      rewrite H; trivial.
    Qed.
   *)
    
(*    Lemma holey_preserver_let2 h cenv v e1 holey_expr holey_bindings :
      Forall (data_normalized h) (map snd cenv) ->
      holey_preserver h cenv holey_expr holey_bindings ->
      ~In v holey_bindings ->
      holey_preserver h cenv
    (fun e2 (bindings1 : list var) =>
       NNRCLet v e1 (holey_expr e2 bindings1)) holey_bindings.
    Proof.
      red; intros ? hp; intros.
      simpl.
      match_case; intros.
      apply hp; trivial.
      - simpl.
        constructor; trivial.
        eapply nnrc_core_eval_normalized; try eapply H5; eauto.
      - 
    Qed.
    
      rewrite hp; trivial.
      simpl.
      rewrite H3.
      trivial.
      

      (fun e b =>
         NNRCLet v e1 e)
        
      (fun e b => (stratify_aux e required_level b holey_expr))
      
    Stratified.holey_preserver h cenv
    (fun (e1n : nnrc) (bindings1 : list var) =>
       NNRCLet v e1n
               (stratify_aux e2 required_level bindings1 holey_expr))
    holey_bindings
   *)

    Lemma stratify_aux_core_correct
          h cenv (env:bindings)
          (e:nnrc) (required_level:nnrcKind)
          (holey_bindings:list var) (holey_expr:nnrc->list var->nnrc) d :
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      incl (nnrc_vars e) holey_bindings ->
      incl (domain env) holey_bindings ->
      Proper (eq ==> equivlist ==> eq) holey_expr ->
      holey_preserver h cenv holey_expr holey_bindings ->
      nnrc_core_eval h cenv env e = Some d ->
      nnrc_core_eval h cenv env (holey_expr (NNRCConst d) holey_bindings) =
      nnrc_core_eval h cenv env (stratify_aux e required_level holey_bindings holey_expr).
    Proof.
      revert required_level d env holey_bindings holey_expr.
      induction e; intros required_level dd env holey_bindings holey_expr cenv_normalized env_normalized inclvars incldomain holey_proper holey_preserver evale; simpl in *.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - apply (holey_preserver env nil).
        
      - apply (holey_preserver env nil); try reflexivity; simpl; auto 1.
        rewrite evale.
        f_equal; apply normalize_normalized_eq.
        rewrite Forall_forall in cenv_normalized.
        eapply cenv_normalized.
        unfold edot in evale.
        apply assoc_lookupr_in in evale.
        rewrite in_map_iff.
        exists (v,dd); tauto.
      - apply (holey_preserver env nil); try reflexivity; simpl; auto 1.
        rewrite evale.
        f_equal; apply normalize_normalized_eq.
        rewrite Forall_forall in env_normalized.
        eapply env_normalized.
        unfold edot in evale.
        apply lookup_in in evale.
        rewrite in_map_iff.
        exists (v,dd); tauto.
      -  intros.
         apply (holey_preserver env nil); simpl; try reflexivity; auto 1.
         invcs evale.
        rewrite normalize_idem; trivial.
      - (* Binary operator *) admit.
      - apply some_olift in evale.
        destruct evale as [ed eqq1 eqq2].
        erewrite <- IHe; try eapply eqq1; trivial.
        + apply (holey_preserver env nil); try reflexivity; simpl; auto 1.
          assert (edn:  data_normalized h ed)
            by (eapply nnrc_core_eval_normalized; try eapply eqq1; eauto).
          assert (ddn:  data_normalized h dd)
            by (eapply unary_op_eval_normalized; try eapply eqq2; eauto).
          repeat rewrite normalize_normalized_eq; trivial.
        + repeat red; intros; subst. apply holey_proper; trivial.
        + apply holey_preserver_unop; trivial.
      - (* Let case *)
        match_case_in evale; [intros ld ldeval | intros ldeval];
          rewrite ldeval in evale; try discriminate.
        assert (ldn:data_normalized h ld)
          by (eapply nnrc_core_eval_normalized; try eapply ldeval; eauto).
        erewrite <- IHe1; try eapply ldeval; trivial.
        + simpl. rewrite <- IHe2 with (d:=dd); trivial.
          * {
              transitivity (nnrc_core_eval h cenv ((v, normalize_data h ld) :: env)
                                           (holey_expr (NNRCConst dd) (v :: holey_bindings))).
              - admit.
(*                
               apply (holey_preserver env ((v, normalize_data h ld) :: nil)); try reflexivity; auto 1; simpl.
              + simpl; repeat constructor.
                apply normalize_normalizes.
              + red; intuition.
              + eapply disjoint_incl; try eapply disjbound.
                red; simpl; intuition.
   *)
              - f_equal.
                apply holey_proper; trivial.
                red; simpl; intuition; subst.
                apply inclvars.
                unfold nnrc_vars; rewrite in_app_iff; simpl; intuition.
            } 
          * constructor; trivial; simpl.
            apply normalize_normalizes.
          * eapply incl_letvars2; eauto.
          * admit.
(*            { apply disjoint_cons1.
              - symmetry in disjbound.
                apply disjoint_cons_inv1 in disjbound.
                rewrite disjoint_app_l in disjbound.
                symmetry; intuition.
              - match_destr_in nshadow.
            }  *)
          * rewrite normalize_normalized_eq; trivial.
        + eapply incl_letvars1; eauto.
        + repeat red; intros; subst.
          f_equal.
          apply holey_bindings_stratify_aux_equiv; trivial.
        + red; intros envv moreenvv ee ee' dnenvv dnmorenvv disje disjme eeeq holey_bindings' hbsub; simpl.
          rewrite <- eeeq.
          match_case; intros.
          assert (dnd:data_normalized h d)
            by (eapply nnrc_core_eval_normalized; try eapply H; trivial).
          { 
          transitivity (
              nnrc_core_eval h cenv (moreenvv ++ (v, d) :: envv)
                             (stratify_aux e2 required_level (domain moreenvv ++ holey_bindings') holey_expr)).
          - repeat rewrite <- IHe2 with (d:=d); trivial.
            + apply (holey_preserver ((v, d) :: envv) moreenvv); trivial.
              * constructor; trivial.
              * admit. (* I can prove this *) 
              (* simpl.
                apply disjoint_cons1; trivial.
                red in disje.
                symmetry in disje.
                apply disje.
                symmetry in disjbound.
                apply disjoint_cons_inv1 in disjbound.
                rewrite disjoint_app_l in disjbound.
                symmetry; intuition.
   *)
            + rewrite map_app.
              apply Forall_app; simpl; trivial.
              constructor; trivial.
            + admit.
            + admit.
            + apply holey_preserver_bindings_app; trivial.
              eapply holey_preserver_bindings_sublist; eauto.
            + 


              
          apply holey_preserver.
          
          transitivity
            (nnrc_core_eval h cenv ((v, d) :: moreenvv ++ envv)
                            (stratify_aux e2 required_level (domain moreenvv ++ holey_bindings') holey_expr)).
          * { 
              transitivity
                (nnrc_core_eval h cenv (moreenvv ++ (v, d) :: envv) (stratify_aux e2 required_level (domain moreenvv ++ v :: holey_bindings') holey_expr)).
              - repeat rewrite <- IHe2 with (d:=d); trivial.
                + apply (holey_preserver ((v, d) :: envv) moreenvv); intros; simpl; trivial.
                  * constructor; trivial.
                  * apply sublist_skip; trivial.
                + rewrite map_app.
                  apply Forall_app; simpl; trivial.
                  constructor; trivial.
                + apply holey_preserver_bindings_app.
                  apply holey_preserver_bindings_cons.
                  eapply holey_preserver_bindings_sublist; eauto.
                + admit.
                + simpl; constructor; trivial.
                + apply holey_preserver_bindings_cons.
                  eapply holey_preserver_bindings_sublist; eauto.
                + 
            }
          * {
              f_equal.
              apply holey_bindings_stratify_aux_equiv; trivial.
              apply Permutation_equivlist.
              rewrite Permutation_middle; reflexivity.
            }
        - 
            
          

          
          generalize (holey_preserver_stratify holey_preserver required_level); intros hpstratify.
          red in hpstratify.
          
          rewrite  hpstratify.
            
        (holey_expr e holey_bindings')   
        
    Qed.
    Lemma stratify_core_correct h cenv (env:bindings) (e:nnrc) :
      nnrc_core_eval h cenv env e = nnrc_core_eval h cenv env (stratify e).
                                              
    Fixpoint nnrc_core_eval (env:bindings) (e:nnrc) : option data :=
      
        Lemma stratify_aux_stratified
          (e: nnrc) (bindings:list var) (holey_expr:nnrc->list var->nnrc) :
      (forall he hb, stratifiedLevel_spec 0 he -> stratified (holey_expr he hb)) ->
      stratified (stratify_aux e bindings holey_expr).

   *)

  End Correct.

  Section Core.

    Lemma stratify1_aux_preserves_core body required_level hb holey_expr :
      (forall (he : nnrc) (hb : list var),
         nnrcIsCore he -> nnrcIsCore (holey_expr he hb)) ->
      nnrcIsCore body ->
      nnrcIsCore (stratify1_aux body required_level hb holey_expr).
    Proof.
      unfold stratified, stratify1_aux.
      intros hpf ab.
      destruct required_level; simpl; intuition.
      apply hpf; simpl; trivial.
    Qed.
    
    Lemma stratify_aux_preserves_core
          (e: nnrc)
          (required_level:nnrcKind)
          (bindings:list var)
          (holey_expr:nnrc->list var->nnrc) :
      (forall he hb,
          nnrcIsCore he ->
          nnrcIsCore (holey_expr he hb)) ->
      nnrcIsCore e ->
      nnrcIsCore (stratify_aux e required_level bindings holey_expr).
    Proof.
      revert required_level bindings holey_expr.
      induction e; intros required_level bindings holey_expr holey_is_core e_is_core; simpl;
        repeat ((first [
                     apply holey_is_core
                   | apply IHe
                   | apply IHe1
                   | apply IHe2
                   | apply IHe3
                   | apply stratify1_aux_preserves_core
                ]); simpl in *; intuition).
    Qed.

    Theorem stratify_preserves_core e :
      nnrcIsCore e ->  nnrcIsCore (stratify e).
    Proof.
      intros e_is_core.
      apply stratify_aux_preserves_core; trivial.
    Qed.

    Definition stratified_core (e:nnrc_core) : Prop
      := stratified (proj1_sig e).
            
    Definition stratify_core (e:nnrc_core) : nnrc_core
      := exist _ _ (stratify_preserves_core _ (proj2_sig e)).

    Theorem stratify_stratified_core (e: nnrc_core) : stratified_core (stratify_core e).
    Proof.
      apply stratify_stratified.
    Qed.
    
    Theorem stratify_stratify_id_core (e: nnrc_core) :
      stratified_core e ->              
      stratify_core e = e.
    Proof.
      unfold stratified_core, stratify_core.
      intros.
      apply nnrc_core_fequal.
      destruct e; simpl in *.
      apply stratify_stratify_id; trivial.
    Qed.

    Corollary stratify_idem_core (e: nnrc_core) :
      stratify_core (stratify_core e) = stratify_core e.
    Proof.
      apply nnrc_core_fequal; simpl.
      apply stratify_idem.
    Qed.
    
  End Core.
  
End Stratify.

(* 
 *** Local Variables: ***
 *** coq-load-path: (("../../../coq" "Qcert")) ***
 *** End: ***
 *)

