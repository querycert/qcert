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
   nnrs.  As an inbetween step, we can stratify the language, 
   separating expressions and statements.
 *)

Require Import String.
Require Import List.
Require Import Bool.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Permutation.
Require Import Eqdep_dec.
Require Import Program.Basics.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNNRC.
Require Import cNNRCNorm.
Require Import cNNRCVars.
Require Import cNNRCEq.
Require Import cNNRCShadow.
Require Import NNRC.
Require Import NNRCEq.
Require Import NNRCShadow.

Section Stratify.
  
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

    Definition mk_expr_from_vars (nws:nnrc_with_substs) : nnrc
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
    (* Eval vm_compute in (stratify nnrc1).  *)

    Example nnrc2 := NNRCLet "x" nnrc1 (NNRCVar "x").
    (* Eval vm_compute in (stratify nnrc2). *)

    Example nnrc3 := (‵abs (NNRCLet "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8)))) ‵+ ‵(dnat 5)) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))).
    (* Eval vm_compute in (stratify nnrc3). *)

    Example nnrc4 := (‵abs (NNRCFor "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8)))) ‵+ ‵(dnat 5)) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))).
    (*    Eval vm_compute in (stratify nnrc4). *)

    Example nnrc5 := (‵abs (NNRCLet "z" (NNRCFor "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8)))) ‵+ ‵(dnat 5)) (NNRCVar "z")) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))).
    (*    Eval vm_compute in (stratify nnrc5). *)

    Example nnrc6 := (‵abs (NNRCLet "z" (NNRCFor "x" ((‵(dnat 1) ‵+ ‵(dnat 2))) (((NNRCVar "x" ‵+ ‵(dnat 8))))) (NNRCVar "z")) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3))).
    (* Eval vm_compute in (stratify nnrc6). *)

    Example nnrc7 := NNRCLet "x" (NNRCLet "y" ‵(dnat 3) (‵(dnat 8) ‵+ (NNRCVar "y"))) (NNRCVar "x").
    
    (* Eval vm_compute in (stratify nnrc7). *)

    Example nnrc8 := NNRCLet "x" (NNRCLet "x" ‵(dnat 3) (‵(dnat 8) ‵+ (NNRCVar "x"))) (NNRCVar "x").
    
    (* Eval vm_compute in (stratify nnrc8). *)

  End tests.

  Lemma Forall_app_iff {A} (P:A->Prop) l1 l2 :
      Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
    Proof.
      split; intros.
      - apply Forall_app_inv in H; trivial.
      - apply Forall_app; tauto.
    Qed.

  Ltac list_simpler :=
    repeat progress (
             try match goal with
                 | [H: ?l  = ?l ++ _ |- _ ] => apply app_inv_self_l in H; try subst
                 | [H: ?l  = _ ++ ?l  |- _ ] => apply app_inv_self_r in H; try subst
                 | [H: ?l ++ _ = ?l ++ _ |- _ ] => apply app_inv_head in H; try subst
                 | [H: _ ++ ?l  = _ ++ ?l |- _ ] => apply app_inv_tail in H; try subst
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
             ; repeat rewrite in_app_iff in *
             ; repeat rewrite Forall_app_iff in *
           ).
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
        specialize (IHe _ _ _ _ eqq1).
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

    Lemma mk_expr_stratify_aux_free_vars e required_kind bound_vars :
      incl (nnrc_free_vars e) bound_vars ->
      equivlist (nnrc_free_vars (mk_expr_from_vars (stratify_aux e required_kind bound_vars))) (nnrc_free_vars e).
    Proof.
      unfold stratify.
      intros inclb.
      case_eq (stratify_aux e required_kind bound_vars); intros n sdefs eqq1.
      destruct (stratify_aux_free_vars_and_growing eqq1 inclb)
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
        specialize (disj x); intuition.
    Qed.
    
    Theorem stratify_free_vars e :
      equivlist (nnrc_free_vars (stratify e)) (nnrc_free_vars e).
    Proof.
      apply mk_expr_stratify_aux_free_vars.
      reflexivity.
    Qed.

  End FreeVars.

  Section Eval_substs.
    (* This is a monadic fold_left, whereas mk_expr_from_vars is a fold_right.
        This is because evaluation goes outside in, whereas we build the let-bindings
        from the inside out.
     *)

    Fixpoint eval_substs h cenv (sdefs:list (var*nnrc)) (env:bindings): option bindings
      := match sdefs with
         | nil => Some env
         | (v,n)::sdefs' =>
           olift (fun d => eval_substs h cenv sdefs' ((v,d)::env))
                 (@nnrc_eval _ h cenv env n)
         end.

    Definition eval_nnrc_with_substs h cenv env nws :=
      olift (fun env' => @nnrc_eval _ h cenv env' (fst nws))
            (eval_substs h cenv (snd nws) env).

    Lemma eval_nnrc_with_substs_eq h cenv env a b :
      olift (fun env' => @nnrc_eval _ h cenv env' a)
            (eval_substs h cenv b env) = eval_nnrc_with_substs h cenv env (a,b).
    Proof.
      reflexivity.
    Qed.

    Lemma eval_nnrc_with_substs_eq_core h cenv env a b :
      olift (fun env' => @nnrc_core_eval _ h cenv env' (nnrc_to_nnrc_base a))
            (eval_substs h cenv b env) = eval_nnrc_with_substs h cenv env (a,b).
    Proof.
      reflexivity.
    Qed.

    Lemma mk_expr_from_vars_eval h cenv env nws :
      @nnrc_eval _ h cenv env
                 (mk_expr_from_vars nws) = 
      eval_nnrc_with_substs h cenv env nws.
    Proof.
      unfold eval_nnrc_with_substs, mk_expr_from_vars.
      destruct nws as [n sdefs].
      revert env n.
      induction sdefs; intros env n; simpl; trivial.
      unfold nnrc_eval in *.
      destruct a; simpl in *.
      match_case; intros ? eqq; simpl.
      rewrite IHsdefs; trivial.
    Qed.

    Lemma eval_substs_app h cenv (sdefs1 sdefs2:list (var*nnrc)) (env:bindings) :
      eval_substs h cenv (sdefs1++sdefs2) env = olift (eval_substs h cenv sdefs2) (eval_substs h cenv sdefs1 env).
    Proof.
      revert sdefs2 env.
      induction sdefs1; intros sdefs2 env; simpl; trivial.
      destruct a; simpl.
      destruct (@nnrc_eval _ h cenv env n); simpl; trivial.
    Qed.

    Lemma eval_substs_applies {h cenv sdefs env res} :
      eval_substs h cenv sdefs env = Some res ->
      {x | res = x++env & domain x = rev (domain sdefs)}.
    Proof.
      revert env res.
      induction sdefs; intros env res eqq; invcs eqq; simpl.
      - exists nil; simpl; eauto.
      - destruct a.
        destruct (@nnrc_eval _ h cenv env n); simpl in *; try discriminate.
        destruct (IHsdefs _ _ H0) as [x ? eqd].
        exists (x++(v,d)::nil).
        + subst. rewrite app_ass; simpl; reflexivity.
        + rewrite domain_app, eqd; simpl; reflexivity.
    Qed.

    Lemma eval_substs_lookup_equiv_on_env
          h cenv sdefs {l env1 env2}:
      lookup_equiv_on l env1 env2 ->
      incl (concat (map nnrc_free_vars (codomain sdefs))) l ->
      match eval_substs h cenv sdefs env1, eval_substs h cenv sdefs env2 with
      | Some e1, Some e2 => lookup_equiv_on l e1 e2
      | None, None => True
      | _, _ => False
      end.
    Proof.
      revert env1 env2; induction sdefs; simpl; trivial.
      destruct a; intros env1 env2 leqq inclu.
      apply incl_app_iff in inclu.
      destruct inclu as [inclu1 inclu2].
      simpl in *.
      assert (eqqs:@nnrc_eval _ h cenv env1 n = @nnrc_eval _ h cenv env2 n).
      { apply nnrc_eval_equiv_free_in_env; eauto. } 
      rewrite <- eqqs.
      case_eq (@nnrc_eval _ h cenv env1 n); simpl; trivial.
      intros d eqq1.
      apply IHsdefs; trivial.
      apply lookup_equiv_on_cons_same; trivial.
    Qed.

    Lemma eval_substs_lookup_equiv_env {h cenv sdefs env1 env2}:
      lookup_equiv env1 env2 ->
      match eval_substs h cenv sdefs env1, eval_substs h cenv sdefs env2 with
      | Some e1, Some e2 => lookup_equiv e1 e2
      | None, None => True
      | _, _ => False
      end.
    Proof.
      revert env1 env2; induction sdefs; simpl; trivial.
      destruct a; intros env1 env2 leqq.
      assert (eqqs:@nnrc_eval _ h cenv env1 n = @nnrc_eval _ h cenv env2 n) by (apply nnrc_eval_equiv_env; eauto).
      rewrite <- eqqs.
      case_eq (@nnrc_eval _ h cenv env1 n); simpl; trivial.
      intros d eqq1.
      apply IHsdefs.
      apply lookup_equiv_cons_same; trivial.      
    Qed.

    Lemma eval_substs_disjoint_swap_env
          h cenv sdefs env₁ env₂ x₁ d₁ x₂ d₂ :
      x₁ <> x₂ ->
      match eval_substs h cenv sdefs (env₁++(x₁,d₁)::(x₂,d₂)::env₂)
            ,  eval_substs h cenv sdefs (env₁++(x₂,d₂)::(x₁,d₁)::env₂) with
      | Some res₁, Some res₂ =>
        {env' | res₁ = env' ++  env₁++((x₁,d₁)::(x₂,d₂)::env₂) & res₂ = env' ++ env₁ ++ ((x₂,d₂)::(x₁,d₁)::env₂)}
      | None, None => True
      | _, _ => False
      end.
    Proof.
      intros neq.
      revert env₁.
      induction sdefs; intros env₁ ; simpl.
      - exists nil; simpl; reflexivity.
      - destruct a.
        generalize (@nnrc_eval_swap_neq _ h cenv env₁ x₁ d₁ x₂ d₂); simpl; intros HH.
        rewrite HH by trivial.
        destruct (@nnrc_eval _ h cenv (env₁ ++ (x₂, d₂) :: (x₁, d₁) :: env₂) n)
        ; simpl; trivial.
        specialize (IHsdefs ((v,d)::env₁)).
        simpl in IHsdefs.
        unfold var in *.
        repeat match_destr.
        destruct IHsdefs as [env' eqq1 eqq2].
        exists ( env' ++ (v, d)::nil); rewrite app_ass; simpl; trivial.
    Qed.

    Lemma eval_substs_disjoint_cons_env h cenv sdefs x d :
      ~ In x (domain sdefs) ->
      ~ In x (concat (map nnrc_free_vars (codomain sdefs))) ->
      forall env,
        match eval_substs h cenv sdefs env
              , eval_substs h cenv sdefs ((x,d)::env) with
        | Some res₁, Some res₂ => {env' | res₁ = env' ++ env & res₂ = env' ++ (x,d)::env}
        | None, None => True
        | _, _ => False
        end.
    Proof.
      induction sdefs; simpl; intros nin1 nin2 env.
      - exists nil; simpl; reflexivity.
      - destruct a; simpl in *.
        list_simpler.
        apply notand in nin1.
        apply notand in nin2.
        destruct nin1 as [nin11 nin12].
        destruct nin2 as [nin21 nin22].
        assert (@nnrc_eval _ h cenv ((x, d) :: env) n =
                @nnrc_eval _ h cenv env n).
        { apply nnrc_eval_equiv_free_in_env.
          intros ? inn; simpl.
          match_destr.
          unfold equiv in *; congruence.
        }
        rewrite H; simpl.
        destruct (@nnrc_eval _ h cenv env n); simpl; trivial.
        specialize (IHsdefs nin12 nin22 ((v, d0) :: env)).
        generalize (eval_substs_disjoint_swap_env
                      h cenv sdefs nil env v d0 x d nin11); intros HH.
        simpl in HH.
        unfold var in*.
        repeat match_destr; repeat match_destr_in HH; try tauto.
        destruct IHsdefs as [env' eqq1 eqq2].
        destruct HH as [env'' eqq3 eqq4].
        subst.
        list_simpler.
        exists (env'' ++ (v, d0) :: nil); rewrite app_ass; simpl; reflexivity.
    Qed.
    
    Lemma eval_substs_disjoint_middle_some h cenv sdefs env' :
      disjoint (domain sdefs) (domain env') ->
      disjoint (concat (map nnrc_free_vars (codomain sdefs))) (domain env') ->
      forall env,
        match eval_substs h cenv sdefs env
              , eval_substs h cenv sdefs (env' ++ env) with
        | Some res₁, Some res₂ => {env'' | res₁ = env'' ++ env & res₂ = env'' ++ env' ++ env}
        | None, None => True
        | _, _ => False
        end.
    Proof.
      induction env'; simpl; intros disj1 disj2 env.
      - match_case; intros.
        apply eval_substs_applies in H.
        destruct H as [env'' ? ?]; subst.
        exists env''; simpl; trivial.
      - apply disjoint_cons_inv2 in disj1.
        destruct disj1 as [disj1 nin1].
        apply disjoint_cons_inv2 in disj2.
        destruct disj2 as [disj2 nin2].
        destruct a; simpl in *.
        specialize (IHenv' disj1 disj2).
        specialize (IHenv' env).
        generalize (eval_substs_disjoint_cons_env h cenv sdefs v d nin1 nin2 (env'++env))
        ; intros HH.
        repeat match_option_in HH; 
          rewrite eqq in *; try tauto.
        match_option_in IHenv'.
        destruct IHenv' as [env'1 ? ?].
        destruct HH as [env'2 ? ?].
        subst.
        list_simpler.
        exists (env'2); trivial.
    Qed.

    Lemma mk_expr_from_vars_eq_expr {n1 n2} :
      nnrc_eq n1 n2 ->
      forall sdefs,
        nnrc_eq (mk_expr_from_vars (n1, sdefs)) (mk_expr_from_vars (n2, sdefs)).
    Proof.
      unfold mk_expr_from_vars, nnrc_eq, nnrc_eval.
      intros eqq sdefs; revert n1 n2 eqq.
      induction sdefs; intros n1 n2 eqq; simpl; trivial; intros.
      match_case; intros ? inn.
      apply IHsdefs; trivial.
      simpl; constructor; trivial.
      eapply nnrc_core_eval_normalized; try eapply inn; eauto.
    Qed.

  End Eval_substs.

  Section Correct.

    Opaque fresh_var.
    Lemma stratify1_aux_correct h cenv env e bound_vars required_kind sdefs :
      eval_nnrc_with_substs h cenv env (stratify1_aux e required_kind bound_vars sdefs) =
      eval_nnrc_with_substs h cenv env (e,sdefs).
    Proof.
      intros.
      destruct required_kind; simpl; trivial.
      unfold eval_nnrc_with_substs; simpl.
      rewrite eval_substs_app; simpl.
      destruct (eval_substs h cenv sdefs env); simpl; trivial.
      destruct (@nnrc_eval _ h cenv b e); simpl; trivial.
      unfold nnrc_eval; simpl.
      match_destr.
      congruence.
    Qed.

    Lemma eval_substs_normalized {h cenv env sdefs env'} :
      eval_substs h cenv sdefs env = Some env' ->
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      Forall (data_normalized h) (map snd env').
    Proof.
      revert env env'.
      induction sdefs; simpl; intros env env' eqq1 FDce FDe.
      - invcs eqq1; trivial.
      - destruct a.
        apply some_olift in eqq1.
        destruct eqq1 as [d eqq2 eqq3].
        unfold nnrc_eval in eqq2.
        apply nnrc_core_eval_normalized in eqq2; trivial.
        symmetry in eqq3.
        apply (IHsdefs _ _ eqq3); trivial.
        constructor; trivial.
    Qed.
    
    Lemma stratify_aux_correct h cenv env e bound_vars required_kind :
      incl (nnrc_free_vars e) bound_vars ->
      @nnrc_eval _ h cenv env (mk_expr_from_vars (stratify_aux e required_kind bound_vars)) =
      @nnrc_eval _ h cenv env e.
    Proof.
      rewrite mk_expr_from_vars_eval.
      unfold eval_nnrc_with_substs.
      unfold nnrc_eval.
      revert required_kind bound_vars env.
      induction e; intros required_kind bound_vars env fbincl; simpl; trivial.
      - repeat (match_case; intros); simpl.
        simpl in fbincl.
        apply incl_app_iff in fbincl.
        destruct fbincl as [fbincl1 fbincl2].
        rewrite <- (IHe1 nnrcExpr bound_vars) by trivial.
        rewrite <- (IHe2 nnrcExpr (domain l ++ bound_vars)); trivial;
          try (apply incl_appr; trivial); simpl.
        clear IHe1 IHe2.
        rewrite H, H0; simpl.
        rewrite eval_substs_app.
        unfold olift.
        case_eq (eval_substs h cenv l env); simpl; trivial
        ; intros ? eqq1.
        destruct (eval_substs_applies eqq1) as [env' ? eqdom]; subst.
        generalize (eval_substs_disjoint_middle_some h cenv l0 env'); intros HH.
        generalize (stratify_aux_free_vars H fbincl1); intros fequiv1.
        generalize (stratify_aux_free_vars H0); intros fequiv2.
        cut_to fequiv2; try (apply incl_appr; trivial).
        generalize (stratify_aux_nbound_vars H); intros nb1.
        generalize (stratify_aux_nbound_vars H0); intros nb2.
        apply disjoint_app_r in nb2.
        destruct nb2 as [nb2 nb3].
        assert (disj1: disjoint (domain l0) (domain env')).
        { unfold var in *.
          rewrite eqdom, disjoint_rev_r; tauto.
        }
        assert (disj2:disjoint (concat (map nnrc_free_vars (codomain l0))) (domain env')).
        {
          intros x inn1 inn2.
          generalize (fequiv2 x); list_simpler; intros [impf _].
          cut_to impf; [| tauto].
          rewrite eqdom, <- in_rev in inn2.
          destruct impf as [inn3|inn3]; eauto.
        }
        specialize (HH disj1 disj2 env).
        unfold var in *.
        repeat match_option_in HH; try rewrite olift2_none_r; try tauto.
        destruct HH as [env'' eeqq1 eeqq2].
        subst.
        f_equal.
        + repeat rewrite <- nnrc_to_nnrc_base_eq.
          apply nnrc_eval_equiv_free_in_env; intros.
          destruct (eval_substs_applies eqq) as [env''' ? eqdom2]; subst.
          list_simpler.
          rewrite lookup_app.
          rewrite (lookup_nin_none _ (l:=env''')); trivial.
          rewrite eqdom2, <- in_rev.
          generalize (fequiv1 x); list_simpler; intros [impf _].
          cut_to impf; [| tauto].
          destruct impf as [inn3|inn3]; eauto.
        + repeat rewrite <- nnrc_to_nnrc_base_eq.
          apply nnrc_eval_equiv_free_in_env; intros.
          repeat rewrite lookup_app.
          match_destr.
          rewrite (lookup_nin_none _ (l:=env')); trivial.
          rewrite eqdom, <- in_rev.
          generalize (fequiv2 x); list_simpler; intros [impf _].
          cut_to impf; [| tauto].
          destruct impf as [inn3|inn3]; eauto.
      - repeat (match_case; intros); simpl in *.
        specialize (IHe nnrcExpr _ env fbincl).
        rewrite <- IHe; simpl.
        rewrite H.
        simpl.
        unfold olift.
        match_option.
      - rewrite eval_nnrc_with_substs_eq_core.
        rewrite <- surjective_pairing.
        rewrite stratify1_aux_correct.
        unfold eval_nnrc_with_substs; simpl.
        simpl in fbincl.
        apply incl_app_iff in fbincl.
        destruct fbincl as [fbincl1 fbincl2].
        apply incl_remove in fbincl2.
        specialize (IHe1 nnrcStmt _ env fbincl1).
        unfold nnrc_eval; simpl; repeat rewrite <- nnrc_to_nnrc_base_eq.
        rewrite mk_expr_from_vars_eval.
        unfold eval_nnrc_with_substs, nnrc_eval; rewrite IHe1.
        match_option.
        specialize (IHe2 nnrcStmt _ ((v,d)::env) fbincl2).
        repeat rewrite <- nnrc_to_nnrc_base_eq.
        rewrite mk_expr_from_vars_eval.
        unfold eval_nnrc_with_substs, nnrc_eval; rewrite IHe2.
        trivial.
      - rewrite eval_nnrc_with_substs_eq_core.
        rewrite <- surjective_pairing.
        case_eq (stratify_aux e1 nnrcExpr bound_vars); intros e1' sdefs1 eqq1.
        rewrite stratify1_aux_correct.
        unfold eval_nnrc_with_substs; simpl.
        simpl in fbincl.
        apply incl_app_iff in fbincl.
        destruct fbincl as [fbincl1 fbincl2].
        apply incl_remove in fbincl2.
        specialize (IHe1 nnrcExpr _ env fbincl1).
        rewrite <- IHe1; clear IHe1.
        rewrite eqq1; simpl.
        case_eq (eval_substs h cenv sdefs1 env); simpl; trivial.
        intros env'' eqq2.
        unfold nnrc_eval; simpl; repeat rewrite <- nnrc_to_nnrc_base_eq.
        match_option.
        destruct d; simpl; trivial.
        f_equal.
        apply lift_map_ext; intros.
        specialize (IHe2 nnrcStmt _ ((v,x)::env'') fbincl2 ).
        repeat rewrite <- nnrc_to_nnrc_base_eq.
        rewrite mk_expr_from_vars_eval.
        unfold eval_nnrc_with_substs, nnrc_eval; rewrite IHe2.
        destruct (eval_substs_applies eqq2) as [env' ? eqdom]; subst.
        apply nnrc_core_eval_equiv_free_in_env; intros z zin.
        simpl.
        destruct (equiv_dec z v); trivial.
        unfold equiv, complement in *.
        rewrite lookup_app.
        generalize (stratify_aux_free_vars eqq1); intros fequiv1.
        generalize (stratify_aux_nbound_vars eqq1); intros nb1.
        assert (ninz:~ In z (domain env')).
        {         
          rewrite <- disjoint_rev_l in nb1.
          rewrite <- eqdom in nb1.
          specialize (nb1 z).
          intros nin2; apply nb1; trivial.
          rewrite <- nnrc_to_nnrc_base_free_vars_same in zin.
          specialize (fbincl2 _ zin).
          simpl in fbincl2; intuition.
        }
        rewrite (lookup_nin_none _ ninz); trivial.
      - rewrite eval_nnrc_with_substs_eq_core.
        rewrite <- surjective_pairing.
        case_eq (stratify_aux e1 nnrcExpr bound_vars); intros e1' sdefs1 eqq1.
        rewrite stratify1_aux_correct.
        unfold eval_nnrc_with_substs; simpl.
        simpl in fbincl.
        apply incl_app_iff in fbincl.
        destruct fbincl as [fbincl1 fbincl2].
        apply incl_app_iff in fbincl2.
        destruct fbincl2 as [fbincl2 fbincl3].
        specialize (IHe1 nnrcExpr _ env fbincl1).
        rewrite <- IHe1; clear IHe1.
        rewrite eqq1; simpl.
        case_eq (eval_substs h cenv sdefs1 env); simpl; trivial.
        intros env'' eqq2.
        unfold nnrc_eval; simpl; repeat rewrite <- nnrc_to_nnrc_base_eq.
        apply olift_ext; intros d eqq3.
        destruct d; simpl; trivial.
        destruct (eval_substs_applies eqq2) as [env' ? eqdom]; subst.
        generalize (stratify_aux_free_vars eqq1); intros fequiv1.
        generalize (stratify_aux_nbound_vars eqq1); intros nb1.
        rewrite <- disjoint_rev_l in nb1.
        rewrite <- eqdom in nb1.
        destruct b.
        + rewrite mk_expr_from_vars_eval.
          unfold eval_nnrc_with_substs, nnrc_eval; rewrite IHe2; trivial.
          apply nnrc_core_eval_equiv_free_in_env; intros z zin.
          rewrite lookup_app.
          assert (ninz:~ In z (domain env')).
          {         
            specialize (nb1 z).
            intros nin2; apply nb1; trivial.
            rewrite <- nnrc_to_nnrc_base_free_vars_same in zin.
            specialize (fbincl2 _ zin).
            simpl in fbincl2; intuition.
          }
          rewrite (lookup_nin_none _ ninz); trivial.
        + rewrite mk_expr_from_vars_eval.
          unfold eval_nnrc_with_substs, nnrc_eval; rewrite IHe3; trivial.
          apply nnrc_core_eval_equiv_free_in_env; intros z zin.
          rewrite lookup_app.
          assert (ninz:~ In z (domain env')).
          {         
            specialize (nb1 z).
            intros nin2; apply nb1; trivial.
            rewrite <- nnrc_to_nnrc_base_free_vars_same in zin.
            specialize (fbincl3 _ zin).
            simpl in fbincl2; intuition.
          }
          rewrite (lookup_nin_none _ ninz); trivial.
      - rewrite eval_nnrc_with_substs_eq_core.
        rewrite <- surjective_pairing.
        case_eq (stratify_aux e1 nnrcExpr bound_vars); intros e1' sdefs1 eqq1.
        rewrite stratify1_aux_correct.
        unfold eval_nnrc_with_substs; simpl.
        simpl in fbincl.
        apply incl_app_iff in fbincl.
        destruct fbincl as [fbincl1 fbincl2].
        apply incl_app_iff in fbincl2.
        destruct fbincl2 as [fbincl2 fbincl3].
        apply incl_remove in fbincl2.
        apply incl_remove in fbincl3.
        specialize (IHe1 nnrcExpr _ env fbincl1).
        rewrite <- IHe1; clear IHe1.
        rewrite eqq1; simpl.
        case_eq (eval_substs h cenv sdefs1 env); simpl; trivial.
        intros env'' eqq2.
        unfold nnrc_eval; simpl; repeat rewrite <- nnrc_to_nnrc_base_eq.
        apply olift_ext; intros d eqq3.
        destruct (eval_substs_applies eqq2) as [env' ? eqdom]; subst.
        generalize (stratify_aux_free_vars eqq1); intros fequiv1.
        generalize (stratify_aux_nbound_vars eqq1); intros nb1.
        rewrite <- disjoint_rev_l in nb1.
        rewrite <- eqdom in nb1.
        destruct d; simpl; trivial.
        + repeat rewrite <- nnrc_to_nnrc_base_eq.
          rewrite mk_expr_from_vars_eval.
          unfold eval_nnrc_with_substs, nnrc_eval; rewrite IHe2; simpl; trivial.
          * apply nnrc_core_eval_equiv_free_in_env; intros z zin.
            simpl. destruct (equiv_dec z v); simpl; trivial.
            unfold equiv, complement in *.
            rewrite lookup_app.
            assert (ninz:~ In z (domain env')).
            {         
              specialize (nb1 z).
              intros nin2; apply nb1; trivial.
              rewrite <- nnrc_to_nnrc_base_free_vars_same in zin.
              specialize (fbincl2 _ zin).
              simpl in fbincl2; intuition.
            }
            rewrite (lookup_nin_none _ ninz); trivial.
        + repeat rewrite <- nnrc_to_nnrc_base_eq.
          rewrite mk_expr_from_vars_eval.
          unfold eval_nnrc_with_substs, nnrc_eval; rewrite IHe3; simpl; trivial.
          * apply nnrc_core_eval_equiv_free_in_env; intros z zin.
            simpl. destruct (equiv_dec z v0); simpl; trivial.
            unfold equiv, complement in *.
            rewrite lookup_app.
            assert (ninz:~ In z (domain env')).
            {         
              specialize (nb1 z).
              intros nin2; apply nb1; trivial.
              rewrite <- nnrc_to_nnrc_base_free_vars_same in zin.
              specialize (fbincl3 _ zin).
              simpl in fbincl3; intuition.
            }
            rewrite (lookup_nin_none _ ninz); trivial.
      - rewrite eval_nnrc_with_substs_eq_core.
        rewrite <- surjective_pairing.
        case_eq (stratify_aux e nnrcExpr bound_vars); intros e1' sdefs1 eqq1.
        rewrite stratify1_aux_correct.
        unfold eval_nnrc_with_substs; simpl.
        specialize (IHe nnrcExpr _ env fbincl).
        rewrite <- IHe; clear IHe.
        rewrite eqq1; simpl.
        case_eq (eval_substs h cenv sdefs1 env); simpl; trivial.
    Qed.

    Theorem stratify_correct h cenv env e :
      @nnrc_eval _ h cenv env (stratify e) =
      @nnrc_eval _ h cenv env e.
    Proof.
      apply stratify_aux_correct; trivial.
      reflexivity.
    Qed.

    (* Note that this is weaker then stratify_correct, since 
       it requires that the environments be normalized.
       However, it looks prettier :-)
     *) 
    Theorem stratify_correct_eq e :
      nnrc_eq (stratify e) e.
    Proof.
      red; intros h cenv env FDce FDe.
      apply stratify_aux_correct; trivial.
      reflexivity.
    Qed.

  End Correct.

  Section Core.

    Lemma stratify1_aux_preserves_core 
          {e required_level bound_vars n}
          {sdefs1 sdefs2:list (var*nnrc)} :
      stratify1_aux e required_level bound_vars sdefs1 = (n, sdefs2) ->
      nnrcIsCore e /\ Forall nnrcIsCore (codomain sdefs1) <->
      nnrcIsCore n /\ Forall nnrcIsCore (codomain sdefs2).
    Proof.
      intros eqq1.
      destruct required_level; simpl in *
      ; invcs eqq1; list_simpler; simpl; intuition.
      invcs H2; trivial.
    Qed.

    Lemma mk_expr_from_vars_preserves_core nws :
      (nnrcIsCore (fst nws) /\ Forall nnrcIsCore (codomain (snd nws))) <->
      nnrcIsCore (mk_expr_from_vars nws).
    Proof.
      unfold mk_expr_from_vars.
      destruct nws as [e sdefs].
      revert e.
      induction sdefs; simpl in *.
      - intuition.
      - intros e; split; intros eqqs.
        + destruct eqqs as [isc1 isc2].
          invcs isc2.
          split; trivial.
          rewrite <- IHsdefs; tauto.
        + destruct eqqs as [isc1 isc2].
           rewrite <- IHsdefs in isc2.
           intuition.
    Qed.
    
    Lemma stratify_aux_preserves_core
          {e required_level bound_vars n sdefs} :
      stratify_aux e required_level bound_vars = (n,sdefs) ->
      nnrcIsCore e <->
      nnrcIsCore n /\ Forall nnrcIsCore (codomain sdefs).
    Proof.
      Hint Resolve Forall_nil.
      revert required_level bound_vars n sdefs.
      induction e; intros required_level bound_vars n sdefs eqq1
      ; simpl in *; invcs eqq1; simpl.
      - intuition.
      - intuition.
      - intuition.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        match_case_in H0; intros ? ? eqq2; rewrite eqq2 in H0.
        invcs H0; simpl in *.
        list_simpler.
        destruct (IHe1 _ _ _ _ eqq1).
        destruct (IHe2 _ _ _ _ eqq2).
        intuition.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        invcs H0; simpl in *.
        destruct (IHe _ _ _ _ eqq1).
        intuition.
      - rewrite <- (stratify1_aux_preserves_core H0).
        simpl.
        repeat rewrite <- mk_expr_from_vars_preserves_core.
        case_eq (stratify_aux e1 nnrcStmt bound_vars); intros ? ? eqq1; simpl.
        case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2; simpl.
        destruct (IHe1 _ _ _ _ eqq1).
        destruct (IHe2 _ _ _ _ eqq2).
        intuition.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        destruct (IHe1 _ _ _ _ eqq1).
        rewrite <- (stratify1_aux_preserves_core H0).
        simpl.
        case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2; simpl.
        destruct (IHe2 _ _ _ _ eqq2).
        rewrite <- mk_expr_from_vars_preserves_core.
        simpl; intuition.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        destruct (IHe1 _ _ _ _ eqq1).
        rewrite <- (stratify1_aux_preserves_core H0).
        simpl.
        case_eq (stratify_aux e2 nnrcStmt bound_vars); intros ? ? eqq2; simpl.
        case_eq (stratify_aux e3 nnrcStmt bound_vars); intros ? ? eqq3; simpl.
        destruct (IHe2 _ _ _ _ eqq2).
        destruct (IHe3 _ _ _ _ eqq3).
        repeat rewrite <- mk_expr_from_vars_preserves_core.
        intuition.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        destruct (IHe1 _ _ _ _ eqq1).
        rewrite <- (stratify1_aux_preserves_core H0).
        simpl.
        case_eq (stratify_aux e2 nnrcStmt (v::bound_vars)); intros ? ? eqq2; simpl.
        case_eq (stratify_aux e3 nnrcStmt (v0::bound_vars)); intros ? ? eqq3; simpl.
        destruct (IHe2 _ _ _ _ eqq2).
        destruct (IHe3 _ _ _ _ eqq3).
        repeat rewrite <- mk_expr_from_vars_preserves_core.
        intuition.
      - match_case_in H0; intros ? ? eqq1; rewrite eqq1 in H0.
        rewrite <- (stratify1_aux_preserves_core H0).
        simpl; intuition.
    Qed.

    Theorem stratify_preserves_core e :
      nnrcIsCore e <->  nnrcIsCore (stratify e).
    Proof.
      unfold stratify.
      case_eq (stratify_aux e nnrcStmt (nnrc_free_vars e)); intros ? ? eqq1.
      rewrite <- mk_expr_from_vars_preserves_core.
      apply stratify_aux_preserves_core in eqq1; trivial.
    Qed.

    Definition stratified_core (e:nnrc_core) : Prop
      := stratified (proj1_sig e).
    
    Definition stratify_core (e:nnrc_core) : nnrc_core
      := exist _ _ (proj1 (stratify_preserves_core _) (proj2_sig e)).

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

