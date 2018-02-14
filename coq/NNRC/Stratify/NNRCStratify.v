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

    Definition stratify (e: nnrc) : nnrc
      := stratify_aux e nnrcStmt nil (fun e _ => e).

  End stratify.
  Section tests.
    Local Open Scope nnrc_scope.
    Local Open Scope string_scope.

    Notation "r1 ‵+ r2" := (NNRCBinop (OpNatBinary NatPlus) r1 r2) (right associativity, at level 65): nnrc_scope.

    Notation "r1 ‵* r2" := (NNRCBinop (OpNatBinary NatMult) r1 r2) (right associativity, at level 65): nnrc_scope.

    Notation "‵abs r" := (NNRCUnop (OpNatUnary NatAbs) r) (right associativity, at level 64): nnrc_scope.

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

  Section Effective.

    Lemma stratify1_aux_stratified body required_level hb holey_expr :
      (forall (he : nnrc) (hb : list var),
          stratifiedLevel required_level he -> stratified (holey_expr he hb)) ->
      stratifiedLevel nnrcStmt body ->
      stratified (stratify1_aux body required_level hb holey_expr).
    Proof.
      unfold stratified, stratify1_aux.
      intros hpf ab.
      destruct required_level; simpl; intuition.
      apply hpf; simpl; trivial.
    Qed.
    
    Lemma stratify_aux_stratified
          (e: nnrc)
          (required_level:nnrcKind)
          (bindings:list var)
          (holey_expr:nnrc->list var->nnrc) :
      (forall he hb,
          stratifiedLevel required_level he ->
          stratified (holey_expr he hb)) ->
      stratified (stratify_aux e required_level bindings holey_expr).
    Proof.
      unfold stratified.
      revert required_level bindings holey_expr.
      induction e; intros required_level bindings holey_expr holey_stratify; simpl;
        repeat ((first [
                     apply holey_stratify
                   | apply IHe
                   | apply IHe1
                   | apply IHe2
                   | apply IHe3
                   | apply stratify1_aux_stratified
                ]); simpl; intuition).
    Qed.

    Theorem stratify_stratified (e: nnrc) : stratified (stratify e).
    Proof.
      apply stratify_aux_stratified; intros.
      apply stratifiedLevel_stratified in H; trivial.
    Qed.

    Corollary stratify_stratified_spec (e: nnrc) : stratified_spec (stratify e).
    Proof.
      apply stratified_correct.
      apply stratify_stratified.
    Qed.

  End Effective.

  Section Idempotent.
    
    Lemma stratify_aux_stratify_id
          (e: nnrc)
          (required_level:nnrcKind)
          (bindings:list var)
          (holey_expr:nnrc->list var->nnrc) :
      stratifiedLevel required_level e ->              
      stratify_aux e required_level bindings holey_expr = holey_expr e bindings.
    Proof.
      revert holey_expr bindings required_level.
      induction e; intros holey_expr bindings required_level stratifylevc
      ; repeat (simpl in *; intuition; subst; first [
                                                  rewrite IHe
                                                | rewrite IHe1
                                                | rewrite IHe2
                                                | rewrite IHe3]
               ).
    Qed.

    Theorem stratify_stratify_id (e: nnrc) :
      stratified e ->              
      stratify e = e.
    Proof.
      intros stratifye.
      apply stratify_aux_stratify_id.
      apply stratifye.
    Qed.

    Corollary stratify_idem (e: nnrc) :
      stratify (stratify e) = stratify e.
    Proof.
      apply stratify_stratify_id.
      apply stratify_stratified.
    Qed.

  End Idempotent.

  Section Correct.
    
    Definition holey_bindings_equiv (holey_expr:nnrc->list var->nnrc) :=
      Proper (eq ==> equivlist ==> eq) holey_expr.

    Lemma stratify1_aux_ext e required_level bindings holey_expr1 holey_expr2 :
      (forall e b, holey_expr1 e b = holey_expr2 e b) ->
      stratify1_aux e required_level bindings holey_expr1 = stratify1_aux e required_level bindings holey_expr2.
    Proof.
      intros; unfold stratify1_aux.
      destruct required_level; congruence.
    Qed.
    
    Lemma stratify_aux_ext e required_level bindings holey_expr1 holey_expr2 :
      (forall e b, holey_expr1 e b = holey_expr2 e b) ->
      stratify_aux e required_level bindings holey_expr1 = stratify_aux e required_level bindings holey_expr2.
    Proof.
      revert required_level bindings holey_expr1 holey_expr2.
      induction e; intros required_level bindings holey_expr1 holey_expr2 ext; simpl; auto 3;
        try solve [((apply IHe1 || apply IHe); intros; (apply stratify1_aux_ext || f_equal); auto)].
    Qed.

    
    Lemma holey_bindings_stratify1_aux_equiv e required_level bindings1 bindings2 holey_expr :
      Proper (eq ==> equivlist ==> eq) holey_expr ->
      equivlist bindings1 bindings2 ->
      stratify1_aux e required_level bindings1 holey_expr = stratify1_aux e required_level bindings2 holey_expr.
    Proof.
      intros.
      unfold stratify1_aux.
      destruct required_level; trivial.
      - assert (fveq:fresh_var "stratify" bindings1 = fresh_var "stratify" bindings2) by (rewrite H0; reflexivity).
        repeat rewrite fveq.
        f_equal; trivial.
        apply H; trivial.
        apply equivlist_cons; trivial.
      - rewrite H0; trivial.
    Qed.

    Lemma stratify1_aux_proper e1 e2 required_level bindings1 bindings2 holey_expr1 holey_expr2 :
      e1 = e2 ->
      Proper (eq ==> equivlist ==> eq) holey_expr1 ->
      equivlist bindings1 bindings2 ->
      (forall e b, holey_expr1 e b = holey_expr2 e b) ->
      stratify1_aux e1 required_level bindings1 holey_expr1 = stratify1_aux e2 required_level bindings2 holey_expr2.
    Proof.
      intros; subst.
      transitivity (stratify1_aux e2 required_level bindings2 holey_expr1).
      - apply holey_bindings_stratify1_aux_equiv; trivial.
      - apply stratify1_aux_ext; trivial.
    Qed.

    Lemma holey_bindings_stratify_aux_equiv e required_level bindings1 bindings2 holey_expr :
      Proper (eq ==> equivlist ==> eq) holey_expr ->
      equivlist bindings1 bindings2 ->
      stratify_aux e required_level bindings1 holey_expr = stratify_aux e required_level bindings2 holey_expr.
    Proof.
      assert (trivprop:Proper (eq ==> equivlist ==> eq) (fun (e : nnrc) (_ : list var) => e)) by (repeat red; tauto).
      revert required_level holey_expr bindings1 bindings2.
      induction e; intros required_level holey_expr bindings1 bindings2 prope eqb; simpl;
        do 2 (repeat (first [rewrite eqb
                            | (erewrite IHe1; try eassumption)
                            | apply stratify_aux_ext
                            | apply stratify1_aux_proper
                            | apply IHe
                            | apply IHe1
                            | apply IHe2
                            | apply IHe3
                            | apply equivlist_cons
                            | apply prope]; unfold Proper, respectful; simpl; intros; subst; auto); f_equal).
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

  (*
    (* our holey contexts preserve contextual equivalence *)
    Definition holey_some_preserver
               h cenv (holey_expr:nnrc->list var -> nnrc) 
      :=
        forall e env d,
          nnrc_core_eval h cenv env e = Some d ->
        forall holey_bindings holey_bindings' moreenv,
          incl holey_bindings holey_bindings' ->
          incl (domain moreenv) holey_bindings' ->
          nnrc_core_eval h cenv env (holey_expr e holey_bindings) =
          nnrc_core_eval h cenv (moreenv++env) (holey_expr (NNRCConst d) holey_bindings').

    Definition holey_none_preserver h cenv (holey_expr:nnrc->list var -> nnrc)  :=
      forall e env holey_bindings,
        nnrc_core_eval h cenv env e = None ->
        nnrc_core_eval h cenv env (holey_expr e holey_bindings) = None.

    Lemma stratify1_aux_core_correct
          h cenv (env:bindings)
          (e:nnrc) (required_level:nnrcKind)
          (holey_bindings:list var) (holey_expr:nnrc->list var->nnrc) :
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      holey_none_preserver h cenv holey_expr ->
      holey_some_preserver h cenv holey_expr ->
      nnrc_core_eval h cenv env (stratify1_aux e required_level holey_bindings holey_expr) =
      nnrc_core_eval h cenv env (holey_expr e holey_bindings).
    Proof.
      intros cenv_normalized env_normalized hnp hsp.
      destruct required_level; simpl; trivial.
      match_case; simpl.
      - intros.
        erewrite (hsp e env d _ _); trivial; try reflexivity.
        simpl.
        erewrite (hsp (NNRCVar (fresh_var "stratify" holey_bindings)) _ d).
        + 
        + simpl. match_destr; congruence.
        + unfold incl; simpl; eauto.
      - intros. rewrite hnp; trivial.
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

