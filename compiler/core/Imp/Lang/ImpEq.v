(*
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
Require Import ZArith.
Require Import Bool.
Require Import Compare_dec.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import Imp.
Require Import ImpEval.

Section NNRSimpEq.
  (* Equivalence for imp *)

  Local Open Scope imp_scope.

  Context {Model: Type}.
  Context {Constant: Type}.
  Context {Op: Type}.
  Context {Runtime: Type}.

  Context {ConstantNormalize: Constant -> Model}.
  Context {ModelToBool: Model -> option bool}.
  Context {ModelToZ: Model -> option Z}.
  Context {ModelToList: Model -> option (list Model)}.
  Context {ZToModel: Z -> Model}.

  Context {RuntimeEval: Runtime -> list Model -> option Model}.
  Context {OpEval: Op -> list Model -> option Model}.

  Definition imp_expr_eq (e₁ e₂:imp_expr) : Prop :=
    forall (σ:pd_rbindings),
      imp_expr_eval
        (ConstantNormalize:=ConstantNormalize)
        (OpEval:=OpEval)
        (RuntimeEval:=RuntimeEval) σ e₁ =
      imp_expr_eval
        (ConstantNormalize:=ConstantNormalize)
        (OpEval:=OpEval)
        (RuntimeEval:=RuntimeEval) σ e₂.

  Definition imp_expr_list_eq (el₁ el₂:list imp_expr) : Prop :=
      Forall2 (fun e₁ e₂ =>
                 forall (σ:pd_rbindings),
                   imp_expr_eval
                     (ConstantNormalize:=ConstantNormalize)
                     (OpEval:=OpEval)
                     (RuntimeEval:=RuntimeEval) σ e₁ =
                   imp_expr_eval
                     (ConstantNormalize:=ConstantNormalize)
                     (OpEval:=OpEval)
                     (RuntimeEval:=RuntimeEval) σ e₂) el₁ el₂.

  Definition imp_stmt_eq (s₁ s₂:imp_stmt) : Prop :=
    forall (σ:pd_rbindings),
      imp_stmt_eval
        (ConstantNormalize:=ConstantNormalize)
        (OpEval:=OpEval)
        (RuntimeEval:=RuntimeEval)
        (ModelToBool:=ModelToBool)
        (ModelToZ:=ModelToZ)
        (ModelToList:=ModelToList)
        (ZToModel:=ZToModel) s₁ σ =
      imp_stmt_eval
        (ConstantNormalize:=ConstantNormalize)
        (OpEval:=OpEval)
        (RuntimeEval:=RuntimeEval)
        (ModelToBool:=ModelToBool)
        (ModelToZ:=ModelToZ)
        (ModelToList:=ModelToList)
        (ZToModel:=ZToModel) s₂ σ.

  Definition imp_function_eq (f₁ f₂:imp_function) : Prop :=
    forall (d:Model),
      imp_function_eval
        (ConstantNormalize:=ConstantNormalize)
        (OpEval:=OpEval)
        (RuntimeEval:=RuntimeEval)
        (ModelToBool:=ModelToBool)
        (ModelToZ:=ModelToZ)
        (ModelToList:=ModelToList)
        (ZToModel:=ZToModel) f₁ d
      = imp_function_eval
        (ConstantNormalize:=ConstantNormalize)
        (OpEval:=OpEval)
        (RuntimeEval:=RuntimeEval)
        (ModelToBool:=ModelToBool)
        (ModelToZ:=ModelToZ)
        (ModelToList:=ModelToList)
        (ZToModel:=ZToModel) f₂ d.

  Definition imp_eq (q₁ q₂:imp) : Prop :=
    forall (d:Model),
      imp_eval
        (ConstantNormalize:=ConstantNormalize)
        (OpEval:=OpEval)
        (RuntimeEval:=RuntimeEval)
        (ModelToBool:=ModelToBool)
        (ModelToZ:=ModelToZ)
        (ModelToList:=ModelToList)
        (ZToModel:=ZToModel) q₁ d
      = imp_eval
        (ConstantNormalize:=ConstantNormalize)
        (OpEval:=OpEval)
        (RuntimeEval:=RuntimeEval)
        (ModelToBool:=ModelToBool)
        (ModelToZ:=ModelToZ)
        (ModelToList:=ModelToList)
        (ZToModel:=ZToModel) q₂ d.

  Global Instance imp_expr_equiv : Equivalence imp_expr_eq.
  Proof.
    unfold imp_expr_eq.
    constructor; red; intros.
    - reflexivity.
    - symmetry; eauto.
    - rewrite H; eauto. 
  Qed.

  Global Instance imp_expr_list_equiv : Equivalence imp_expr_list_eq.
  Proof.
    unfold imp_expr_list_eq.
    constructor; red; intros.
    - reflexivity.
    - symmetry; eauto.
    - rewrite H. eauto.
  Qed.
  
  Global Instance imp_stmt_equiv : Equivalence imp_stmt_eq.
  Proof.
    unfold imp_stmt_eq.
    constructor; red; intros.
    - reflexivity.
    - symmetry; eauto.
    - rewrite H; eauto.
  Qed.

  Global Instance imp_function_equiv : Equivalence imp_function_eq.
  Proof.
    unfold imp_function_eq. 
    constructor; red; intros.
    - reflexivity.
    - symmetry; eauto.
    - rewrite H; eauto. 
  Qed.

  Global Instance imp_equiv : Equivalence imp_eq.
  Proof.
    unfold imp_eq. 
    constructor; red; intros.
    - reflexivity.
    - symmetry; eauto.
    - rewrite H; eauto. 
  Qed.

  Section proper.

    Global Instance ImpExprError_proper msg :
      Proper imp_expr_eq (ImpExprError msg).
    Proof.
      unfold Proper, respectful, imp_expr_eq; trivial.
    Qed.

    Global Instance ImpExprVar_proper v :
      Proper imp_expr_eq (ImpExprVar v).
    Proof.
      unfold Proper, respectful, imp_expr_eq; trivial.
    Qed.

    Global Instance ImpExprConst_proper d :
      Proper imp_expr_eq (ImpExprConst d).
    Proof.
      unfold Proper, respectful, imp_expr_eq; trivial.
    Qed.

        Lemma match_eq_lemma :
      forall A B  (l1: option  A) (l2:option  A) f (z:B),
        l1 = l2 ->
        match l1 with
        | Some x => f x
        | None => z
        end
        =
        match l2 with
        | Some x => f x
        | None => z
        end.
    Proof.
      do 3 intro.
      intuition.
      subst;apply eq_refl.
    Qed.

    
    Global Instance ImpExprOp_proper :
      Proper (eq ==> imp_expr_list_eq ==> imp_expr_eq) ImpExprOp.
    Proof.
      unfold Proper, respectful, imp_expr_list_eq; intros; simpl.
      unfold imp_expr_eq; intros; subst.
      simpl.
      unfold olift; simpl.
      apply match_eq_lemma.
      rewrite 2 lift_map_map_fusion.
      revert H0.
      induction 1.
      auto.
      simpl.
      rewrite H.
      destruct imp_expr_eval;[|apply eq_refl].
      unfold lift.
      rewrite IHForall2.
      apply eq_refl.
    Qed.


    Global Instance ImpExprRuntimeCall_proper :
      Proper (eq ==> imp_expr_list_eq ==> imp_expr_eq) ImpExprRuntimeCall.
    Proof.
      unfold Proper, respectful, imp_expr_list_eq; intros; simpl.
      unfold imp_expr_eq; intros; subst.
      simpl.
      unfold olift; simpl.
      apply match_eq_lemma.
      rewrite 2 lift_map_map_fusion.
      revert H0.
      induction 1.
      auto.
      simpl.
      rewrite H.
      destruct imp_expr_eval;[|apply eq_refl].
      unfold lift.
      rewrite IHForall2.
      apply eq_refl.
    Qed.

    Global Instance ImpStmtAssign :
      Proper (eq ==> imp_expr_eq ==> imp_stmt_eq) ImpStmtAssign.
    Proof.
      unfold Proper, respectful, imp_stmt_eq; intros; simpl.
      rewrite H0; subst; reflexivity.
    Qed.
   
    Global Instance ImpStmtIf :
      Proper (imp_expr_eq ==> imp_stmt_eq ==> imp_stmt_eq ==> imp_stmt_eq) ImpStmtIf.
    Proof.
      unfold Proper, respectful, imp_stmt_eq; intros; simpl.
      rewrite H; rewrite H0; rewrite H1; reflexivity.
    Qed.
    
    Global Instance ImpFun_proper:
      Proper (eq ==> imp_stmt_eq ==> eq ==> imp_function_eq) ImpFun.
    Proof.
      unfold Proper, respectful, imp_function_eq; intros; simpl.
      subst.
      unfold imp_stmt_eq in H0.
      rewrite H0.
      reflexivity.
    Qed.
    
  End proper.
  
End NNRSimpEq.

Notation "X ≡ᵉ Y" := (imp_expr_eq X Y) (at level 90) : nnrs_imp. (* ≡ = \equiv *)

Notation "X ≡ˢ Y" := (imp_stmt_eq X Y) (at level 90) : nnrs_imp. (* ≡ = \equiv *)

Notation "X ≡ˢⁱ Y" := (imp_eq X Y) (at level 90) : nnrs_imp. (* ≡ = \equiv *)

