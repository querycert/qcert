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
Require Import Bool.
Require Import List.
Require Import Arith.
Require Import Program.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonSystem.
Require Import NNRSimp.
Require Import NNRSimpVars.
Require Import NNRSimpEval.
Require Import NNRSimpSem.
Require Import NNRSimpSemEval.

Section NNRSimpUsage.

  Context {fruntime:foreign_runtime}.

  Fixpoint nnrs_imp_expr_may_use (e:nnrs_imp_expr) (x:var) : bool
    := match e with
       | NNRSimpGetConstant v => false
       | NNRSimpVar v => x ==b v
       | NNRSimpConst d => false
       | NNRSimpBinop bop e₁ e₂ =>
         nnrs_imp_expr_may_use e₁ x || nnrs_imp_expr_may_use e₂ x
       | NNRSimpUnop uop e => nnrs_imp_expr_may_use e x
       | NNRSimpGroupBy g sl e => nnrs_imp_expr_may_use e x
       end.

  Lemma nnrs_imp_expr_may_use_free_vars e x :
    nnrs_imp_expr_may_use e x = true <-> In x (nnrs_imp_expr_free_vars e).
  Proof.
    induction e; simpl; intuition; unfold equiv_decb in *.
    - match_destr_in H; rewrite e; tauto.
    - match_destr; congruence.
    - rewrite in_app_iff.
      apply orb_prop in H3.
      tauto.
    - rewrite in_app_iff in H3.
      intuition.
  Qed.

  Lemma nnrs_imp_expr_may_use_free_vars_neg e x :
    nnrs_imp_expr_may_use e x = false <-> ~ In x (nnrs_imp_expr_free_vars e).
  Proof.
    split; intros HH.
    - intros H.
      apply nnrs_imp_expr_may_use_free_vars in H.
      congruence.
    - case_eq (nnrs_imp_expr_may_use e x); trivial.
      intros H.
      apply nnrs_imp_expr_may_use_free_vars in H.
      congruence.
  Qed.
  
  Inductive VarUsage :=
  | VarMustBeAssigned
  | VarMayBeUsedWithoutAssignment
  | VarNotUsedAndNotAssigned.

  Global Instance VarUsage_dec : EqDec VarUsage eq.
  Proof.
    change (forall x y:VarUsage, {x = y} + {x <> y}).
    decide equality.
  Defined.

  Fixpoint nnrs_imp_stmt_var_usage (s:nnrs_imp_stmt) (x:var) : VarUsage
    := match s with
       | NNRSimpSkip => VarNotUsedAndNotAssigned
       | NNRSimpSeq s₁ s₂ =>
         match nnrs_imp_stmt_var_usage s₁ x with
         | VarMustBeAssigned => VarMustBeAssigned
         | VarMayBeUsedWithoutAssignment => VarMayBeUsedWithoutAssignment
         | VarNotUsedAndNotAssigned => nnrs_imp_stmt_var_usage s₂ x 
         end
       | NNRSimpLet v oe₁ s₂ =>
         if match oe₁ with
            | Some e₁ => nnrs_imp_expr_may_use e₁ x
            | None => false
            end
         then VarMayBeUsedWithoutAssignment
         else if v ==b x
              then VarNotUsedAndNotAssigned
              else nnrs_imp_stmt_var_usage s₂ x
       | NNRSimpAssign v e =>
         if nnrs_imp_expr_may_use e x
         then VarMayBeUsedWithoutAssignment
         else if v ==b x
              then VarMustBeAssigned
              else VarNotUsedAndNotAssigned
       | NNRSimpFor v e s₀ => 
         if nnrs_imp_expr_may_use e x
         then VarMayBeUsedWithoutAssignment
         else if v ==b x
              then VarNotUsedAndNotAssigned
              else match nnrs_imp_stmt_var_usage s₀ x with
                   (* If the loops does run, then there may be a problem *)
                   | VarMayBeUsedWithoutAssignment => VarMayBeUsedWithoutAssignment
                   (* Since the loop may not execute, it can't count as a definite assignment *)
                   | VarMustBeAssigned => VarNotUsedAndNotAssigned
                   | VarNotUsedAndNotAssigned => VarNotUsedAndNotAssigned
                   end
       | NNRSimpIf e s₁ s₂ =>
         if nnrs_imp_expr_may_use e x
         then VarMayBeUsedWithoutAssignment
         else match nnrs_imp_stmt_var_usage s₁ x, nnrs_imp_stmt_var_usage s₂ x with
              | VarMayBeUsedWithoutAssignment, _ => VarMayBeUsedWithoutAssignment
              | _, VarMayBeUsedWithoutAssignment => VarMayBeUsedWithoutAssignment
              | VarMustBeAssigned, VarMustBeAssigned => VarMustBeAssigned
              | _, _ => VarNotUsedAndNotAssigned
              end

       | NNRSimpEither e x₁ s₁ x₂ s₂ =>
         if nnrs_imp_expr_may_use e x
         then VarMayBeUsedWithoutAssignment
         else match x₁ == x, nnrs_imp_stmt_var_usage s₁ x, x₂ == x, nnrs_imp_stmt_var_usage s₂ x with
              | right _, VarMayBeUsedWithoutAssignment, _, _ => VarMayBeUsedWithoutAssignment
              | _, _, right _, VarMayBeUsedWithoutAssignment => VarMayBeUsedWithoutAssignment
              | right _, VarMustBeAssigned, right _, VarMustBeAssigned => VarMustBeAssigned
              | _, _, _, _ => VarNotUsedAndNotAssigned
              end
       end.

End NNRSimpUsage.