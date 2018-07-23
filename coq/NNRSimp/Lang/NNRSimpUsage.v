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

  Section vars.

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

    Lemma nnrs_imp_expr_may_use_free_vars_eq {e₁ e₂} :
      nnrs_imp_expr_free_vars e₁ = nnrs_imp_expr_free_vars e₂ ->
      forall x, nnrs_imp_expr_may_use e₁ x = nnrs_imp_expr_may_use e₂ x.
    Proof.
      intros eqq x.
      case_eq (nnrs_imp_expr_may_use e₁ x); intros eqq2.
      - apply nnrs_imp_expr_may_use_free_vars in eqq2.
        rewrite eqq in eqq2.
        apply nnrs_imp_expr_may_use_free_vars in eqq2; eauto.
      - apply nnrs_imp_expr_may_use_free_vars_neg in eqq2.
        rewrite eqq in eqq2.
        apply nnrs_imp_expr_may_use_free_vars_neg in eqq2; eauto.
    Qed.
    
    
    Lemma nnrs_imp_stmt_free_used s x :
      nnrs_imp_stmt_var_usage s x <> VarNotUsedAndNotAssigned ->
      In x (nnrs_imp_stmt_free_vars s).
    Proof.
      nnrs_imp_stmt_cases (induction s) Case
      ; simpl
      ; repeat rewrite in_app_iff
      ; try rewrite nnrs_imp_expr_may_use_free_vars
      ; try rewrite IHs
      ; try rewrite IHs1
      ; try rewrite IHs2.
      - Case "NNRSimpSkip"%string.
        congruence.
      - Case "NNRSimpSeq"%string.
        match_case; intuition congruence.
      - Case "NNRSimpAssign"%string.
        match_case; try congruence
        ; try rewrite nnrs_imp_expr_may_use_free_vars
        ; try rewrite nnrs_imp_expr_may_use_free_vars_neg.
        + intuition congruence.
        + unfold equiv_decb; destruct (v == x); intuition congruence.
      - Case "NNRSimpLet"%string.
        destruct o.
        + (match_case; intros eqq)
          ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
          ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq.
          * intuition congruence.
          * { unfold equiv_decb; destruct (v == x); unfold equiv, complement in *.
              - subst.
                intuition.
              - intuition.
                right; apply remove_in_neq; intuition.
            }
        + simpl; intuition.
          unfold equiv_decb in *; destruct (v ==x); try intuition congruence.
          right.
          apply remove_in_neq; intuition.
      - Case "NNRSimpFor"%string.
        (match_case; intros eqq)
        ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
        ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq.
        + intuition congruence.
        +  unfold equiv_decb; destruct (v == x); unfold equiv, complement in *.
           * subst.
             intuition.
           * { match_case; intros eqq2; try congruence.
               rewrite <- remove_in_neq by eauto.
               right; apply IHs.
               intuition; try congruence.
             }
      - Case "NNRSimpIf"%string.
        (match_case; intros eqq)
        ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
        ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq.
        + intuition congruence.
        + match_case; intros eqq1
          ; try (match_case; intros eqq2)
          ; try intuition congruence.
      - Case "NNRSimpEither"%string.
        (match_case; intros eqq)
        ; try rewrite nnrs_imp_expr_may_use_free_vars in eqq
        ; try rewrite nnrs_imp_expr_may_use_free_vars_neg in eqq.
        + intuition congruence.
        + destruct (v == x).
          * { destruct (v0 == x)
              ; try intuition congruence.
              match_case; intros eqq1
              ; try (match_case; intros eqq2)
              ; try intuition congruence.
              right; right.
              rewrite <- remove_in_neq by eauto.
              apply IHs2; congruence.
            } 
          * { match_case; intros eqq1.
              -  destruct (v0 == x)
                 ; try intuition congruence.
                 match_case; intros eqq2
                 ; try intuition congruence.
                 + right; left.
                   rewrite <- remove_in_neq by eauto.
                   apply IHs1; congruence.
                 + right; left.
                   rewrite <- remove_in_neq by eauto.
                   apply IHs1; congruence.
              -  right; left.
                 rewrite <- remove_in_neq by eauto.
                 apply IHs1; congruence.
              - destruct (v0 == x)
                ; try intuition congruence.
                match_case; intros eqq2
                ; try intuition congruence.
                + right; right.
                  rewrite <- remove_in_neq by eauto.
                  apply IHs2; congruence.
            }
    Qed.

    Lemma nnrs_imp_stmt_free_unassigned s x :
      ~ In x (nnrs_imp_stmt_free_vars s) ->
      nnrs_imp_stmt_var_usage s x = VarNotUsedAndNotAssigned.
    Proof.
      generalize (nnrs_imp_stmt_free_used s x); intros.
      destruct (nnrs_imp_stmt_var_usage s x)
      ; intuition congruence.
    Qed.
    
  End vars.

  Section eval.
    
    Lemma nnrs_imp_stmt_eval_must_assign_assigns {h σc s σ σ'}:
      nnrs_imp_stmt_eval h σc s σ = Some σ' ->
      forall x,
        nnrs_imp_stmt_var_usage s x = VarMustBeAssigned ->
        exists o, lookup equiv_dec σ' x = Some (Some o).
    Proof.
      intros eqq1 x; revert eqq1.
      revert σ σ'.
      nnrs_imp_stmt_cases (induction s) Case; simpl; intros σ σ' eq1 eq2.
      - Case "NNRSimpSkip"%string.
        congruence.
      - Case "NNRSimpSeq"%string.
        apply some_olift in eq1.
        destruct eq1 as [? eqq1 eqq2].
        symmetry in eqq2.
        specialize (IHs1 _ _ eqq1).
        specialize (IHs2 _ _ eqq2).
        match_destr_in eq2; eauto.
        destruct IHs1 as [o inn]; trivial.
        generalize (nnrs_imp_stmt_eval_lookup_some_some eqq2 _ _ inn); trivial.
      - match_destr_in eq2.
        unfold equiv_decb in *.
        destruct (v == x); try congruence.
        match_destr_in eq1.
        unfold equiv in *; subst.
        match_option_in eq1.
        invcs eq1.
        apply lookup_in_domain in eqq.
        rewrite lookup_update_eq_in; eauto.
      - Case "NNRSimpLet"%string.
        destruct o.
        + match_destr_in eq2.
          unfold equiv_decb in *.
          destruct (v == x); try congruence.
          unfold olift in eq1.
          match_destr_in eq1.
          match_option_in eq1.
          destruct p; try discriminate.
          invcs eq1.
          specialize (IHs _ _ eqq eq2).
          simpl in IHs.
          destruct p.
          apply nnrs_imp_stmt_eval_domain_stack in eqq.
          simpl in eqq; invcs eqq.
          match_destr_in IHs; try congruence.
        + match_option_in eq1.
          unfold equiv_decb in *.
          destruct (v == x); try congruence.
          destruct p; try discriminate.
          invcs eq1.
          specialize (IHs _ _ eqq eq2).
          simpl in IHs.
          destruct p.
          apply nnrs_imp_stmt_eval_domain_stack in eqq.
          simpl in eqq; invcs eqq.
          match_destr_in IHs; try congruence.
      - Case "NNRSimpFor"%string.
        match_destr_in eq2.
        unfold equiv_decb in *.
        destruct (v == x); try congruence.
        match_case_in eq2; intros eqq; rewrite eqq in *; try discriminate.
      - Case "NNRSimpIf"%string.
        match_destr_in eq1.
        match_destr_in eq2.
        match_case_in eq2; intros eqq1; rewrite eqq1 in *
        ; try discriminate
        ; match_case_in eq2; intros eqq2; rewrite eqq2 in *
        ; try discriminate.

        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRSimpEither"%string.
        match_destr_in eq1.
        match_destr_in eq2.
        destruct (v == x)
        ; destruct (v0 == x)
        ; try discriminate
        ; try solve [repeat match_destr_in eq2; try congruence].
        
        match_case_in eq2; intros eqq1; rewrite eqq1 in *
        ; try discriminate
        ; match_case_in eq2; intros eqq2; rewrite eqq2 in *
        ; try discriminate.

        unfold var in *.
        destruct d; try discriminate.
        + match_option_in eq1.
          destruct p; try discriminate.
          specialize (IHs1 _ _ eqq eq2).
          simpl in IHs1.
          destruct p.
          apply nnrs_imp_stmt_eval_domain_stack in eqq.
          simpl in eqq; invcs eqq.
          invcs eq1.
          destruct (equiv_dec x s); try congruence.
        + match_option_in eq1.
          destruct p; try discriminate.
          specialize (IHs2 _ _ eqq eq2).
          simpl in IHs2.
          destruct p.
          apply nnrs_imp_stmt_eval_domain_stack in eqq.
          simpl in eqq; invcs eqq.
          invcs eq1.
          destruct (equiv_dec x s); try congruence.
    Qed.

  End eval.
  
End NNRSimpUsage.