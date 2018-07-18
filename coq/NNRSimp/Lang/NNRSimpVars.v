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
Require Import Permutation.
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
Require Import NNRSimp.

Section NNRSimpVars.

  Context {fruntime:foreign_runtime}. 
  Context (h:brand_relation_t).
  
  Fixpoint nnrs_imp_expr_free_vars (e:nnrs_imp_expr) : list var
    := match e with 
       | NNRSimpGetConstant _ => nil
       | NNRSimpVar v => v :: nil
       | NNRSimpConst _ => nil
       | NNRSimpBinop _ e₁ e₂ => nnrs_imp_expr_free_vars e₁ ++ nnrs_imp_expr_free_vars e₂
       | NNRSimpUnop _ e₁ => nnrs_imp_expr_free_vars e₁ 
       | NNRSimpGroupBy _ _ e₁ => nnrs_imp_expr_free_vars e₁
       end.

  Fixpoint nnrs_imp_stmt_free_vars (s:nnrs_imp_stmt) : list var
    := match s with
       | NNRSimpSkip => nil
       | NNRSimpSeq s₁ s₂ =>
         nnrs_imp_stmt_free_vars s₁ ++ nnrs_imp_stmt_free_vars s₂
       | NNRSimpAssign v e =>
         v::(nnrs_imp_expr_free_vars e)
       | NNRSimpLet v eo s₀ =>
         match eo with
         | Some e => nnrs_imp_expr_free_vars e
         | None => nil
         end ++ remove string_eqdec v (nnrs_imp_stmt_free_vars s₀)
       | NNRSimpFor v e s₀ =>
         nnrs_imp_expr_free_vars e ++ remove string_eqdec v (nnrs_imp_stmt_free_vars s₀)
       | NNRSimpIf e s₁ s₂ =>
         nnrs_imp_expr_free_vars e ++ nnrs_imp_stmt_free_vars s₁ ++ nnrs_imp_stmt_free_vars s₂
       | NNRSimpEither e x₁ s₁ x₂ s₂ =>
         nnrs_imp_expr_free_vars e ++ remove string_eqdec x₁ (nnrs_imp_stmt_free_vars s₁) ++ remove string_eqdec x₂ (nnrs_imp_stmt_free_vars s₂)
       end.

  Fixpoint nnrs_imp_stmt_bound_vars (s:nnrs_imp_stmt) : list var
    := match s with
       | NNRSimpSkip => nil
       | NNRSimpSeq s₁ s₂ =>
         nnrs_imp_stmt_bound_vars s₁ ++ nnrs_imp_stmt_bound_vars s₂
       | NNRSimpAssign v e =>
         nil
       | NNRSimpLet v eo s₀ =>
         v::(nnrs_imp_stmt_bound_vars s₀)
       | NNRSimpFor v e s₀ =>
         v::(nnrs_imp_stmt_bound_vars s₀)
       | NNRSimpIf e s₁ s₂ =>
         nnrs_imp_stmt_bound_vars s₁ ++ nnrs_imp_stmt_bound_vars s₂
       | NNRSimpEither e x₁ s₁ x₂ s₂ =>
         x₁::(nnrs_imp_stmt_bound_vars s₁) ++ x₂::(nnrs_imp_stmt_bound_vars s₂)
       end.

  Fixpoint nnrs_imp_stmt_mayberead_vars (s:nnrs_imp_stmt) : list var
    := match s with
       | NNRSimpSkip => nil
       | NNRSimpSeq s₁ s₂ =>
         nnrs_imp_stmt_mayberead_vars s₁ ++ nnrs_imp_stmt_mayberead_vars s₂
       | NNRSimpAssign v e =>
         nnrs_imp_expr_free_vars e
       | NNRSimpLet v eo s₀ =>
         match eo with
         | Some e => nnrs_imp_expr_free_vars e
         | None => nil
         end ++ remove string_eqdec v (nnrs_imp_stmt_mayberead_vars s₀)
       | NNRSimpFor v e s₀ =>
         nnrs_imp_expr_free_vars e ++ remove string_eqdec v (nnrs_imp_stmt_mayberead_vars s₀)
       | NNRSimpIf e s₁ s₂ =>
         nnrs_imp_expr_free_vars e ++ nnrs_imp_stmt_mayberead_vars s₁ ++ nnrs_imp_stmt_mayberead_vars s₂
       | NNRSimpEither e x₁ s₁ x₂ s₂ =>
         nnrs_imp_expr_free_vars e ++ remove string_eqdec x₁ (nnrs_imp_stmt_mayberead_vars s₁) ++ remove string_eqdec x₂ (nnrs_imp_stmt_mayberead_vars s₂)
       end.

    Fixpoint nnrs_imp_stmt_maybewritten_vars (s:nnrs_imp_stmt) : list var
    := match s with
       | NNRSimpSkip => nil
       | NNRSimpSeq s₁ s₂ =>
         nnrs_imp_stmt_maybewritten_vars s₁ ++ nnrs_imp_stmt_maybewritten_vars s₂
       | NNRSimpAssign v e =>
         v::nil
       | NNRSimpLet v eo s₀ =>
         remove string_eqdec v (nnrs_imp_stmt_maybewritten_vars s₀)
       | NNRSimpFor v e s₀ =>
         remove string_eqdec v (nnrs_imp_stmt_maybewritten_vars s₀)
       | NNRSimpIf e s₁ s₂ =>
         nnrs_imp_stmt_maybewritten_vars s₁ ++ nnrs_imp_stmt_maybewritten_vars s₂
       | NNRSimpEither e x₁ s₁ x₂ s₂ =>
         remove string_eqdec x₁ (nnrs_imp_stmt_maybewritten_vars s₁) ++ remove string_eqdec x₂ (nnrs_imp_stmt_maybewritten_vars s₂)
       end.

    Global Instance remove_perm_proper {A} dec v :
      Proper ((@Permutation A) ==> (@Permutation A)) (remove dec v).
    Proof.
      unfold Proper, respectful.
      apply Permutation_ind_bis; simpl; intros.
      - trivial.
      - match_destr.
        eauto.
      - repeat match_destr; eauto.
        rewrite H0.
        apply perm_swap.
      - etransitivity; eauto.
    Qed.
        
    Lemma nnrs_imp_stmt_free_vars_readwrite_perm (s:nnrs_imp_stmt)
      : Permutation
          (nnrs_imp_stmt_free_vars s)
          (nnrs_imp_stmt_mayberead_vars s ++ nnrs_imp_stmt_maybewritten_vars s).
    Proof.
      nnrs_imp_stmt_cases (induction s) Case
      ; simpl.
      - Case "NNRSimpSkip"%string.
        trivial.
      - Case "NNRSimpSeq"%string.
        rewrite IHs1, IHs2.
        repeat rewrite app_ass.
        apply Permutation_app; try reflexivity.
        repeat rewrite <- app_ass.
        apply Permutation_app; try reflexivity.
        apply Permutation_app_swap.
      - Case "NNRSimpAssign"%string.
        apply Permutation_cons_append.
      - Case "NNRSimpLet"%string.
        rewrite app_ass.
        apply Permutation_app; try reflexivity.
        rewrite list_remove_append_distrib.
        apply remove_perm_proper; trivial.
      - Case "NNRSimpFor"%string.
        rewrite app_ass.
        apply Permutation_app; try reflexivity.
        rewrite list_remove_append_distrib.
        apply remove_perm_proper; trivial.
      - Case "NNRSimpIf"%string.
        rewrite app_ass.
        apply Permutation_app; try reflexivity.
        rewrite IHs1, IHs2.
        repeat rewrite app_ass.
        apply Permutation_app; try reflexivity.
        repeat rewrite <- app_ass.
        apply Permutation_app; try reflexivity.
        apply Permutation_app_swap.
      - Case "NNRSimpEither"%string.
        rewrite app_ass.
        apply Permutation_app; try reflexivity.
        transitivity (
            ((remove string_eqdec v (nnrs_imp_stmt_mayberead_vars s1))
                     ++ remove string_eqdec v (nnrs_imp_stmt_maybewritten_vars s1))
               ++
               ((remove string_eqdec v0 (nnrs_imp_stmt_mayberead_vars s2))
                  ++ remove string_eqdec v0 (nnrs_imp_stmt_maybewritten_vars s2))).
        + repeat rewrite list_remove_append_distrib.
          apply Permutation_app
          ; apply remove_perm_proper; trivial.
        + repeat rewrite app_ass.
          apply Permutation_app; try reflexivity.
          repeat rewrite <- app_ass.
          apply Permutation_app; try reflexivity.
          apply Permutation_app_swap.
    Qed.

    Lemma nnrs_imp_stmt_free_vars_readwrite_equiv (s:nnrs_imp_stmt)
      : equivlist
          (nnrs_imp_stmt_free_vars s)
          (nnrs_imp_stmt_mayberead_vars s ++ nnrs_imp_stmt_maybewritten_vars s).
    Proof.
      rewrite nnrs_imp_stmt_free_vars_readwrite_perm; reflexivity.
    Qed.

End NNRSimpVars.
