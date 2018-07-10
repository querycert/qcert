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

End NNRSimpVars.
