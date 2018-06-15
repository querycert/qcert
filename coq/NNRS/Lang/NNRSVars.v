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
Require Import NNRS.

Section NNRSVars.
  Context {fruntime:foreign_runtime}. 
  Context (h:brand_relation_t).
  
  Fixpoint nnrs_expr_free_vars (e:nnrs_expr) : list var
    := match e with 
       | NNRSGetConstant _ => nil
       | NNRSVar v => v :: nil
       | NNRSConst _ => nil
       | NNRSBinop _ e₁ e₂ => nnrs_expr_free_vars e₁ ++ nnrs_expr_free_vars e₂
       | NNRSUnop _ e₁ => nnrs_expr_free_vars e₁ 
       | NNRSGroupBy _ _ e₁ => nnrs_expr_free_vars e₁
       end.

  
  Fixpoint nnrs_stmt_free_env_vars (s:nnrs_stmt) : list var
    := match s with
       | NNRSSeq s₁ s₂ =>
         nnrs_stmt_free_env_vars s₁ ++ nnrs_stmt_free_env_vars s₂
       | NNRSLet v e s₀ =>
         nnrs_expr_free_vars e ++ remove equiv_dec v (nnrs_stmt_free_env_vars s₀)
       | NNRSLetMut v s₁ s₂ =>
         nnrs_stmt_free_env_vars s₁ ++ remove equiv_dec v (nnrs_stmt_free_env_vars s₂)
       | NNRSLetMutColl v s₁ s₂ =>
         nnrs_stmt_free_env_vars s₁ ++ remove equiv_dec v (nnrs_stmt_free_env_vars s₂)
       | NNRSAssign v e =>
         nnrs_expr_free_vars e
       | NNRSPush v e =>
         nnrs_expr_free_vars e
       | NNRSFor v e s₀ =>
         nnrs_expr_free_vars e ++ remove equiv_dec v (nnrs_stmt_free_env_vars s₀)
       | NNRSIf e s₁ s₂ =>
         nnrs_expr_free_vars e ++
                                    nnrs_stmt_free_env_vars s₁ ++ nnrs_stmt_free_env_vars s₂
       | NNRSEither e x₁ s₁ x₂ s₂ =>
         nnrs_expr_free_vars e ++
                                    remove equiv_dec x₁ (nnrs_stmt_free_env_vars s₁) ++
                                    remove equiv_dec x₂ (nnrs_stmt_free_env_vars s₂)
       end.

  Fixpoint nnrs_stmt_free_mcenv_vars (s:nnrs_stmt) : list var
    := match s with
       | NNRSSeq s₁ s₂ =>
         nnrs_stmt_free_mcenv_vars s₁ ++ nnrs_stmt_free_mcenv_vars s₂
       | NNRSLet v e s₀ =>
         nnrs_stmt_free_mcenv_vars s₀
       | NNRSLetMut v s₁ s₂ =>
         nnrs_stmt_free_mcenv_vars s₁ ++ nnrs_stmt_free_mcenv_vars s₂
       | NNRSLetMutColl v s₁ s₂ =>
         remove equiv_dec v (nnrs_stmt_free_mcenv_vars s₁) ++ nnrs_stmt_free_mcenv_vars s₂
       | NNRSAssign v e =>
         nil
       | NNRSPush v e =>
         v::nil
       | NNRSFor v e s₀ =>
         nnrs_stmt_free_mcenv_vars s₀
       | NNRSIf e s₁ s₂ =>
         nnrs_stmt_free_mcenv_vars s₁ ++ nnrs_stmt_free_mcenv_vars s₂
       | NNRSEither e x₁ s₁ x₂ s₂ =>
         nnrs_stmt_free_mcenv_vars s₁ ++ nnrs_stmt_free_mcenv_vars s₂
       end.

  Fixpoint nnrs_stmt_free_mdenv_vars (s:nnrs_stmt) : list var
    := match s with
       | NNRSSeq s₁ s₂ =>
         nnrs_stmt_free_mdenv_vars s₁ ++ nnrs_stmt_free_mdenv_vars s₂
       | NNRSLet v e s₀ =>
         nnrs_stmt_free_mdenv_vars s₀
       | NNRSLetMut v s₁ s₂ =>
         remove equiv_dec v (nnrs_stmt_free_mdenv_vars s₁) ++ nnrs_stmt_free_mdenv_vars s₂
       | NNRSLetMutColl v s₁ s₂ =>
         nnrs_stmt_free_mdenv_vars s₁ ++ nnrs_stmt_free_mdenv_vars s₂
       | NNRSAssign v e =>
         v::nil
       | NNRSPush v e =>
         nil
       | NNRSFor v e s₀ =>
         nnrs_stmt_free_mdenv_vars s₀
       | NNRSIf e s₁ s₂ =>
         nnrs_stmt_free_mdenv_vars s₁ ++ nnrs_stmt_free_mdenv_vars s₂
       | NNRSEither e x₁ s₁ x₂ s₂ =>
         nnrs_stmt_free_mdenv_vars s₁ ++ nnrs_stmt_free_mdenv_vars s₂
       end.

  Fixpoint nnrs_stmt_bound_env_vars (s:nnrs_stmt) : list var
    := match s with
       | NNRSSeq s₁ s₂ =>
         nnrs_stmt_bound_env_vars s₁ ++ nnrs_stmt_bound_env_vars s₂
       | NNRSLet v e s₀ =>
         v :: nnrs_stmt_bound_env_vars s₀
       | NNRSLetMut v s₁ s₂ =>
         v :: nnrs_stmt_bound_env_vars s₁ ++ nnrs_stmt_bound_env_vars s₂
       | NNRSLetMutColl v s₁ s₂ =>
         v :: nnrs_stmt_bound_env_vars s₁ ++ nnrs_stmt_bound_env_vars s₂
       | NNRSAssign v e =>
         nil
       | NNRSPush v e =>
         nil
       | NNRSFor v e s₀ =>
         v :: nnrs_stmt_bound_env_vars s₀
       | NNRSIf e s₁ s₂ =>
         nnrs_stmt_bound_env_vars s₁ ++ nnrs_stmt_bound_env_vars s₂
       | NNRSEither e x₁ s₁ x₂ s₂ =>
         x₁ :: x₂ :: nnrs_stmt_bound_env_vars s₁ ++ nnrs_stmt_bound_env_vars s₂
       end.

  Fixpoint nnrs_stmt_bound_mcenv_vars (s:nnrs_stmt) : list var
    := match s with
       | NNRSSeq s₁ s₂ =>
         nnrs_stmt_bound_mcenv_vars s₁ ++ nnrs_stmt_bound_mcenv_vars s₂
       | NNRSLet v e s₀ =>
         nnrs_stmt_bound_mcenv_vars s₀
       | NNRSLetMut v s₁ s₂ =>
         nnrs_stmt_bound_mcenv_vars s₁ ++ nnrs_stmt_bound_mcenv_vars s₂
       | NNRSLetMutColl v s₁ s₂ =>
         v :: nnrs_stmt_bound_mcenv_vars s₁ ++ nnrs_stmt_bound_mcenv_vars s₂
       | NNRSAssign v e =>
         nil
       | NNRSPush v e =>
         nil
       | NNRSFor v e s₀ =>
         nnrs_stmt_bound_mcenv_vars s₀
       | NNRSIf e s₁ s₂ =>
         nnrs_stmt_bound_mcenv_vars s₁ ++ nnrs_stmt_bound_mcenv_vars s₂
       | NNRSEither e x₁ s₁ x₂ s₂ =>
         nnrs_stmt_bound_mcenv_vars s₁ ++ nnrs_stmt_bound_mcenv_vars s₂
       end.

  Fixpoint nnrs_stmt_bound_mdenv_vars (s:nnrs_stmt) : list var
    := match s with
       | NNRSSeq s₁ s₂ =>
         nnrs_stmt_bound_mdenv_vars s₁ ++ nnrs_stmt_bound_mdenv_vars s₂
       | NNRSLet v e s₀ =>
         nnrs_stmt_bound_mdenv_vars s₀
       | NNRSLetMut v s₁ s₂ =>
         v :: nnrs_stmt_bound_mdenv_vars s₁ ++ nnrs_stmt_bound_mdenv_vars s₂
       | NNRSLetMutColl v s₁ s₂ =>
         nnrs_stmt_bound_mdenv_vars s₁ ++ nnrs_stmt_bound_mdenv_vars s₂
       | NNRSAssign v e =>
         nil
       | NNRSPush v e =>
         nil
       | NNRSFor v e s₀ =>
         nnrs_stmt_bound_mdenv_vars s₀
       | NNRSIf e s₁ s₂ =>
         nnrs_stmt_bound_mdenv_vars s₁ ++ nnrs_stmt_bound_mdenv_vars s₂
       | NNRSEither e x₁ s₁ x₂ s₂ =>
         nnrs_stmt_bound_mdenv_vars s₁ ++ nnrs_stmt_bound_mdenv_vars s₂
       end.
  
End NNRSVars.
