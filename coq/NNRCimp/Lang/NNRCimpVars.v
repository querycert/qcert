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
Require Import NNRCimp.

Section NNRCimpVars.

  Context {fruntime:foreign_runtime}. 
  Context (h:brand_relation_t).
  
  Fixpoint nnrc_imp_expr_free_vars (e:nnrc_imp_expr) : list var
    := match e with 
       | NNRCimpGetConstant _ => nil
       | NNRCimpVar v => v :: nil
       | NNRCimpConst _ => nil
       | NNRCimpBinop _ e₁ e₂ => nnrc_imp_expr_free_vars e₁ ++ nnrc_imp_expr_free_vars e₂
       | NNRCimpUnop _ e₁ => nnrc_imp_expr_free_vars e₁ 
       | NNRCimpGroupBy _ _ e₁ => nnrc_imp_expr_free_vars e₁
       end.

    Fixpoint nnrc_imp_stmt_free_vars (s:nnrc_imp_stmt) : list var
      := match s with
         | NNRCimpSeq s₁ s₂ =>
           nnrc_imp_stmt_free_vars s₁ ++ nnrc_imp_stmt_free_vars s₂
         | NNRCimpAssign v e =>
           v::(nnrc_imp_expr_free_vars e)
         | NNRCimpLet v eo s₀ =>
           match eo with
           | Some e => nnrc_imp_expr_free_vars e
           | None => nil
           end ++ remove string_eqdec v (nnrc_imp_stmt_free_vars s₀)
         | NNRCimpFor v e s₀ =>
           nnrc_imp_expr_free_vars e ++ remove string_eqdec v (nnrc_imp_stmt_free_vars s₀)
         | NNRCimpIf e s₁ s₂ =>
           nnrc_imp_expr_free_vars e ++ nnrc_imp_stmt_free_vars s₁ ++ nnrc_imp_stmt_free_vars s₂
         | NNRCimpEither e x₁ s₁ x₂ s₂ =>
           nnrc_imp_expr_free_vars e ++ remove string_eqdec x₁ (nnrc_imp_stmt_free_vars s₁) ++ remove string_eqdec x₂ (nnrc_imp_stmt_free_vars s₂)
       end.

End NNRCimpVars.
