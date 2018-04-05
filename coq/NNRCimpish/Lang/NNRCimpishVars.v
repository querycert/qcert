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

Section NNRCimpishVars.
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
  Require Import NNRCimpish.

  Context {fruntime:foreign_runtime}. 
  Context (h:brand_relation_t).
  
  Fixpoint nnrc_impish_expr_free_vars (e:nnrc_impish_expr) : list var
    := match e with 
       | NNRCimpishGetConstant _ => nil
       | NNRCimpishVar v => v :: nil
       | NNRCimpishConst _ => nil
       | NNRCimpishBinop _ e₁ e₂ => nnrc_impish_expr_free_vars e₁ ++ nnrc_impish_expr_free_vars e₂
       | NNRCimpishUnop _ e₁ => nnrc_impish_expr_free_vars e₁ 
       | NNRCimpishGroupBy _ _ e₁ => nnrc_impish_expr_free_vars e₁
       end.

End NNRCimpishVars.
