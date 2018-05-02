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

(* Cross Shadowing is when a variable in one namespace "shadows" 
   a variable in another namespace.  This is not a problem for nnrc_impish, since 
   the namespaces are all distinct.  However, it poses a problem when compiling to
   a language like nnrc_imp that has a single namespace.
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
Require Import NNRCimpish.
Require Import NNRCimpishVars.

Section NNRCimpishCrossShadow.

  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  Local Open Scope nnrc_impish.
  Local Open Scope string.

  Fixpoint nnrc_impish_stmt_cross_shadow_free_under
           (s:nnrc_impish_stmt)
           (σ ψc ψd:list var)
    : Prop
    := match s with
       | NNRCimpishSeq s₁ s₂ =>
         nnrc_impish_stmt_cross_shadow_free_under s₁ σ ψc ψd
         /\ nnrc_impish_stmt_cross_shadow_free_under s₂ σ ψc ψd
       | NNRCimpishLet v e s₀ =>
         disjoint (nnrc_impish_expr_free_vars e) ψc
         /\ disjoint (nnrc_impish_expr_free_vars e) ψd
        (* not the same: incl (nnrc_impish_expr_free_vars e) σ *)
         /\ ~ In v ψc
         /\ ~ In v ψd
         /\ nnrc_impish_stmt_cross_shadow_free_under s₀ (v::σ) ψc ψd
       | NNRCimpishLetMut v s₁ s₂ =>
            ~ In v σ
         /\ ~ In v ψc
         /\ ~ In v ψd      
         /\ nnrc_impish_stmt_cross_shadow_free_under s₁ σ ψc (v::ψd)
         /\ nnrc_impish_stmt_cross_shadow_free_under s₂ (v::σ) ψc ψd
       | NNRCimpishLetMutColl v s₁ s₂ =>
            ~ In v σ
         /\ ~ In v ψc
         /\ ~ In v ψd      
         /\ nnrc_impish_stmt_cross_shadow_free_under s₁ σ (v::ψc) ψd
         /\ nnrc_impish_stmt_cross_shadow_free_under s₂ (v::σ) ψc ψd
       | NNRCimpishAssign v e =>
            disjoint (nnrc_impish_expr_free_vars e) ψc
         /\ disjoint (nnrc_impish_expr_free_vars e) ψd
         /\ ~ In v σ
         /\ ~ In v ψc
       (* not the same: In v ψd *)
       | NNRCimpishPush v e =>
         disjoint (nnrc_impish_expr_free_vars e) ψc
         /\ disjoint (nnrc_impish_expr_free_vars e) ψd
         /\ ~ In v σ
         /\ ~ In v ψd
       (* not the same: In v ψc *)
       | NNRCimpishFor v e s₀ =>
         disjoint (nnrc_impish_expr_free_vars e) ψc
         /\ disjoint (nnrc_impish_expr_free_vars e) ψd
        (* not the same: incl (nnrc_impish_expr_free_vars e) σ *)          
         /\ ~ In v ψc
         /\ ~ In v ψd
         /\ nnrc_impish_stmt_cross_shadow_free_under s₀ (v::σ) ψc ψd
       | NNRCimpishIf e s₁ s₂ =>
         disjoint (nnrc_impish_expr_free_vars e) ψc
         /\ disjoint (nnrc_impish_expr_free_vars e) ψd
        (* not the same: incl (nnrc_impish_expr_free_vars e) σ *)
         /\ nnrc_impish_stmt_cross_shadow_free_under s₁ σ ψc ψd
         /\ nnrc_impish_stmt_cross_shadow_free_under s₂ σ ψc ψd
       | NNRCimpishEither e x₁ s₁ x₂ s₂ =>
         disjoint (nnrc_impish_expr_free_vars e) ψc
         /\ disjoint (nnrc_impish_expr_free_vars e) ψd
        (* not the same: incl (nnrc_impish_expr_free_vars e) σ *)
         /\ ~ In x₁ ψc
         /\ ~ In x₁ ψd
         /\ ~ In x₂ ψc
         /\ ~ In x₂ ψd
         /\ nnrc_impish_stmt_cross_shadow_free_under s₁ (x₁::σ) ψc ψd
         /\ nnrc_impish_stmt_cross_shadow_free_under s₂ (x₂::σ) ψc ψd
       end.

  Definition nnrc_impish_cross_shadow_free (s:nnrc_impish)
    := nnrc_impish_stmt_cross_shadow_free_under (fst s) nil nil (snd s::nil).
  
End NNRCimpishCrossShadow.
