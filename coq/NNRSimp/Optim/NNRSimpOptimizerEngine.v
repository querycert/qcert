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

(* This includes some rewrites/simplification rules for the Nested relational calculus *)

Require Import String.
Require Import List.
Require Import ListSet.
Require Import Arith.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import NNRSimpSystem.

Section NNRSimpOptimizerEngine.
  Local Open Scope nnrs_imp.
  Local Open Scope string.

  Section map.
    Context {fruntime:foreign_runtime}.

    Fixpoint nnrs_imp_expr_map_deep
             (fe :  nnrs_imp_expr -> nnrs_imp_expr)
             (e:nnrs_imp_expr) : nnrs_imp_expr
      := match e with
         | NNRSimpGetConstant v =>
           fe (NNRSimpGetConstant v)
         | NNRSimpVar v =>
           fe (NNRSimpVar v)
         | NNRSimpConst d =>
           fe (NNRSimpConst d)
         | NNRSimpBinop bop e1 e2 =>
           fe (NNRSimpBinop bop
                            (nnrs_imp_expr_map_deep fe e1)
                            (nnrs_imp_expr_map_deep fe e2))
         | NNRSimpUnop uop e1 =>
           fe (NNRSimpUnop uop
                           (nnrs_imp_expr_map_deep fe e1))
         | NNRSimpGroupBy g sl e1 =>
           fe (NNRSimpGroupBy g sl
                              (nnrs_imp_expr_map_deep fe e1))
         end.

    Fixpoint nnrs_imp_stmt_map_deep
             (fe :  nnrs_imp_expr -> nnrs_imp_expr)
             (fs :  nnrs_imp_stmt -> nnrs_imp_stmt)
             (s:nnrs_imp_stmt) : nnrs_imp_stmt
      := match s with
         | NNRSimpSkip => fs NNRSimpSkip
         | NNRSimpSeq s₁ s₂ =>
           fs (NNRSimpSeq
                 (nnrs_imp_stmt_map_deep fe fs s₁)
                 (nnrs_imp_stmt_map_deep fe fs s₂))
         | NNRSimpAssign v e =>
           fs (NNRSimpAssign v
                             (nnrs_imp_expr_map_deep fe e))
         | NNRSimpLet v None s₀ =>
           let s_opt :=  nnrs_imp_stmt_map_deep fe fs s₀ in
           let s_maybeopt :=
               if VarUsage_dec (nnrs_imp_stmt_var_usage s₀ v) VarMayBeUsedWithoutAssignment then
                 s_opt
               else
                 if VarUsage_dec (nnrs_imp_stmt_var_usage s_opt v) VarMayBeUsedWithoutAssignment 
                 then s₀
                 else s_opt in
           fs (NNRSimpLet v None s_maybeopt)
         | NNRSimpLet v (Some e) s₀ =>
           fs (NNRSimpLet v
                          (Some (nnrs_imp_expr_map_deep fe e))
                          (nnrs_imp_stmt_map_deep fe fs s₀))
         | NNRSimpFor v e s₀ =>
           fs (NNRSimpFor v
                          (nnrs_imp_expr_map_deep fe e)
                          (nnrs_imp_stmt_map_deep fe fs s₀))
         | NNRSimpIf e s₁ s₂ =>
           fs (NNRSimpIf 
                 (nnrs_imp_expr_map_deep fe e)
                 (nnrs_imp_stmt_map_deep fe fs s₁)
                 (nnrs_imp_stmt_map_deep fe fs s₂))
         | NNRSimpEither e x₁ s₁ x₂ s₂ =>
           fs (NNRSimpEither 
                 (nnrs_imp_expr_map_deep fe e)
                 x₁
                 (nnrs_imp_stmt_map_deep fe fs s₁)
                 x₂
                 (nnrs_imp_stmt_map_deep fe fs s₂))
         end.

    Definition nnrs_imp_map_deep
               (fe :  nnrs_imp_expr -> nnrs_imp_expr)
               (fs :  nnrs_imp_stmt -> nnrs_imp_stmt)
               (fsi :  nnrs_imp -> nnrs_imp)
               (si:nnrs_imp) : nnrs_imp
      :=
        let s_opt :=  nnrs_imp_stmt_map_deep fe fs (fst si) in
        let s_maybeopt :=
            if VarUsage_dec (nnrs_imp_stmt_var_usage (fst si) (snd si)) VarMayBeUsedWithoutAssignment then
              s_opt
            else 
              if VarUsage_dec (nnrs_imp_stmt_var_usage s_opt (snd si)) VarMayBeUsedWithoutAssignment 
              then fst si
              else s_opt in
        fsi (s_maybeopt, snd si).

  End map.

  Section correct_untyped.
    Context {fruntime:foreign_runtime}.
    
    Lemma nnrs_imp_expr_map_deep_eq_correctness
          (fe :  nnrs_imp_expr -> nnrs_imp_expr)
          (e : nnrs_imp_expr) : 
      (forall e', fe e' ≡ᵉ e') -> nnrs_imp_expr_map_deep fe e ≡ᵉ e.
    Proof.
      intros Hfe.
      nnrs_imp_expr_cases (induction e) Case; simpl
      ; repeat rewrite Hfe
      ; repeat rewrite IHe
      ; repeat rewrite IHe1
      ; repeat rewrite IHe2
      ; try reflexivity.
    Qed.

    Lemma nnrs_imp_stmt_map_deep_eq_correctness
          (fe :  nnrs_imp_expr -> nnrs_imp_expr)
          (fs :  nnrs_imp_stmt -> nnrs_imp_stmt)
          (s : nnrs_imp_stmt) : 
      (forall e', fe e' ≡ᵉ e') ->
      (forall s', fs s' ≡ˢ s') ->
      nnrs_imp_stmt_map_deep fe fs s ≡ˢ s.
    Proof.
      intros Hfe Hfs.
      nnrs_imp_stmt_cases (induction s) Case; simpl
      ; try match_destr
      ; repeat rewrite Hfs
      ; repeat rewrite IHs
      ; repeat rewrite IHs1
      ; repeat rewrite IHs2
      ; repeat rewrite nnrs_imp_expr_map_deep_eq_correctness by eauto
      ; try reflexivity.
      - Case "NNRSimpLet"%string.
        apply NNRSimpLet_proper; try reflexivity; simpl.
        repeat rewrite nnrs_imp_expr_map_deep_eq_correctness by eauto.
        reflexivity.
      - Case "NNRSimpLet"%string.
        apply NNRSimpLet_none_proper.
        repeat match_destr.
        reflexivity.
    Qed.

    Lemma nnrs_imp_map_deep_eq_correctness
          (fe :  nnrs_imp_expr -> nnrs_imp_expr)
          (fs :  nnrs_imp_stmt -> nnrs_imp_stmt)
          (fsi :  nnrs_imp -> nnrs_imp)
          (si : nnrs_imp) : 
      (forall e', fe e' ≡ᵉ e') ->
      (forall s', fs s' ≡ˢ s') ->
      (forall si', fsi si' ≡ˢⁱ si') ->
      nnrs_imp_map_deep fe fs fsi si ≡ˢⁱ si.
    Proof.
      intros Hfe Hfs Hfsi.
      unfold nnrs_imp_map_deep.
      rewrite Hfsi.
      destruct si.
      repeat match_destr; simpl; try reflexivity
      ; apply NNRSImp_proper
      ; apply nnrs_imp_stmt_map_deep_eq_correctness; eauto.
    Qed.

  End correct_untyped.

  Section correct_typed.
    Context {model:basic_model}.

    Lemma nnrs_imp_expr_map_deep_trew_correctness
          (fe :  nnrs_imp_expr -> nnrs_imp_expr)
          (e : nnrs_imp_expr) : 
      (forall e', e' ⇒ᵉ fe e') -> e ⇒ᵉ nnrs_imp_expr_map_deep fe e.
    Proof.
      intros Hfe.
      nnrs_imp_expr_cases (induction e) Case; simpl
      ; repeat rewrite <- Hfe
      ; repeat rewrite <- IHe
      ; repeat rewrite <- IHe1
      ; repeat rewrite <- IHe2
      ; try reflexivity.
    Qed.

    Lemma nnrs_imp_stmt_map_deep_trew_correctness
          (fe :  nnrs_imp_expr -> nnrs_imp_expr)
          (fs :  nnrs_imp_stmt -> nnrs_imp_stmt)
          (s : nnrs_imp_stmt) : 
      (forall e', e' ⇒ᵉ fe e') ->
      (forall s', s' ⇒ˢ fs s') ->
      s ⇒ˢ nnrs_imp_stmt_map_deep fe fs s.
    Proof.
      intros Hfe Hfs.
      nnrs_imp_stmt_cases (induction s) Case; simpl
      ; try match_destr
      ; repeat rewrite <- Hfs
      ; repeat rewrite <- IHs
      ; repeat rewrite <- IHs1
      ; repeat rewrite <- IHs2
      ; repeat rewrite <- nnrs_imp_expr_map_deep_trew_correctness by eauto
      ; try reflexivity.
      - Case "NNRSimpLet"%string.
        apply NNRSimpLet_some_tproper; trivial.
        repeat rewrite <- nnrs_imp_expr_map_deep_trew_correctness by eauto.
        reflexivity.
      - Case "NNRSimpLet"%string.
        repeat match_destr
        ; apply NNRSimpLet_none_tproper; eauto; try reflexivity.
    Qed.

    Lemma nnrs_imp_map_deep_trew_correctness
          (fe :  nnrs_imp_expr -> nnrs_imp_expr)
          (fs :  nnrs_imp_stmt -> nnrs_imp_stmt)
          (fsi :  nnrs_imp -> nnrs_imp)
          (si : nnrs_imp) : 
      (forall e', e' ⇒ᵉ fe e') ->
      (forall s', s' ⇒ˢ fs s') ->
      (forall si', si' ⇒ˢⁱ fsi si') ->
      si ⇒ˢⁱ nnrs_imp_map_deep fe fs fsi si.
    Proof.
      intros Hfe Hfs Hfsi.
      unfold nnrs_imp_map_deep.
      rewrite <- Hfsi.
      destruct si.
      repeat match_destr; simpl; try reflexivity
      ; apply NNRSImp_tproper
      ; eauto
      ; apply nnrs_imp_stmt_map_deep_trew_correctness; eauto.
    Qed.

  End correct_typed.
  
End NNRSimpOptimizerEngine.

Ltac tcorrectness_prover :=
  simpl; repeat progress
                (try match goal with
                     | [|- context [match ?p with | _ => _ end] ] => destruct p
                     end; try reflexivity; try unfold Equivalence.equiv in *; try subst).

Ltac tprove_correctness p :=
  destruct p;
  tcorrectness_prover.
