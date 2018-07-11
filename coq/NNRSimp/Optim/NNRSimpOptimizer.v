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
Require Import NNRSimpOptimizerEngine.
Require Import TNNRSimpRewrite.

Section NNRSimpOptimizer.
  Local Open Scope nnrs_imp.
  Local Open Scope string.

  Section optims.
    (* The separator used when creating new variables from old variables *)
    Definition nnrs_imp_optimizer_sep := "$".

    (* It would be nice to generalize this, but normalization gets in the way *)
    Definition op_const_fun  {fruntime:foreign_runtime} (e:nnrs_imp_expr) :=
      match e with
      | NNRSimpUnop OpDistinct ‵{||} => NNRSimpConst (dcoll nil)
      | _ => e
      end.

    Lemma op_const_fun_correctness {model:basic_model} (e:nnrs_imp_expr) :
      e ⇒ᵉ (op_const_fun e).
    Proof.
      tprove_correctness e.
      - apply distinct_nil_trew.
    Qed.

    Definition op_const_step {fruntime:foreign_runtime}
      := mkOptimizerStep
           "op/const" (* name *)
           "Simplify operators applied to constants" (* description *)
           "op_const_fun" (* lemma name *)
           op_const_fun (* lemma *).

    Definition op_const_step_correct {model:basic_model}
      := mkOptimizerStepModel op_const_step op_const_fun_correctness.
    
    Definition for_nil_fun  {fruntime:foreign_runtime}(s:nnrs_imp_stmt) :=
      match s with
      | NNRSimpFor x ‵{||} s => NNRSimpSkip
      | _ => s
      end.

    Lemma for_nil_fun_correctness {model:basic_model} (s:nnrs_imp_stmt) :
      s ⇒ˢ (for_nil_fun s).
    Proof.
      tprove_correctness s.
      apply for_nil_trew.
    Qed.

    Definition for_nil_step {fruntime:foreign_runtime}
      := mkOptimizerStep
           "for/nil" (* name *)
           "Remove loop comprehensions over empty bags" (* description *)
           "for_nil_fun" (* lemma name *)
           for_nil_fun (* lemma *).

    Definition for_nil_step_correct {model:basic_model}
      := mkOptimizerStepModel for_nil_step for_nil_fun_correctness.

    Definition let_let_assign_coalesce_fun sep {fruntime:foreign_runtime}(s:nnrs_imp_stmt) :=
      match s with
      | NNRSimpLet x₁ None
                   (NNRSimpSeq
                      (NNRSimpLet x₂ oe
                                  (NNRSimpSeq s₁
                                              (NNRSimpAssign x₁' (NNRSimpVar x₂'))))
                      s₂) =>
        if x₁ == x₁'
        then if x₂ == x₂'
             then if x₁ == x₂
                  then s
                  else
                    if in_dec string_dec x₁ (nnrs_imp_stmt_free_vars s₁)
                    then s
                    else if in_dec string_dec x₁ (nnrs_imp_stmt_bound_vars s₁)
                         then
                           let x₃ := (fresh_var_from sep x₁
                                                     (nnrs_imp_stmt_free_vars s₁ ++ nnrs_imp_stmt_bound_vars s₁ ++ nnrs_imp_stmt_free_vars s₂ ++ nnrs_imp_stmt_bound_vars s₂)) in
                                                                              
                           NNRSimpLet x₃
                                      oe
                                      (NNRSimpSeq (nnrs_imp_stmt_rename s₁ x₂ x₃)
                                                  (nnrs_imp_stmt_rename s₂ x₁ x₃))

                         else
                           NNRSimpLet x₁ oe
                                      (NNRSimpSeq (nnrs_imp_stmt_rename s₁ x₂ x₁)
                                                  s₂)
             else s
        else s
      | _ => s
      end.

    Lemma let_let_assign_coalesce_fun_correctness sep {model:basic_model} (s:nnrs_imp_stmt) :
      s ⇒ˢ (let_let_assign_coalesce_fun sep s).
    Proof.
      tprove_correctness s; unfold complement in *.
      - apply let_let_coalesce_trew; trivial
        ; try (right; split); try solve [apply fresh_var_from_incl_nin
                                         ; unfold incl; intros ?; repeat rewrite in_app_iff; intuition].
      - apply let_let_coalesce_trew1; trivial.
    Qed.

    Definition let_let_assign_coalesce_step {fruntime:foreign_runtime}
      := mkOptimizerStep
           "let/let/assign" (* name *)
           "Remove loop comprehensions over empty bags" (* description *)
           "let_let_assign_coalesce_fun" (* lemma name *)
           (let_let_assign_coalesce_fun nnrs_imp_optimizer_sep) (* lemma *).

    Definition let_let_assign_coalesce_step_correct {model:basic_model}
      := mkOptimizerStepModel
           let_let_assign_coalesce_step
           (let_let_assign_coalesce_fun_correctness nnrs_imp_optimizer_sep).
    
    
  End optims.

  Section optim_lists.
    
    (* list of all optimizations and correctness proofs for them *)
    Definition nnrs_imp_expr_optim_list {fruntime:foreign_runtime} : list (@OptimizerStep nnrs_imp_expr)
      := [
          op_const_step
        ].

    Definition nnrs_imp_expr_optim_model_list {model:basic_model} : list (OptimizerStepModel tnnrs_imp_expr_rewrites_to)
      := [
          op_const_step_correct
        ].
    
    Definition nnrs_imp_stmt_optim_list {fruntime:foreign_runtime} : list (@OptimizerStep nnrs_imp_stmt)
      := [
          for_nil_step
          ; let_let_assign_coalesce_step
        ].

    Definition nnrs_imp_stmt_optim_model_list {model:basic_model} : list (OptimizerStepModel tnnrs_imp_stmt_rewrites_to)
      := [
          for_nil_step_correct
          ; let_let_assign_coalesce_step_correct
        ].

    Definition nnrs_imp_optim_list {fruntime:foreign_runtime} : list (@OptimizerStep nnrs_imp)
      := [
        ].

    Definition nnrs_imp_optim_model_list {model:basic_model} : list (OptimizerStepModel tnnrs_imp_rewrites_to)
      := [
        ].

  End optim_lists.

  Section optim_lists_props.
    
    Lemma nnrs_imp_expr_optim_model_list_complete {model:basic_model}
    : optim_model_list_complete nnrs_imp_expr_optim_list nnrs_imp_expr_optim_model_list.
    Proof.
      optim_correct_list_complete_prover.
    Qed.

    Lemma nnrs_imp_stmt_optim_model_list_complete {model:basic_model}
      : optim_model_list_complete nnrs_imp_stmt_optim_list nnrs_imp_stmt_optim_model_list.
    Proof.
      optim_correct_list_complete_prover.
    Qed.

    Lemma nnrs_imp_optim_model_list_complete {model:basic_model}
      : optim_model_list_complete nnrs_imp_optim_list nnrs_imp_optim_model_list.
    Proof.
      optim_correct_list_complete_prover.
    Qed.

    Definition nnrs_imp_expr_optim_list_correct {model:basic_model}
      : optim_list_correct tnnrs_imp_expr_rewrites_to nnrs_imp_expr_optim_list
      := optim_list_correct_from_model nnrs_imp_expr_optim_model_list_complete.

    Definition nnrs_imp_stmt_optim_list_correct {model:basic_model}
      : optim_list_correct tnnrs_imp_stmt_rewrites_to nnrs_imp_stmt_optim_list
      := optim_list_correct_from_model nnrs_imp_stmt_optim_model_list_complete.
    
    Definition nnrs_imp_optim_list_correct {model:basic_model}
      : optim_list_correct tnnrs_imp_rewrites_to nnrs_imp_optim_list
      := optim_list_correct_from_model nnrs_imp_optim_model_list_complete.

    Lemma nnrs_imp_expr_optim_list_distinct {fruntime:foreign_runtime}:
      optim_list_distinct nnrs_imp_expr_optim_list.
    Proof.
      apply optim_list_distinct_prover.
      vm_compute.
      apply eq_refl.
    Qed.

    Lemma nnrs_imp_stmt_optim_list_distinct {fruntime:foreign_runtime}:
      optim_list_distinct nnrs_imp_stmt_optim_list.
    Proof.
      apply optim_list_distinct_prover.
      vm_compute.
      apply eq_refl.
    Qed.

    Lemma nnrs_imp_optim_list_distinct {fruntime:foreign_runtime}:
      optim_list_distinct nnrs_imp_optim_list.
    Proof.
      apply optim_list_distinct_prover.
      vm_compute.
      apply eq_refl.
    Qed.

    
  End optim_lists_props.

  Section optim_runner.

    (* *************************** *)
    Definition run_nnrs_imp_optims 
               {fruntime:foreign_runtime}
               {logger_e:optimizer_logger string nnrs_imp_expr}
               {logger_s:optimizer_logger string nnrs_imp_stmt}
               {logger_t:optimizer_logger string nnrs_imp}
               (opc:optim_phases3_config)
    : nnrs_imp -> nnrs_imp :=
      run_phases3
        nnrs_imp_map_deep nnrs_imp_size
        nnrs_imp_expr_optim_list
        nnrs_imp_stmt_optim_list
        nnrs_imp_optim_list
        opc.

    Lemma run_nnrs_imp_optims_correctness
          {model:basic_model}
          {logger_e:optimizer_logger string nnrs_imp_expr}
          {logger_s:optimizer_logger string nnrs_imp_stmt}
          {logger_t:optimizer_logger string nnrs_imp}
          (opc:optim_phases3_config)
          (p:nnrs_imp) :
      tnnrs_imp_rewrites_to p (run_nnrs_imp_optims opc p).
    Proof.
      unfold run_nnrs_imp_optims.
      apply run_phases3_correctness.
      - intros.
        apply nnrs_imp_map_deep_trew_correctness; trivial.
      - apply nnrs_imp_expr_optim_list_correct.
      - apply nnrs_imp_stmt_optim_list_correct.
      - apply nnrs_imp_optim_list_correct.
    Qed.

  End optim_runner.
  
  Section default.
    
    Definition default_nnrs_imp_expr_optim_list {fruntime:foreign_runtime} : list string
      := [
          optim_step_name op_const_step
        ].

    Definition default_nnrs_imp_stmt_optim_list {fruntime:foreign_runtime} : list string
      := [
          optim_step_name for_nil_step
          ; optim_step_name let_let_assign_coalesce_step
        ].

    Definition default_nnrs_imp_optim_list {fruntime:foreign_runtime} : list string
      := [
        ].

    Remark default_nnrs_imp_expr_optim_list_all_valid {fruntime:foreign_runtime}
      : valid_optims nnrs_imp_expr_optim_list default_nnrs_imp_expr_optim_list =
        (default_nnrs_imp_expr_optim_list,nil).
    Proof.
      vm_compute; trivial.
    Qed.
    
    Remark default_nnrs_imp_stmt_optim_list_all_valid {fruntime:foreign_runtime}
      : valid_optims nnrs_imp_stmt_optim_list default_nnrs_imp_stmt_optim_list =
        (default_nnrs_imp_stmt_optim_list,nil).
    Proof.
      vm_compute; trivial.
    Qed.

    Remark default_nnrs_imp_optim_list_all_valid {fruntime:foreign_runtime}
      : valid_optims nnrs_imp_optim_list default_nnrs_imp_optim_list =
        (default_nnrs_imp_optim_list,nil).
    Proof.
      vm_compute; trivial.
    Qed.
    
    Definition default_nnrs_imp_optim_phases {fruntime:foreign_runtime} : optim_phases3_config :=
      ("[nnrs_imp] default"%string,
       default_nnrs_imp_expr_optim_list,
       default_nnrs_imp_stmt_optim_list,
       default_nnrs_imp_optim_list,
       10)::nil.

  End default.
  
  Definition run_nnrs_imp_optims_default
             {fruntime:foreign_runtime}
             {logger_e:optimizer_logger string nnrs_imp_expr}
             {logger_s:optimizer_logger string nnrs_imp_stmt}
             {logger_t:optimizer_logger string nnrs_imp}
    := run_nnrs_imp_optims default_nnrs_imp_optim_phases.

  Lemma run_nnrs_imp_optims_default_correct
        {model:basic_model}
        {logger_e:optimizer_logger string nnrs_imp_expr}
        {logger_s:optimizer_logger string nnrs_imp_stmt}
        {logger_t:optimizer_logger string nnrs_imp}
        p :
    tnnrs_imp_rewrites_to p (run_nnrs_imp_optims_default p).
  Proof.
    unfold run_nnrs_imp_optims_default.
    apply run_nnrs_imp_optims_correctness.
  Qed.
  
End NNRSimpOptimizer.