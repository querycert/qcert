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
        ].

    Definition nnrs_imp_stmt_optim_model_list {model:basic_model} : list (OptimizerStepModel tnnrs_imp_stmt_rewrites_to)
      := [
          for_nil_step_correct
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