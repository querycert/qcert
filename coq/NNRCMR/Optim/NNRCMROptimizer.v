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
Require Import List ListSet.
Require Import Arith.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import cNNRCSystem.
Require Import NNRCOptim.
Require Import OptimizerLogger.
Require Import OptimizerStep.
Require Import NNRCMR.
Require Import NNRCMRRewrite.
Require Import ForeignReduceOps.

Section NNRCMROptimizer.
  Definition trew_nnrcmr
             {fruntime:foreign_runtime} {fredop:foreign_reduce_op} {logger:optimizer_logger string nnrc}
             (l: nnrcmr) :=
    let inputs_loc := l.(mr_inputs_loc) in
    let chain :=
        List.map
          (fun mr =>
             let map :=
                 match mr.(mr_map) with
                 | MapDist (x, n) => MapDist (x, run_nnrc_optims_default n)
                 | MapDistFlatten (x, n) => MapDistFlatten (x, run_nnrc_optims_default n)
                 | MapScalar (x, n) => MapScalar (x, run_nnrc_optims_default n)
                 end
             in
             let reduce :=
                 match mr.(mr_reduce) with
                 | RedId => RedId
                 | RedCollect (x, n) => RedCollect (x, run_nnrc_optims_default n)
                 | RedOp op => RedOp op
                 | RedSingleton => RedSingleton
                 end
             in
             mkMR mr.(mr_input) mr.(mr_output) map reduce)
          l.(mr_chain)
    in
    let last :=
        let '((params, n), args) := l.(mr_last) in
        ((params, run_nnrc_optims_default n), args)
    in
    mkMRChain
      inputs_loc
      chain
      last.

  Definition run_nnrcmr_optims
             {fruntime:foreign_runtime} {fredop:foreign_reduce_op} {logger:optimizer_logger string nnrc}
             q :=
    let q := trew_nnrcmr (mr_optimize q) in (* MR-level optimization *)
    trew_nnrcmr q. (* Optimize NNRC expressions within resulting NNRCMR *)
  
End NNRCMROptimizer.

