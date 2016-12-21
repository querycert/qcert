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

Section TNNRCMROptimizer.
  Require Import String.
  Require Import List ListSet.
  Require Import Arith.
  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.

  Require Import Utils BasicSystem.
  Require Import NNRCSystem.
  Require Import NNRCRewriteUtil NNRCRewrite TNNRCRewrite.
  Require Import NNRCOptimizer TNNRCOptimizer.
  Require Import OptimizerLogger.
  Require Import OptimizerStep.

  Require Import NNRCMR.
  Require Import ForeignReduceOps.
  Definition trew_old_nnrcmr
             {fruntime:foreign_runtime} {fredop:foreign_reduce_op} {logger:optimizer_logger string nnrc}
             (l: nnrcmr) :=
    let inputs_loc := l.(mr_inputs_loc) in
    let chain :=
        List.map
          (fun mr =>
             let map :=
                 match mr.(mr_map) with
                 | MapDist (x, n) => MapDist (x, trew_old n)
                 | MapDistFlatten (x, n) => MapDistFlatten (x, trew_old n)
                 | MapScalar (x, n) => MapScalar (x, trew_old n)
                 end
             in
             let reduce :=
                 match mr.(mr_reduce) with
                 | RedId => RedId
                 | RedCollect (x, n) => RedCollect (x, trew_old n)
                 | RedOp op => RedOp op
                 | RedSingleton => RedSingleton
                 end
             in
             mkMR mr.(mr_input) mr.(mr_output) map reduce)
          l.(mr_chain)
    in
    let last :=
        let '((params, n), args) := l.(mr_last) in
        ((params, trew_old n), args)
    in
    mkMRChain
      inputs_loc
      chain
      last.

End TNNRCMROptimizer.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
