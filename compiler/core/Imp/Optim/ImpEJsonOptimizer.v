(*
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
Require Import EJsonRuntime.
Require Import Imp.
Require Import ImpEJson.
Require Import ImpEJsonEval.
Require Import ImpEJsonOptimizerEngine.
Require Import ImpEJsonRewrite.

(* XXX This is a temporary place-holder, includes only for loop rewrites *)
Section ImpEJsonOptimizer.
  Context {foreign_ejson_model:Set}.
  Context {fejson:foreign_ejson foreign_ejson_model}.
  Context {foreign_ejson_runtime_op : Set}.
  Context {fejruntime:foreign_ejson_runtime foreign_ejson_runtime_op}.

  (** XXX Empty optimizations for now *)
  Definition nooptims (q:@imp_ejson_stmt foreign_ejson_model foreign_ejson_runtime_op) := q.
  Lemma nooptims_correct h s j:
    imp_ejson_stmt_eval h s j = imp_ejson_stmt_eval h (nooptims s) j.
  Proof.
    reflexivity.
  Qed.

  Definition imp_ejson_optim_top (q:@imp_ejson foreign_ejson_model foreign_ejson_runtime_op) : imp_ejson :=
    imp_ejson_block_rewrite
      nooptims
      q.

  Section Correctness.
    Lemma imp_ejson_optim_top_correct h (σ : list (string * ejson)) (q:imp_ejson) :
        imp_ejson_eval_top_on_ejson h σ q =
        imp_ejson_eval_top_on_ejson h σ (imp_ejson_optim_top q).
    Proof.
      unfold imp_ejson_eval_top_on_ejson.
      unfold imp_ejson_optim_top.
      rewrite (imp_ejson_block_rewrite_correct nooptims).
      reflexivity.
      apply nooptims_correct.
    Qed.
      
  End Correctness.
End ImpEJsonOptimizer.
