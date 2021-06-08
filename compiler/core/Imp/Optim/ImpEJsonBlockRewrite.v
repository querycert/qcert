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

(** Imp is a simpl imperative intermediate language. *)

Require Import String.
Require Import List.
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import Utils.
Require Import JsAst.JsNumber.
Require Import EJsonRuntime.
Require Import Imp.
Require Import ImpEJson.
Require Import ImpEJsonVars.
Require Import ImpEJsonEval.

Section ImpEJsonBlockRewrite.
  Import ListNotations.

  Context {foreign_ejson_model:Set}.
  Context {fejson:foreign_ejson foreign_ejson_model}.
  Context {foreign_ejson_runtime_op : Set}.
  Context {fejruntime:foreign_ejson_runtime foreign_ejson_runtime_op}.

  Section BlockRewrite.

    (* Rewriting functional for into imperative for loop is now isolated *)
    Fixpoint imp_ejson_stmt_block_rewrite (stmt: @imp_ejson_stmt foreign_ejson_model foreign_ejson_runtime_op): imp_ejson_stmt :=
      match stmt with
      | ImpStmtBlock lv ls =>
        ImpStmtBlock
          lv
          (map imp_ejson_stmt_block_rewrite ls)
      | ImpStmtAssign v e =>
        ImpStmtAssign v e
      | ImpStmtFor v e s =>
        ImpStmtFor v e
                   (imp_ejson_stmt_block_rewrite s)
      | ImpStmtForRange v e1 e2 s =>
        ImpStmtForRange v e1 e2
                        (imp_ejson_stmt_block_rewrite s)
      | ImpStmtIf e s1 s2 =>
        ImpStmtIf e
                  (imp_ejson_stmt_block_rewrite s1)
                  (imp_ejson_stmt_block_rewrite s2)
      end.

    Definition imp_ejson_function_block_rewrite (f:imp_function) : imp_function :=
      match f with
      | ImpFun v1 s v2 =>
        ImpFun v1 (imp_ejson_stmt_block_rewrite s) v2
      end.
    Definition imp_ejson_block_rewrite (q:imp_ejson) : imp_ejson :=
      match q with
      | ImpLib l =>
        ImpLib (map (fun xy => (fst xy, imp_ejson_function_block_rewrite (snd xy))) l)
      end.
  End BlockRewrite.

  Section CorrectnessBlockRewrite.
    Lemma imp_ejson_block_rewrite_correct h (j : ejson) (q:imp_ejson) :
        imp_ejson_eval h q j =
        imp_ejson_eval h (imp_ejson_block_rewrite q) j.
    Proof.
      admit.
    Admitted.
  End CorrectnessBlockRewrite.

End ImpEJsonBlockRewrite.
