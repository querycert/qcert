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

(** NNRSimp is a variant of the named nested relational calculus
     (NNRC) that is meant to be more imperative in feel.  It is used
     as an intermediate language between NNRC and more imperative /
     statement oriented backends *)

Require Import String.
Require Import List.
Require Import Bool.
Require Import Arith.
Require Import Utils.
Require Import JsAst.JsNumber.
Require Import EJsonRuntime.
Require Import Imp.
Require Import ImpEJson.
Require Import ImpEJsonEval.

Section ImpEJsonRewrite.
  Import ListNotations.

  Context {fejson:foreign_ejson}.
  Context {fejruntime:foreign_ejson_runtime}.

  Section ForRewrite.
    (* Rewriting functional for into imperative for loop is now isolated *)
    Fixpoint imp_ejson_stmt_for_rewrite (avoid: list string) (stmt: imp_ejson_stmt): imp_ejson_stmt :=
      match stmt with
      | ImpStmtBlock lv ls =>
        ImpStmtBlock
          lv
          (map (imp_ejson_stmt_for_rewrite ((List.map fst lv) ++ avoid)) ls)
      | ImpStmtAssign v e =>
        ImpStmtAssign v e
      | ImpStmtFor v e s =>
        let avoid := v :: avoid in
        let src_id := fresh_var "src" avoid in
        let avoid := src_id :: avoid in
        let i_id := fresh_var "i" avoid in
        let avoid := i_id :: avoid in
        let src := ImpExprVar src_id in
        let i := ImpExprVar i_id in
        ImpStmtBlock
          [ (src_id, Some e) ]
          [ ImpStmtForRange
              i_id
              (ImpExprConst (ejbigint 0))
              (* XXX Use src.length - 1, consistent with semantic of 'for i1 to i2 do ... done' loop *)
              (ImpExprRuntimeCall EJsonRuntimeNatMinus
                                  [ ImpExprOp EJsonOpArrayLength [ src ] ; ImpExprConst (ejbigint 1) ])
              (ImpStmtBlock
                 [ (v, Some (ImpExprOp EJsonOpArrayAccess [ src; i ])) ]
                 [ imp_ejson_stmt_for_rewrite avoid s ]) ]
      | ImpStmtForRange v e1 e2 s =>
        ImpStmtForRange v
                        e1
                        e2
                        (imp_ejson_stmt_for_rewrite (v :: avoid) s)
      | ImpStmtIf e s1 s2 =>
        ImpStmtIf e
                  (imp_ejson_stmt_for_rewrite avoid s1)
                  (imp_ejson_stmt_for_rewrite avoid s2)
      end.
  End ForRewrite.

  Section CorrectnessForRewrite.
    Lemma imp_ejson_stmt_for_rewrite_correct h (σ : pd_jbindings) (stmt:imp_ejson_stmt) :
      forall avoid,
        imp_ejson_stmt_eval h stmt σ =
        imp_ejson_stmt_eval h (imp_ejson_stmt_for_rewrite avoid stmt)  σ.
    Proof.
      admit.
    Admitted.
  End CorrectnessForRewrite.

End ImpEJsonRewrite.
