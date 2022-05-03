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

Section ImpEJsonOptimizerEngine.
  Import ListNotations.

  Context {foreign_ejson_model:Set}.
  Context {fejson:foreign_ejson foreign_ejson_model}.
  Context {foreign_ejson_runtime_op : Set}.
  Context {fejruntime:foreign_ejson_runtime foreign_ejson_runtime_op}.

  Section OptimizerEngine.

    (* Rewriting functional for into imperative for loop is now isolated *)
    Fixpoint imp_ejson_stmt_block_rewrite
             (fs : imp_stmt -> imp_stmt)
             (stmt: @imp_ejson_stmt foreign_ejson_model foreign_ejson_runtime_op)
    : imp_ejson_stmt :=
      match stmt with
      | ImpStmtBlock lv ls =>
        fs (ImpStmtBlock
              lv (* XXX Could add expr rewrite *)
              (map (imp_ejson_stmt_block_rewrite fs) ls))
      | ImpStmtAssign v e =>
        fs (ImpStmtAssign v e)
      | ImpStmtFor v e s =>
        fs (ImpStmtFor v e
                       (imp_ejson_stmt_block_rewrite fs s))
      | ImpStmtForRange v e1 e2 s =>
        fs (ImpStmtForRange v e1 e2
                            (imp_ejson_stmt_block_rewrite fs s))
      | ImpStmtIf e s1 s2 =>
        fs (ImpStmtIf e
                      (imp_ejson_stmt_block_rewrite fs s1)
                      (imp_ejson_stmt_block_rewrite fs s2))
      end.

    Definition imp_ejson_function_block_rewrite
               (fs : imp_stmt -> imp_stmt)
               (f:imp_function) : imp_function :=
      match f with
      | ImpFun v1 s v2 =>
        ImpFun v1 (imp_ejson_stmt_block_rewrite fs s) v2
      end.
    Definition imp_ejson_block_rewrite
               (fs : imp_stmt -> imp_stmt)
               (q:imp_ejson) : imp_ejson :=
      match q with
      | ImpLib l =>
        ImpLib (map (fun xy => (fst xy, imp_ejson_function_block_rewrite fs (snd xy))) l)
      end.
  End OptimizerEngine.

  Section CorrectnessOptimizerEngine.
    Lemma imp_ejson_function_stmt_rewrite_correct
          (fs : imp_stmt -> imp_stmt)
          h (j:pd_jbindings) (s:imp_ejson_stmt) :
      (forall s0, forall j0, imp_ejson_stmt_eval h s0 j0 = imp_ejson_stmt_eval h (fs s0) j0) ->
      imp_ejson_stmt_eval h s j = imp_ejson_stmt_eval h (imp_ejson_stmt_block_rewrite fs s) j.
    Proof.
      revert j.
      induction s; intros; simpl in *.
      - rewrite <- H0; simpl.
        generalize (@ImpEval.imp_decls_eval (@imp_ejson_model foreign_ejson_model)
             (@imp_ejson_constant foreign_ejson_model) imp_ejson_op
             (@imp_ejson_runtime_op foreign_ejson_runtime_op)
             (@imp_ejson_model_normalize foreign_ejson_model)
             (@imp_ejson_runtime_eval foreign_ejson_model fejson foreign_ejson_runtime_op
                fejruntime h) (@imp_ejson_op_eval foreign_ejson_model) j el); intros.
        induction el; intros; simpl in *; try reflexivity.
        + destruct o; intros; simpl; try reflexivity.
          generalize (Some p).
          induction sl; intros; simpl in *; try reflexivity.
          inversion H; clear H; subst.
          destruct o; simpl; try reflexivity.
          * rewrite IHsl; clear IHsl; [|assumption].
            assert (imp_ejson_stmt_eval h a p0
                    = imp_ejson_stmt_eval h (imp_ejson_stmt_block_rewrite fs a) p0) by
                apply (H3 p0 H0).
            rewrite H; reflexivity.
          * rewrite IHsl; clear IHsl; [reflexivity|assumption].
        + rewrite IHel; reflexivity.
      - rewrite <- H; simpl; reflexivity.
      - rewrite <- H; simpl.
        destruct (@ImpEval.imp_expr_eval (@imp_ejson_model foreign_ejson_model)
        (@imp_ejson_constant foreign_ejson_model) imp_ejson_op
        (@imp_ejson_runtime_op foreign_ejson_runtime_op)
        (@imp_ejson_model_normalize foreign_ejson_model)
        (@imp_ejson_runtime_eval foreign_ejson_model fejson foreign_ejson_runtime_op fejruntime h)
        (@imp_ejson_op_eval foreign_ejson_model) j e); try reflexivity.
        destruct (imp_ejson_model_to_list i); try reflexivity.
        revert j.
        induction l; intros; try reflexivity.
        rewrite <- IHs; [|assumption].
        destruct (@imp_ejson_stmt_eval foreign_ejson_model fejson foreign_ejson_runtime_op fejruntime h s
        (@cons (prod var (option (@imp_ejson_model foreign_ejson_model)))
           (@pair var (option (@imp_ejson_model foreign_ejson_model)) v
                  (@Some (@imp_ejson_model foreign_ejson_model) a)) j)); try reflexivity.
        destruct p; try reflexivity.
        apply IHl.
      - rewrite <- H; simpl.
        destruct (@olift (@imp_ejson_model foreign_ejson_model) Z (@imp_ejson_model_to_Z foreign_ejson_model)
        (@ImpEval.imp_expr_eval (@imp_ejson_model foreign_ejson_model)
           (@imp_ejson_constant foreign_ejson_model) imp_ejson_op
           (@imp_ejson_runtime_op foreign_ejson_runtime_op)
           (@imp_ejson_model_normalize foreign_ejson_model)
           (@imp_ejson_runtime_eval foreign_ejson_model fejson foreign_ejson_runtime_op fejruntime
                                    h) (@imp_ejson_op_eval foreign_ejson_model) j e1)); try reflexivity.
        destruct (@olift (@imp_ejson_model foreign_ejson_model) Z (@imp_ejson_model_to_Z foreign_ejson_model)
        (@ImpEval.imp_expr_eval (@imp_ejson_model foreign_ejson_model)
           (@imp_ejson_constant foreign_ejson_model) imp_ejson_op
           (@imp_ejson_runtime_op foreign_ejson_runtime_op)
           (@imp_ejson_model_normalize foreign_ejson_model)
           (@imp_ejson_runtime_eval foreign_ejson_model fejson foreign_ejson_runtime_op fejruntime
                                    h) (@imp_ejson_op_eval foreign_ejson_model) j e2)); try reflexivity.
        generalize (ImpEval.nb_iter z z0); clear z0; intros.
        revert z j.
        induction n; intros; try reflexivity.
        rewrite IHs; clear IHs; [|assumption].
        destruct (@imp_ejson_stmt_eval foreign_ejson_model fejson foreign_ejson_runtime_op fejruntime h
        (imp_ejson_stmt_block_rewrite fs s)
        (@cons (prod var (option (@imp_ejson_model foreign_ejson_model)))
           (@pair var (option (@imp_ejson_model foreign_ejson_model)) v
              (@Some (@imp_ejson_model foreign_ejson_model)
                     (@imp_ejson_Z_to_data foreign_ejson_model z))) j)); try reflexivity.
        destruct p; try reflexivity.
        apply IHn.
      - rewrite <- H; simpl.
        destruct (@ImpEval.imp_expr_eval (@imp_ejson_model foreign_ejson_model)
        (@imp_ejson_constant foreign_ejson_model) imp_ejson_op
        (@imp_ejson_runtime_op foreign_ejson_runtime_op)
        (@imp_ejson_model_normalize foreign_ejson_model)
        (@imp_ejson_runtime_eval foreign_ejson_model fejson foreign_ejson_runtime_op fejruntime h)
        (@imp_ejson_op_eval foreign_ejson_model) j e); try reflexivity.
        destruct (imp_ejson_model_to_bool i); try reflexivity.
        destruct b; auto.
    Qed.

    Lemma imp_ejson_function_block_rewrite_correct
          (fs : imp_stmt -> imp_stmt)
          h (j:ejson) (f:imp_ejson_function) :
      (forall s0, forall j0, imp_ejson_stmt_eval h s0 j0 = imp_ejson_stmt_eval h (fs s0) j0) ->
      imp_ejson_function_eval h f j = imp_ejson_function_eval h (imp_ejson_function_block_rewrite fs f) j.
    Proof.
      intros; destruct f. simpl.
      assert (imp_ejson_stmt_eval h i [(v0, None); (v, Some j)]
              = imp_ejson_stmt_eval h (imp_ejson_stmt_block_rewrite fs i) [(v0, None); (v, Some j)])
        by (apply (imp_ejson_function_stmt_rewrite_correct fs); assumption).
      unfold imp_ejson_stmt_eval in H0; simpl in *.
      assert (@ImpEval.imp_stmt_eval (@imp_ejson_model foreign_ejson_model)
           (@imp_ejson_constant foreign_ejson_model) imp_ejson_op
           (@imp_ejson_runtime_op foreign_ejson_runtime_op)
           (@imp_ejson_model_normalize foreign_ejson_model)
           (@imp_ejson_model_to_bool foreign_ejson_model)
           (@imp_ejson_model_to_Z foreign_ejson_model)
           (@imp_ejson_model_to_list foreign_ejson_model)
           (@imp_ejson_Z_to_data foreign_ejson_model)
           (@imp_ejson_runtime_eval foreign_ejson_model fejson foreign_ejson_runtime_op fejruntime
              h) (@imp_ejson_op_eval foreign_ejson_model) i
           (@cons (prod var (option (@ejson foreign_ejson_model)))
              (@pair var (option (@ejson foreign_ejson_model)) v0
                 (@None (@ejson foreign_ejson_model)))
              (@cons (prod var (option (@ejson foreign_ejson_model)))
                 (@pair var (option (@ejson foreign_ejson_model)) v
                    (@Some (@ejson foreign_ejson_model) j))
                 (@nil (prod var (option (@ejson foreign_ejson_model))))))
           = @ImpEval.imp_stmt_eval (@imp_ejson_model foreign_ejson_model)
        (@imp_ejson_constant foreign_ejson_model) imp_ejson_op
        (@imp_ejson_runtime_op foreign_ejson_runtime_op)
        (@imp_ejson_model_normalize foreign_ejson_model)
        (@imp_ejson_model_to_bool foreign_ejson_model) (@imp_ejson_model_to_Z foreign_ejson_model)
        (@imp_ejson_model_to_list foreign_ejson_model) (@imp_ejson_Z_to_data foreign_ejson_model)
        (@imp_ejson_runtime_eval foreign_ejson_model fejson foreign_ejson_runtime_op fejruntime h)
        (@imp_ejson_op_eval foreign_ejson_model) i
        (@cons (prod var (option (@imp_ejson_model foreign_ejson_model)))
           (@pair var (option (@imp_ejson_model foreign_ejson_model)) v0
              (@None (@imp_ejson_model foreign_ejson_model)))
           (@cons (prod var (option (@imp_ejson_model foreign_ejson_model)))
              (@pair var (option (@imp_ejson_model foreign_ejson_model)) v
                 (@Some (@imp_ejson_model foreign_ejson_model) j))
              (@nil (prod var (option (@imp_ejson_model foreign_ejson_model))))))) by reflexivity.
      rewrite H1 in H0.
      rewrite H0; reflexivity.
    Qed.

    Lemma imp_ejson_block_rewrite_correct
          (fs : imp_stmt -> imp_stmt)
          h (j : ejson) (q:imp_ejson) :
      (forall s0, forall j0, imp_ejson_stmt_eval h s0 j0 = imp_ejson_stmt_eval h (fs s0) j0) ->
      imp_ejson_eval h q j =
      imp_ejson_eval h (imp_ejson_block_rewrite fs q) j.
    Proof.
      induction q; simpl; intros.
      destruct l; simpl; intros; [reflexivity|].
      destruct p; simpl.
      destruct l; simpl; [|reflexivity].
      assert (imp_ejson_function_eval h i j
              = imp_ejson_function_eval h (imp_ejson_function_block_rewrite fs i) j)
        by (apply imp_ejson_function_block_rewrite_correct; assumption).
      simpl in H0.
      unfold imp_ejson_function_eval in H0.
      rewrite H0; reflexivity.
    Qed.
  End CorrectnessOptimizerEngine.

End ImpEJsonOptimizerEngine.
