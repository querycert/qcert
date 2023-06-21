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

Section ImpEJsonRewrite.
  Import ListNotations.

  Context {foreign_ejson_model:Set}.
  Context {fejson:foreign_ejson foreign_ejson_model}.
  Context {foreign_ejson_runtime_op : Set}.
  Context {fejruntime:foreign_ejson_runtime foreign_ejson_runtime_op}.

  Section ForLetRewrite.

    (* Rewriting functional for into imperative for loop is now isolated *)
    Definition imp_ejson_stmt_for_let_rewrite (stmt: @imp_ejson_stmt foreign_ejson_model foreign_ejson_runtime_op): imp_ejson_stmt :=
      match stmt with
      | ImpStmtFor v e s =>
        (**
              for(v in e) do s done
              (src) fresh in v::s
              ============================
              { let src = e;
                for(v in src) do s done }
         *)
        let avoid := v :: imp_ejson_stmt_free_vars s in
        let src_id := fresh_var "src" avoid in
        let src := ImpExprVar src_id in
        ImpStmtBlock
          [ (src_id, Some e) ]
          [ ImpStmtFor v src s ]
      | _ => stmt
      end.

  End ForLetRewrite.

  Section CorrectnessForLetRewrite.

    Lemma lookup_first_var A (i0 : A) (v:var) σ :
      lookup EquivDec.equiv_dec ((v, i0) :: σ) v = Some i0.
    Proof.
      simpl.
      destruct (EquivDec.equiv_dec v v); try congruence.
    Qed.

    (**
    Lemma imp_ejson_stmt_for_let_rewrite_correct h (σ : pd_jbindings) (stmt:imp_ejson_stmt) :
        imp_ejson_stmt_eval h stmt σ =
        imp_ejson_stmt_eval h (imp_ejson_stmt_for_let_rewrite stmt) σ.
    Proof.
      destruct stmt; try reflexivity.
      simpl.
      unfold ImpEval.imp_decls_eval; unfold olift; simpl.
      generalize (@ImpEval.imp_expr_eval (@imp_ejson_model foreign_ejson_model)
        (@imp_ejson_constant foreign_ejson_model) imp_ejson_op
        (@imp_ejson_runtime_op foreign_ejson_runtime_op)
        (@imp_ejson_model_normalize foreign_ejson_model)
        (@imp_ejson_runtime_eval foreign_ejson_model fejson foreign_ejson_runtime_op fejruntime h)
        (@imp_ejson_op_eval foreign_ejson_model) σ i); intros; clear i.
      destruct o; try reflexivity.
      rewrite lookup_first_var.
      destruct (imp_ejson_model_to_list i); try reflexivity.
      ...
     *)

  End CorrectnessForLetRewrite.

  Section ForRewrite.

    (* Rewriting functional for into imperative for loop is now isolated *)
    Definition imp_ejson_stmt_for_rewrite (stmt: @imp_ejson_stmt foreign_ejson_model foreign_ejson_runtime_op): imp_ejson_stmt :=
      match stmt with
      | ImpStmtFor v (ImpExprVar src_id) s =>
        (**
              for(v in vsrc) do s done // vsrc is variable
              vi fresh in s
              ============================
              for(i = 0 to length(vsrc)-1) do
                { let v = vsrc[i];
                  s }
              done
         *)
        let avoid := imp_ejson_stmt_free_vars stmt in
        let i_id := fresh_var "i" avoid in
        let avoid := i_id :: avoid in
        let i := ImpExprVar i_id in
        ImpStmtForRange
          i_id
          (ImpExprConst (cejbigint 0))
          (* XXX Use src.length - 1, consistent with semantic of 'for i1 to i2 do ... done' loop *)
          (ImpExprRuntimeCall
             EJsonRuntimeNatMinus [
               ImpExprRuntimeCall EJsonRuntimeArrayLength [ (ImpExprVar src_id) ]; ImpExprConst (cejbigint 1)
          ])
          (ImpStmtBlock
             [ (v, Some (ImpExprRuntimeCall EJsonRuntimeArrayAccess [ (ImpExprVar src_id); i ])) ]
             [ s ])
      | _ => stmt
      end.
  End ForRewrite.

  Section CorrectnessForRewrite.

    Lemma number_iterations A (l: list A):
      (ImpEval.nb_iter 0 (BinInt.Z.sub (BinInt.Z.of_nat (List.length l)) 1)) = length l.
    Proof.
      unfold ImpEval.nb_iter; simpl.
      induction (Datatypes.length l); [ simpl; reflexivity | ].
      rewrite BinInt.Z.sub_1_r.
      rewrite Znat.Nat2Z.inj_succ.
      rewrite <- BinInt.Zpred_succ.
      case n; [ simpl; reflexivity | ].
      intros.
      rewrite <- BinInt.Zminus_0_l_reverse.
      rewrite Znat.Nat2Z.id.
      simpl; reflexivity.
    Qed.

    Fixpoint list_n_nat {A} (n:nat) (l:list A) :=
      match n with
      | 0 => nil
      | S n' =>
        match l with
        | nil => nil
        | x :: l' => x :: (list_n_nat n' l')
        end
      end.

    Definition list_tail_n_nat {A} n (l: list A) :=
      List.rev (list_n_nat n (List.rev l)).

    (**
    Lemma imp_ejson_stmt_for_rewrite_correct h (σ : pd_jbindings) (stmt:imp_ejson_stmt) :
        imp_ejson_stmt_eval h stmt σ =
        imp_ejson_stmt_eval h (imp_ejson_stmt_for_rewrite stmt) σ.
    Proof.
      imp_stmt_cases (destruct stmt) Case; try reflexivity; intros.
      simpl.
      destruct i; try reflexivity; intros; simpl.
      destruct (@olift (option (@imp_ejson_model foreign_ejson_model))
        (@imp_ejson_model foreign_ejson_model)
        (fun x : option (@imp_ejson_model foreign_ejson_model) => x)
        (@lookup string (option (@imp_ejson_model foreign_ejson_model))
           (@EquivDec.equiv_dec string (@eq string) (@RelationClasses.eq_equivalence string)
              string_eqdec) σ v0)); try reflexivity.
      simpl.
      unfold imp_ejson_model_to_list.
      case i; simpl; try reflexivity; intros l; clear i.
      rewrite number_iterations.
      revert σ.
      induction l; [ simpl; reflexivity | ].
      intros.
      simpl.
      unfold olift.
      ...
     *)

  End CorrectnessForRewrite.

End ImpEJsonRewrite.
