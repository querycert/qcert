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

Require Import String.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.

Require Import Utils BasicRuntime.

Section LambdaNRAtoNRAEnv.

  Require Import LambdaAlg NRAEnvRuntime.

  Context {fruntime:foreign_runtime}.

  Fixpoint algenv_of_lalg (op:lalg) : algenv :=
    match op with
    | LAVar x => ANUnop (ADot x) ANEnv
    | LATable x => ANGetConstant x
    | LAConst d => ANConst d
    | LABinop b op1 op2 => ANBinop b (algenv_of_lalg op1) (algenv_of_lalg op2)
    | LAUnop u op1 => ANUnop u (algenv_of_lalg op1)
    | LAMap lop1 op2 => ANMap (algenv_of_lalg_lambda lop1) (algenv_of_lalg op2)
    | LAMapConcat lop1 op2 => ANMapConcat (algenv_of_lalg_lambda lop1) (algenv_of_lalg op2)
    | LAProduct op1 op2 => ANProduct (algenv_of_lalg op1) (algenv_of_lalg op2)
    | LASelect lop1 op2 => ANSelect (algenv_of_lalg_lambda lop1) (algenv_of_lalg op2)
    end
  with algenv_of_lalg_lambda (lop:lalg_lambda) : algenv :=
    match lop with
    | LALambda x op =>
      ANAppEnv (algenv_of_lalg op) (ANBinop AConcat ANEnv (ANUnop (ARec x) ANID))
    end.

  Context (h:brand_relation_t).
  Context (constant_env:list (string*data)).
    
  Theorem algenv_of_lalg_lambda_correct (env:bindings) (lop:lalg_lambda) (d:data) :
    fun_of_lalg_lambda h constant_env env lop d = fun_of_algenv h constant_env (algenv_of_lalg_lambda lop) (drec env) d.
  Proof.
    destruct lop.
    revert env s d.
    lalg_cases (induction l) Case
    ; intros; simpl in *
    ; autorewrite with lalg.
    - Case "LAVar"%string.
      unfold edot, rec_concat_sort.
      rewrite assoc_lookupr_drec_sort.
      trivial.
    - Case "LATable"%string.
      unfold edot, rec_concat_sort.
      trivial.
    - Case "LAConst"%string.
      trivial.
    - Case "LABinop"%string.
      rewrite <- IHl1, <- IHl2.
      trivial.
    - Case "LAUnop"%string.
      rewrite <- IHl.
      trivial.
    - Case "LAMap"%string.
      rewrite <- IHl2.
      apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      subst.
      f_equal.
      apply rmap_ext; intros.
      rewrite IHl1.
      rewrite rec_sort_rec_sort_app1.
      trivial.
    - Case "LAMapConcat"%string.
      rewrite <- IHl2.
      apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      subst.
      f_equal.
      apply rmap_concat_ext; intros.
      rewrite IHl1.
      rewrite rec_sort_rec_sort_app1.
      trivial.
    - Case "LAProduct"%string.
      rewrite <- IHl1, <- IHl2.
      trivial.
    - Case "LASelect"%string.
      rewrite <- IHl2.
      apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      subst.
      f_equal.
      apply lift_filter_ext; intros.
      rewrite IHl1.
      rewrite rec_sort_rec_sort_app1.
      trivial.
  Qed.

  Definition eval_nraenv_q (Qe:algenv) (input:data) : option data :=
    fun_of_algenv h constant_env Qe (drec nil) input.

  Theorem eval_nraenv_q_correct (Q:lalg -> lalg) (input:data) :
    eval_q h constant_env Q input = eval_nraenv_q (algenv_of_lalg_lambda (q_to_lambda Q)) input.
  Proof.
    unfold eval_q, eval_nraenv_q.
    rewrite algenv_of_lalg_lambda_correct.
    reflexivity.
  Qed.

End LambdaNRAtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
