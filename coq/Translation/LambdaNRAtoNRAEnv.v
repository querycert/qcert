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

  Require Import LambdaNRA NRAEnvRuntime.

  Context {fruntime:foreign_runtime}.

  Fixpoint nraenv_of_lalg (op:lalg) : nraenv :=
    match op with
    | LAVar x => NRAEnvUnop (ADot x) NRAEnvEnv
    | LATable x => NRAEnvGetConstant x
    | LAConst d => NRAEnvConst d
    | LABinop b op1 op2 => NRAEnvBinop b (nraenv_of_lalg op1) (nraenv_of_lalg op2)
    | LAUnop u op1 => NRAEnvUnop u (nraenv_of_lalg op1)
    | LAMap lop1 op2 => NRAEnvMap (nraenv_of_lalg_lambda lop1) (nraenv_of_lalg op2)
    | LAMapConcat lop1 op2 => NRAEnvMapConcat (nraenv_of_lalg_lambda lop1) (nraenv_of_lalg op2)
    | LAProduct op1 op2 => NRAEnvProduct (nraenv_of_lalg op1) (nraenv_of_lalg op2)
    | LASelect lop1 op2 => NRAEnvSelect (nraenv_of_lalg_lambda lop1) (nraenv_of_lalg op2)
    end
  with nraenv_of_lalg_lambda (lop:lalg_lambda) : nraenv :=
    match lop with
    | LALambda x op =>
      NRAEnvAppEnv (nraenv_of_lalg op) (NRAEnvBinop AConcat NRAEnvEnv (NRAEnvUnop (ARec x) NRAEnvID))
    end.

  Context (h:brand_relation_t).
  Context (constant_env:list (string*data)).
    
  Theorem nraenv_of_lalg_lambda_correct (env:bindings) (lop:lalg_lambda) (d:data) :
    fun_of_lalg_lambda h constant_env env lop d = nraenv_eval h constant_env (nraenv_of_lalg_lambda lop) (drec env) d.
  Proof.
    destruct lop.
    revert env s d.
    lalg_cases (induction l) Case
    ; intros; unfold nraenv_eval in *; simpl in *
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

  Definition eval_nraenv_q (Qe:nraenv) (input:data) : option data :=
    nraenv_eval h constant_env Qe (drec nil) input.

  Theorem eval_nraenv_q_correct (Q:lalg -> lalg) (input:data) :
    eval_q h constant_env Q input = eval_nraenv_q (nraenv_of_lalg_lambda (q_to_lambda Q)) input.
  Proof.
    unfold eval_q, eval_nraenv_q.
    rewrite nraenv_of_lalg_lambda_correct.
    reflexivity.
  Qed.

End LambdaNRAtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
