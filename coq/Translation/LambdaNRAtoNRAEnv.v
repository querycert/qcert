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

  Fixpoint nraenv_of_lnra (op:lnra) : nraenv :=
    match op with
    | LNRAVar x => NRAEnvUnop (ADot x) NRAEnvEnv
    | LNRATable x => NRAEnvGetConstant x
    | LNRAConst d => NRAEnvConst d
    | LNRABinop b op1 op2 => NRAEnvBinop b (nraenv_of_lnra op1) (nraenv_of_lnra op2)
    | LNRAUnop u op1 => NRAEnvUnop u (nraenv_of_lnra op1)
    | LNRAMap lop1 op2 => NRAEnvMap (nraenv_of_lnra_lambda lop1) (nraenv_of_lnra op2)
    | LNRAMapConcat lop1 op2 => NRAEnvMapConcat (nraenv_of_lnra_lambda lop1) (nraenv_of_lnra op2)
    | LNRAProduct op1 op2 => NRAEnvProduct (nraenv_of_lnra op1) (nraenv_of_lnra op2)
    | LNRAFilter lop1 op2 => NRAEnvSelect (nraenv_of_lnra_lambda lop1) (nraenv_of_lnra op2)
    end
  with nraenv_of_lnra_lambda (lop:lnra_lambda) : nraenv :=
    match lop with
    | LNRALambda x op =>
      NRAEnvAppEnv (nraenv_of_lnra op) (NRAEnvBinop AConcat NRAEnvEnv (NRAEnvUnop (ARec x) NRAEnvID))
    end.

  Context (h:brand_relation_t).
  Context (constant_env:list (string*data)).
    
  Theorem nraenv_of_lnra_lambda_correct (env:bindings) (lop:lnra_lambda) (d:data) :
    lnra_eval_lambda h constant_env env lop d = nraenv_eval h constant_env (nraenv_of_lnra_lambda lop) (drec env) d.
  Proof.
    destruct lop.
    revert env s d.
    lnra_cases (induction l) Case
    ; intros; unfold nraenv_eval in *; simpl in *
    ; autorewrite with lnra.
    - Case "LNRAVar"%string.
      unfold edot, rec_concat_sort.
      rewrite assoc_lookupr_drec_sort.
      trivial.
    - Case "LNRATable"%string.
      unfold edot, rec_concat_sort.
      trivial.
    - Case "LNRAConst"%string.
      trivial.
    - Case "LNRABinop"%string.
      rewrite <- IHl1, <- IHl2.
      trivial.
    - Case "LNRAUnop"%string.
      rewrite <- IHl.
      trivial.
    - Case "LNRAMap"%string.
      rewrite <- IHl2.
      apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      subst.
      f_equal.
      apply rmap_ext; intros.
      rewrite IHl1.
      rewrite rec_sort_rec_sort_app1.
      trivial.
    - Case "LNRAMapConcat"%string.
      rewrite <- IHl2.
      apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      subst.
      f_equal.
      apply rmap_concat_ext; intros.
      rewrite IHl1.
      rewrite rec_sort_rec_sort_app1.
      trivial.
    - Case "LNRAProduct"%string.
      rewrite <- IHl1, <- IHl2.
      trivial.
    - Case "LNRAFilter"%string.
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

  Theorem eval_nraenv_q_correct (Q:lnra -> lnra) (input:data) :
    eval_q h constant_env Q input = eval_nraenv_q (nraenv_of_lnra_lambda (q_to_lambda Q)) input.
  Proof.
    unfold eval_q, eval_nraenv_q.
    rewrite nraenv_of_lnra_lambda_correct.
    reflexivity.
  Qed.

End LambdaNRAtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
