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

  Fixpoint lambda_nra_to_nraenv (op:lambda_nra) : nraenv :=
    match op with
    | LNRAVar x => NRAEnvUnop (ADot x) NRAEnvEnv
    | LNRATable x => NRAEnvGetConstant x
    | LNRAConst d => NRAEnvConst d
    | LNRABinop b op1 op2 => NRAEnvBinop b (lambda_nra_to_nraenv op1) (lambda_nra_to_nraenv op2)
    | LNRAUnop u op1 => NRAEnvUnop u (lambda_nra_to_nraenv op1)
    | LNRAMap lop1 op2 => NRAEnvMap (nraenv_of_lnra_lambda lop1) (lambda_nra_to_nraenv op2)
    | LNRAMapConcat lop1 op2 => NRAEnvMapConcat (nraenv_of_lnra_lambda lop1) (lambda_nra_to_nraenv op2)
    | LNRAProduct op1 op2 => NRAEnvProduct (lambda_nra_to_nraenv op1) (lambda_nra_to_nraenv op2)
    | LNRAFilter lop1 op2 => NRAEnvSelect (nraenv_of_lnra_lambda lop1) (lambda_nra_to_nraenv op2)
    end
  with nraenv_of_lnra_lambda (lop:lnra_lambda) : nraenv :=
    match lop with
    | LNRALambda x op =>
      NRAEnvAppEnv (lambda_nra_to_nraenv op) (NRAEnvBinop AConcat NRAEnvEnv (NRAEnvUnop (ARec x) NRAEnvID))
    end.

  Context (h:brand_relation_t).
  Context (global_env:bindings).

  Lemma lambda_nra_to_nraenv_never_uses_id :
    forall env:bindings, forall q:lambda_nra, forall d1 d2:data,
          nraenv_eval h global_env
                      (lambda_nra_to_nraenv q) (drec env) d1 =
          nraenv_eval h global_env
                      (lambda_nra_to_nraenv q) (drec env) d2.
  Proof.
    lambda_nra_cases (induction q) Case
    ; intros; unfold nraenv_eval in *; simpl in *
    ; autorewrite with lambda_nra; try reflexivity.
    - Case "LNRABinop"%string.
      rewrite (IHq1 d1 d2).
      rewrite (IHq2 d1 d2).
      reflexivity.
    - Case "LNRAUnop"%string.
      rewrite (IHq d1 d2).
      reflexivity.
    - Case "LNRAMap"%string.
      rewrite (IHq2 d1 d2).
      reflexivity.
    - Case "LNRAMapConcat"%string.
      rewrite (IHq2 d1 d2).
      reflexivity.
    - Case "LNRAProduct"%string.
      rewrite (IHq1 d1 d2).
      rewrite (IHq2 d1 d2).
      reflexivity.
    - Case "LNRAFilter"%string.
      rewrite (IHq2 d1 d2).
      reflexivity.
  Qed.

  Theorem lambda_nra_to_nraenv_correct :
    forall q:lambda_nra, forall env:bindings, forall d:data,
      lambda_nra_eval h global_env env q =
      nraenv_eval h global_env
                  (lambda_nra_to_nraenv q) (drec env) d.
  Proof.
    lambda_nra_cases (induction q) Case
    ; intros; unfold nraenv_eval in *; simpl in *
    ; autorewrite with lambda_nra; try reflexivity.
    - Case "LNRABinop"%string.
      rewrite (IHq1 _ d).
      rewrite (IHq2 _ d).
      reflexivity.
    - Case "LNRAUnop"%string.
      rewrite (IHq _ d).
      reflexivity.
    - Case "LNRAMap"%string.
      rewrite <- (IHq2 _ d).
      simpl.
      apply olift_ext; intros.
      apply lift_oncoll_ext; intros.
      subst.
      f_equal.
      apply rmap_ext; intros.
      autorewrite with lambda_nra.
      rewrite (IHq1 _ x).
      admit.
    - Case "LNRAMapConcat"%string.
      admit.
    - Case "LNRAProduct"%string.
      admit.
    - Case "LNRAFilter"%string.
      admit.
  Admitted.
  
  Theorem nraenv_of_lnra_lambda_correct :
    forall env:bindings, forall lop:lnra_lambda, forall d:data,
      lnra_lambda_eval h global_env env lop d =
      nraenv_eval h global_env
                  (nraenv_of_lnra_lambda lop) (drec env) d.
  Proof.
    destruct lop.
    revert env s.
    lambda_nra_cases (induction l) Case
    ; intros; unfold nraenv_eval in *; simpl in *
    ; autorewrite with lambda_nra.
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
    nraenv_eval h global_env Qe (drec nil) input.

  Theorem eval_nraenv_q_correct (Q:lambda_nra -> lambda_nra) (input:data) :
    eval_lnra_lambda h global_env Q input = eval_nraenv_q (nraenv_of_lnra_lambda (q_to_lambda Q)) input.
  Proof.
    unfold eval_lnra_lambda, eval_nraenv_q.
    rewrite nraenv_of_lnra_lambda_correct.
    reflexivity.
  Qed.

End LambdaNRAtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
