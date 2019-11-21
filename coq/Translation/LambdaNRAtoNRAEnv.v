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
Require Import Utils.
Require Import CommonRuntime.
Require Import LambdaNRARuntime.
Require Import NRAEnvRuntime.

Section LambdaNRAtoNRAEnv.
  Context {fruntime:foreign_runtime}.

  Fixpoint lambda_nra_to_nraenv (op:lambda_nra) : nraenv :=
    match op with
    | LNRAVar x => NRAEnvUnop (OpDot x) NRAEnvEnv
    | LNRATable x => NRAEnvGetConstant x
    | LNRAConst d => NRAEnvConst d
    | LNRABinop b op1 op2 => NRAEnvBinop b (lambda_nra_to_nraenv op1) (lambda_nra_to_nraenv op2)
    | LNRAUnop u op1 => NRAEnvUnop u (lambda_nra_to_nraenv op1)
    | LNRAMap lop1 op2 => NRAEnvMap (nraenv_of_lnra_lambda lop1) (lambda_nra_to_nraenv op2)
    | LNRAMapProduct lop1 op2 => NRAEnvMapProduct (nraenv_of_lnra_lambda lop1) (lambda_nra_to_nraenv op2)
    | LNRAProduct op1 op2 => NRAEnvProduct (lambda_nra_to_nraenv op1) (lambda_nra_to_nraenv op2)
    | LNRAFilter lop1 op2 => NRAEnvSelect (nraenv_of_lnra_lambda lop1) (lambda_nra_to_nraenv op2)
    end
  with nraenv_of_lnra_lambda (lop:lnra_lambda) : nraenv :=
    match lop with
    | LNRALambda x op =>
      NRAEnvAppEnv (lambda_nra_to_nraenv op)
                   (NRAEnvBinop OpRecConcat NRAEnvEnv (NRAEnvUnop (OpRec x) NRAEnvID))
    end.

  Lemma  lambda_nra_to_nraenv_var_eq x :
      lambda_nra_to_nraenv (LNRAVar x) = 
      NRAEnvUnop (OpDot x) NRAEnvEnv.
  Proof.
    reflexivity.
  Qed.
  
  Lemma  lambda_nra_to_nraenv_table_eq x :
    lambda_nra_to_nraenv (LNRATable x) = NRAEnvGetConstant x.
  Proof.
    reflexivity.
  Qed.
  
  
  Lemma  lambda_nra_to_nraenv_const_eq d :
    lambda_nra_to_nraenv (LNRAConst d) = NRAEnvConst d.
  Proof.
    reflexivity.
  Qed.

  Lemma  lambda_nra_to_nraenv_binop_eq b op1 op2 :
    lambda_nra_to_nraenv (LNRABinop b op1 op2) =
    NRAEnvBinop b (lambda_nra_to_nraenv op1) (lambda_nra_to_nraenv op2).
  Proof.
    reflexivity.
  Qed.

  Lemma  lambda_nra_to_nraenv_unop_eq u op :
    lambda_nra_to_nraenv (LNRAUnop u op) =
    NRAEnvUnop u (lambda_nra_to_nraenv op).
  Proof.
    reflexivity.
  Qed.

  Lemma  lambda_nra_to_nraenv_map_eq lop1 op2 :
    lambda_nra_to_nraenv (LNRAMap lop1 op2) = NRAEnvMap (nraenv_of_lnra_lambda lop1) (lambda_nra_to_nraenv op2).
  Proof.
    reflexivity.
  Qed.

  Lemma  lambda_nra_to_nraenv_map_concat_eq lop1 op2 :
    lambda_nra_to_nraenv (LNRAMapProduct lop1 op2) = NRAEnvMapProduct (nraenv_of_lnra_lambda lop1) (lambda_nra_to_nraenv op2).
  Proof.
    reflexivity.
  Qed.

  Lemma  lambda_nra_to_nraenv_product_eq op1 op2 :
    lambda_nra_to_nraenv (LNRAProduct op1 op2) = NRAEnvProduct (lambda_nra_to_nraenv op1) (lambda_nra_to_nraenv op2).
  Proof.
    reflexivity.
  Qed.

  Lemma  lambda_nra_to_nraenv_filter_eq lop1 op2 :
    lambda_nra_to_nraenv (LNRAFilter lop1 op2) = NRAEnvSelect (nraenv_of_lnra_lambda lop1) (lambda_nra_to_nraenv op2).
  Proof.
    reflexivity.
  Qed.

  Lemma  lambda_nra_to_nraenv_lambda_eq x op :
    nraenv_of_lnra_lambda (LNRALambda x op) =
    NRAEnvAppEnv (lambda_nra_to_nraenv op)
                 (NRAEnvBinop OpRecConcat NRAEnvEnv (NRAEnvUnop (OpRec x) NRAEnvID)).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite @lambda_nra_to_nraenv_var_eq : lambda_nra_to_nraenv.
  Hint Rewrite @lambda_nra_to_nraenv_table_eq : lambda_nra_to_nraenv.
  Hint Rewrite @lambda_nra_to_nraenv_const_eq : lambda_nra_to_nraenv.
  Hint Rewrite @lambda_nra_to_nraenv_binop_eq : lambda_nra_to_nraenv.
  Hint Rewrite @lambda_nra_to_nraenv_unop_eq : lambda_nra_to_nraenv.
  Hint Rewrite @lambda_nra_to_nraenv_map_eq : lambda_nra_to_nraenv.
  Hint Rewrite @lambda_nra_to_nraenv_map_concat_eq : lambda_nra_to_nraenv.
  Hint Rewrite @lambda_nra_to_nraenv_product_eq : lambda_nra_to_nraenv.
  Hint Rewrite @lambda_nra_to_nraenv_filter_eq : lambda_nra_to_nraenv.
  Hint Rewrite @lambda_nra_to_nraenv_lambda_eq : lambda_nra_to_nraenv.

  Context (h:brand_relation_t).

  Section Translation.
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
      - Case "LNRAMapProduct"%string.
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

    (** Evaluation for lambda nra is the same as evaluation for translated expression to NRAEnv
      - Note that only the global and local environments matter.
        The 'input value' for NRA (d in the theorem) is not used on the LambdaNRA side.
        This is consistent with the previous theorem showing that any 'd' does not matter.
     *)
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
        apply lift_map_ext; intros.
        autorewrite with lambda_nra.
        rewrite (IHq1 _ x).
        reflexivity.
      - Case "LNRAMapProduct"%string.
        rewrite <- (IHq2 _ d).
        apply olift_ext; intros.
        apply lift_oncoll_ext; intros.
        subst.
        f_equal.
        apply omap_product_ext; intros.
        autorewrite with lambda_nra.
        rewrite (IHq1 _ x).
        reflexivity.
      - Case "LNRAProduct"%string.
        rewrite (IHq1 _ d).
        rewrite (IHq2 _ d).
        reflexivity.
      - Case "LNRAFilter"%string.
        rewrite <- (IHq2 _ d).
        apply olift_ext; intros.
        apply lift_oncoll_ext; intros.
        subst.
        f_equal.
        apply lift_filter_ext; intros.
        autorewrite with lambda_nra.
        rewrite (IHq1 _ x).
        reflexivity.
    Qed.
  
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
        apply lift_map_ext; intros.
        rewrite IHl1.
        rewrite rec_sort_rec_sort_app1.
        trivial.
      - Case "LNRAMapProduct"%string.
        rewrite <- IHl2.
        apply olift_ext; intros.
        apply lift_oncoll_ext; intros.
        subst.
        f_equal.
        apply omap_product_ext; intros.
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
      lnra_lambda_eval_top h Q global_env input = eval_nraenv_q (nraenv_of_lnra_lambda (q_to_lambda Q)) input.
    Proof.
      unfold lnra_lambda_eval_top, eval_nraenv_q.
      rewrite nraenv_of_lnra_lambda_correct.
      reflexivity.
    Qed.
  End Translation.

  Section Top.
    Definition lambda_nra_to_nraenv_top (q:lambda_nra) : nraenv :=
      lambda_nra_to_nraenv q.

    Theorem lambda_nra_to_nraenv_top_correct :
      forall q:lambda_nra, forall global_env:bindings,
          lambda_nra_eval_top h q global_env =
          nraenv_eval_top h (lambda_nra_to_nraenv_top q) global_env.
    Proof.
      intros.
      unfold lambda_nra_to_nraenv_top.
      unfold lambda_nra_eval_top.
      unfold nraenv_eval_top.
      rewrite (lambda_nra_to_nraenv_correct (rec_sort global_env) q nil dunit).
      reflexivity.
    Qed.
      
  End Top.

End LambdaNRAtoNRAEnv.

Hint Rewrite @lambda_nra_to_nraenv_var_eq : lambda_nra_to_nraenv.
Hint Rewrite @lambda_nra_to_nraenv_table_eq : lambda_nra_to_nraenv.
Hint Rewrite @lambda_nra_to_nraenv_const_eq : lambda_nra_to_nraenv.
Hint Rewrite @lambda_nra_to_nraenv_binop_eq : lambda_nra_to_nraenv.
Hint Rewrite @lambda_nra_to_nraenv_unop_eq : lambda_nra_to_nraenv.
Hint Rewrite @lambda_nra_to_nraenv_map_eq : lambda_nra_to_nraenv.
Hint Rewrite @lambda_nra_to_nraenv_map_concat_eq : lambda_nra_to_nraenv.
Hint Rewrite @lambda_nra_to_nraenv_product_eq : lambda_nra_to_nraenv.
Hint Rewrite @lambda_nra_to_nraenv_filter_eq : lambda_nra_to_nraenv.
Hint Rewrite @lambda_nra_to_nraenv_lambda_eq : lambda_nra_to_nraenv.

