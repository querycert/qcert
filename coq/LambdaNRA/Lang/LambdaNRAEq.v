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
Require Import LambdaNRA.

Section LambdaNRAEq.

  Context {fruntime:foreign_runtime}.

  Definition lambda_nra_eq (op1 op2:lambda_nra) : Prop :=
    forall
      (h:list(string*string))
      (cenv:bindings)
      (env:bindings)
      (dn_cenv:Forall (fun d => data_normalized h (snd d)) cenv)
      (dn_env:Forall (fun d => data_normalized h (snd d)) env),
      lambda_nra_eval h cenv env op1 = lambda_nra_eval h cenv env op2.

  Definition lnra_lambda_eq (op1 op2:lnra_lambda) : Prop :=
    forall
      (h:list(string*string))
      (cenv:bindings)
      (env:bindings)
      (dn_cenv:Forall (fun d => data_normalized h (snd d)) cenv)
      (dn_env:Forall (fun d => data_normalized h (snd d)) env)
      (d:data)
      (dn_d:data_normalized h d),
      lnra_lambda_eval h cenv env op1 d = lnra_lambda_eval h cenv env op2 d.

  Global Instance lambda_nra_equiv : Equivalence lambda_nra_eq.
  Proof.
    constructor.
    - unfold Reflexive, lambda_nra_eq.
      intros; reflexivity.
    - unfold Symmetric, lambda_nra_eq.
      intros. rewrite (H h cenv env dn_cenv dn_env) by trivial; reflexivity.
    - unfold Transitive, lambda_nra_eq.
      intros. rewrite (H h cenv env dn_cenv dn_env) by trivial; rewrite (H0 h cenv env dn_cenv dn_env) by trivial; reflexivity.
  Qed.

  Global Instance lnra_lambda_equiv : Equivalence lnra_lambda_eq.
  Proof.
    constructor.
    - unfold Reflexive, lnra_lambda_eq.
      intros; reflexivity.
    - unfold Symmetric, lnra_lambda_eq.
      intros. rewrite (H h cenv env dn_cenv dn_env) by trivial; reflexivity.
    - unfold Transitive, lnra_lambda_eq.
      intros. rewrite (H h cenv env dn_cenv dn_env) by trivial; rewrite (H0 h cenv env dn_cenv dn_env) by trivial; reflexivity.
  Qed.

  Global Instance lavar_proper : Proper (eq ==> lambda_nra_eq) LNRAVar.
  Proof.
    unfold Proper, respectful, lambda_nra_eq; intros.
    subst.
    reflexivity.
  Qed.

  Global Instance latable_proper : Proper (eq ==> lambda_nra_eq) LNRATable.
  Proof.
    unfold Proper, respectful, lambda_nra_eq; intros.
    subst.
    reflexivity.
  Qed.

  Global Instance laconst_proper : Proper (eq ==> lambda_nra_eq) LNRAConst.
  Proof.
    unfold Proper, respectful, lambda_nra_eq; intros.
    subst.
    reflexivity.
  Qed.

  Global Instance labinop_proper :
    Proper (eq ==> lambda_nra_eq ==> lambda_nra_eq ==> lambda_nra_eq) LNRABinop.
  Proof.
    unfold Proper, respectful, lambda_nra_eq; intros.
    subst.
    cbn.
    rewrite <- H0, H1 by trivial.
    reflexivity.
  Qed.

  Global Instance launop_proper :
    Proper (eq ==> lambda_nra_eq ==> lambda_nra_eq) LNRAUnop.
  Proof.
    unfold Proper, respectful, lambda_nra_eq; intros.
    subst.
    cbn.
    rewrite <- H0 by trivial.
    reflexivity.
  Qed.

  Global Instance lamap_proper :
    Proper (lnra_lambda_eq ==> lambda_nra_eq ==> lambda_nra_eq) LNRAMap.
  Proof.
    unfold Proper, respectful, lambda_nra_eq, lnra_lambda_eq; intros.
    autorewrite with lambda_nra.
    rewrite <- H0 by trivial.
    apply olift_ext; intros.
    apply lift_oncoll_ext; intros; subst.
    f_equal.
    apply lift_map_ext; intros.
    apply H; trivial.
    eapply lambda_nra_eval_normalized in H1; trivial.
    invcs H1.
    rewrite Forall_forall in H4.
    eauto.
  Qed.

  Global Instance lamapconcat_proper :
    Proper (lnra_lambda_eq ==> lambda_nra_eq ==> lambda_nra_eq) LNRAMapProduct.
  Proof.
    unfold Proper, respectful, lambda_nra_eq, lnra_lambda_eq; intros.
    autorewrite with lambda_nra.
    rewrite <- H0 by trivial.
    apply olift_ext; intros.
    apply lift_oncoll_ext; intros; subst.
    f_equal.
    apply omap_product_ext; intros.
    apply H; trivial.
    eapply lambda_nra_eval_normalized in H1; trivial.
    invcs H1.
    rewrite Forall_forall in H4.
    eauto.
  Qed.
  
  Global Instance laproduct_proper :
    Proper (lambda_nra_eq ==> lambda_nra_eq ==> lambda_nra_eq) LNRAProduct.
  Proof.
    unfold Proper, respectful, lambda_nra_eq, lnra_lambda_eq; intros.
    autorewrite with lambda_nra.
    simpl.
    rewrite <- H, H0 by trivial.
    trivial.
  Qed.

  Global Instance lafilter_proper :
    Proper (lnra_lambda_eq ==> lambda_nra_eq ==> lambda_nra_eq) LNRAFilter.
  Proof.
    unfold Proper, respectful, lambda_nra_eq, lnra_lambda_eq; intros.
    autorewrite with lambda_nra.
    rewrite <- H0 by trivial.
    apply olift_ext; intros.
    apply lift_oncoll_ext; intros; subst.
    f_equal.
    apply lift_filter_ext; intros.
    rewrite H; trivial.
    eapply lambda_nra_eval_normalized in H1; trivial.
    invcs H1.
    rewrite Forall_forall in H4.
    eauto.
  Qed.

  Global Instance lalambda_proper :
    Proper (eq ==> lambda_nra_eq ==> lnra_lambda_eq) LNRALambda.
  Proof.
    unfold Proper, respectful, lambda_nra_eq, lnra_lambda_eq; intros.
    subst.
    autorewrite with lambda_nra.
    rewrite H0.
    - reflexivity.
    - trivial.
    - apply Forall_sorted; apply Forall_app; auto.
  Qed.

End LambdaNRAEq.

