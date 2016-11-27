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

Require Import LambdaAlg.
Section LambdaNRAEq.

  Context {fruntime:foreign_runtime}.

    Definition lalg_eq (op1 op2:lalg) : Prop :=
    forall
      (h:list(string*string))
      (cenv:bindings)
      (env:bindings)
      (dn_cenv:Forall (fun d => data_normalized h (snd d)) cenv)
      (dn_env:Forall (fun d => data_normalized h (snd d)) env),
       fun_of_lalg h cenv env op1 = fun_of_lalg h cenv env op2.

    Definition lalg_lambda_eq (op1 op2:lalg_lambda) : Prop :=
    forall
      (h:list(string*string))
      (cenv:bindings)
      (env:bindings)
      (dn_cenv:Forall (fun d => data_normalized h (snd d)) cenv)
      (dn_env:Forall (fun d => data_normalized h (snd d)) env)
      (d:data)
      (dn_d:data_normalized h d),
      fun_of_lalg_lambda h cenv env op1 d = fun_of_lalg_lambda h cenv env op2 d.

  Global Instance lalg_equiv : Equivalence lalg_eq.
  Proof.
    constructor.
    - unfold Reflexive, lalg_eq.
      intros; reflexivity.
    - unfold Symmetric, lalg_eq.
      intros. rewrite (H h cenv env dn_cenv dn_env) by trivial; reflexivity.
    - unfold Transitive, lalg_eq.
      intros. rewrite (H h cenv env dn_cenv dn_env) by trivial; rewrite (H0 h cenv env dn_cenv dn_env) by trivial; reflexivity.
  Qed.

  Global Instance lalg_lambda_equiv : Equivalence lalg_lambda_eq.
  Proof.
    constructor.
    - unfold Reflexive, lalg_lambda_eq.
      intros; reflexivity.
    - unfold Symmetric, lalg_lambda_eq.
      intros. rewrite (H h cenv env dn_cenv dn_env) by trivial; reflexivity.
    - unfold Transitive, lalg_lambda_eq.
      intros. rewrite (H h cenv env dn_cenv dn_env) by trivial; rewrite (H0 h cenv env dn_cenv dn_env) by trivial; reflexivity.
  Qed.

  Global Instance lavar_proper : Proper (eq ==> lalg_eq) LAVar.
  Proof.
    unfold Proper, respectful, lalg_eq; intros.
    subst.
    reflexivity.
  Qed.

  Global Instance latable_proper : Proper (eq ==> lalg_eq) LATable.
  Proof.
    unfold Proper, respectful, lalg_eq; intros.
    subst.
    reflexivity.
  Qed.

  Global Instance laconst_proper : Proper (eq ==> lalg_eq) LAConst.
  Proof.
    unfold Proper, respectful, lalg_eq; intros.
    subst.
    reflexivity.
  Qed.

  Global Instance labinop_proper :
    Proper (eq ==> lalg_eq ==> lalg_eq ==> lalg_eq) LABinop.
  Proof.
    unfold Proper, respectful, lalg_eq; intros.
    subst.
    cbn.
    rewrite <- H0, H1 by trivial.
    reflexivity.
  Qed.

  Global Instance launop_proper :
    Proper (eq ==> lalg_eq ==> lalg_eq) LAUnop.
  Proof.
    unfold Proper, respectful, lalg_eq; intros.
    subst.
    cbn.
    rewrite <- H0 by trivial.
    reflexivity.
  Qed.

  Global Instance lamap_proper :
    Proper (lalg_lambda_eq ==> lalg_eq ==> lalg_eq) LAMap.
  Proof.
    unfold Proper, respectful, lalg_eq, lalg_lambda_eq; intros.
    autorewrite with lalg.
    rewrite <- H0 by trivial.
    apply olift_ext; intros.
    apply lift_oncoll_ext; intros; subst.
    f_equal.
    apply rmap_ext; intros.
    apply H; trivial.
    eapply fun_of_lalg_normalized in H1; trivial.
    invcs H1.
    rewrite Forall_forall in H4.
    eauto.
  Qed.

  Global Instance lamapconcat_proper :
    Proper (lalg_lambda_eq ==> lalg_eq ==> lalg_eq) LAMapConcat.
  Proof.
    unfold Proper, respectful, lalg_eq, lalg_lambda_eq; intros.
    autorewrite with lalg.
    rewrite <- H0 by trivial.
    apply olift_ext; intros.
    apply lift_oncoll_ext; intros; subst.
    f_equal.
    apply rmap_concat_ext; intros.
    apply H; trivial.
    eapply fun_of_lalg_normalized in H1; trivial.
    invcs H1.
    rewrite Forall_forall in H4.
    eauto.
  Qed.
  
  Global Instance laproduct_proper :
    Proper (lalg_eq ==> lalg_eq ==> lalg_eq) LAProduct.
  Proof.
    unfold Proper, respectful, lalg_eq, lalg_lambda_eq; intros.
    autorewrite with lalg.
    simpl.
    rewrite <- H, H0 by trivial.
    trivial.
  Qed.

  Global Instance laselect_proper :
    Proper (lalg_lambda_eq ==> lalg_eq ==> lalg_eq) LASelect.
  Proof.
    unfold Proper, respectful, lalg_eq, lalg_lambda_eq; intros.
    autorewrite with lalg.
    rewrite <- H0 by trivial.
    apply olift_ext; intros.
    apply lift_oncoll_ext; intros; subst.
    f_equal.
    apply lift_filter_ext; intros.
    rewrite H; trivial.
    eapply fun_of_lalg_normalized in H1; trivial.
    invcs H1.
    rewrite Forall_forall in H4.
    eauto.
  Qed.

  Global Instance lalambda_proper :
    Proper (eq ==> lalg_eq ==> lalg_lambda_eq) LALambda.
  Proof.
    unfold Proper, respectful, lalg_eq, lalg_lambda_eq; intros.
    subst.
    autorewrite with lalg.
    rewrite H0.
    - reflexivity.
    - trivial.
    - apply Forall_app; auto.
  Qed.

End LambdaNRAEq.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
