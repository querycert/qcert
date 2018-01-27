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
Require Import CommonSystem.
Require Import NRAEnvSystem.
Require Import LambdaNRASystem.
Require Import LambdaNRAtoNRAEnv.

Section TLambdaNRAtoNRAEnv.

  Context {m:basic_model}.

  Theorem tlambda_nra_sem_correct
          {τcenv} {Γ:tbindings} {τ₀ τ} (e:lambda_nra) pf :
    lambda_nra_type τcenv e Γ τ ->
    nraenv_type τcenv (lambda_nra_to_nraenv e) (Rec Closed Γ pf) τ₀ τ.
  Proof.
    revert Γ pf τ₀ τ.
    induction e; intros Γ pf τ₀ τ lnt
    ; invcs lnt
      ; autorewrite with lambda_nra lambda_nra_to_nraenv
      ; simpl.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor. fold nraenv_to_nraenv_core.
      + eauto.
      + apply IHe1; trivial.
      + apply IHe2; trivial.
    - econstructor; fold nraenv_to_nraenv_core.
      + eauto.
      + apply IHe; trivial.
    - econstructor; fold nraenv_to_nraenv_core
      ; [ | apply IHe2; eassumption].
      econstructor.
      + econstructor; [ | eauto | eauto ]; eauto.
      + apply TLLambda_inv in H1.
        eapply IHe1; eauto.
    - econstructor; fold nraenv_to_nraenv_core
      ; [ | apply IHe2; eassumption | reflexivity].
      econstructor.
      + econstructor; [ | eauto | eauto ]; eauto.
      + apply TLLambda_inv in H1.
        eapply IHe1; eauto.
    - econstructor; fold nraenv_to_nraenv_core.
      + apply IHe1; eauto.
      + apply IHe2; eauto.
      + reflexivity.
    - econstructor; fold nraenv_to_nraenv_core
      ; [ | apply IHe2; eassumption].
      econstructor.
      + econstructor; [ | eauto | eauto ]; eauto.
      + apply TLLambda_inv in H1.
        eapply IHe1; eauto.
    Grab Existential Variables.
    solve[eauto].
    solve[eauto].
    solve[eauto].
    solve[eauto].
    solve[eauto].
    solve[eauto].
  Qed.

  Lemma tlambda_nra_ignores_input_type {τcenv} {Γrec} {τ₁ τ₂ τ} (e:lambda_nra) :
    nraenv_type τcenv (lambda_nra_to_nraenv e) Γrec τ₁ τ ->
    nraenv_type τcenv (lambda_nra_to_nraenv e) Γrec τ₂ τ.
  Proof.
    revert Γrec τ₁ τ₂ τ.
    induction e; intros Γrec τ₁ τ₂ τ  lnt
    ; invcs lnt
    ; autorewrite with lambda_nra lambda_nra_to_nraenv
    ; simpl
    ; econstructor; fold nraenv_to_nraenv_core in *; eauto
    ; try solve [eapply IHe; eauto | eapply IHe1; eauto | eapply IHe2; eauto].
    - invcs H5; eauto.
  Qed.
  
  Theorem tlambda_nra_sem_correct_back
          {τcenv} {Γ:tbindings} {τ₀ τ} (e:lambda_nra) pf :
    nraenv_type τcenv (lambda_nra_to_nraenv e) (Rec Closed Γ pf) τ₀ τ ->
    lambda_nra_type τcenv e Γ τ.
  Proof.
    revert Γ τ₀ τ pf.
    induction e; intros Γ τ₀ τ pf lnt
    ; invcs lnt
    ; autorewrite with lambda_nra lambda_nra_to_nraenv
    ; simpl
    ; econstructor; fold nraenv_to_nraenv_core in *; eauto.
    - invcs H5.
      invcs H1; rtype_equalizer; subst.
      trivial.
    - constructor.
      invcs H1.
      invcs H2.
      invcs H10.
      invcs H8.
      invcs H9.
      invcs H1.
      invcs H3.
      rtype_equalizer; subst.
      destruct τ₂0; simpl in H0; try discriminate.
      destruct τ₂0; simpl in H0; try discriminate.
      invcs H0.
      rtype_equalizer; subst.
      destruct p.
      eapply IHe1.
      eapply H7.
    - constructor.
      invcs H1.
      invcs H3.
      invcs H9.
      invcs H10.
      invcs H8.
      invcs H1.
      invcs H4.
      rtype_equalizer; subst.
      destruct τ₂0; simpl in H0; try discriminate.
      destruct τ₂0; simpl in H0; try discriminate.
      destruct p.
      invcs H0.
      apply Rec₀_eq_proj1_Rec in H3.
      destruct H3; subst.
      rewrite (is_list_sorted_ext _ _ pf1 x).
      eapply IHe1.
      eapply H7.
    - invcs H1.
      invcs H2.
      invcs H9.
      invcs H10.
      invcs H8.
      invcs H1.
      invcs H3.
      rtype_equalizer; subst.
      destruct τ₂; simpl in H0; try discriminate.
      destruct τ₂; simpl in H0; try discriminate.
      destruct p.
      invcs H0.
      rtype_equalizer; subst.
      constructor.
      eapply IHe1.
      eapply H7.
  Qed.
  
End TLambdaNRAtoNRAEnv.

