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

Require Import List.
Require Import String.
Require Import Utils.
Require Import CommonSystem.
Require Import NRA.
Require Import NRAEq.
Require Import cNRAEnv.
Require Import cNRAEnvEq.
Require Import cNRAEnvIgnore.
Require Import TcNRAEnv.

Section TcNRAEnvIgnore.
  (* Some of algebraic equivalences for NRA with environment *)
  (* Those are valid without type *)

  Local Open Scope nraenv_core_scope.
  
  Lemma tnraenv_core_ignores_env_swap {m:basic_model} (e:nraenv_core) :
    nraenv_core_ignores_env e ->
    forall τc (τin τout τenv₁ τenv₂:rtype),
    e ▷ τin >=> τout ⊣ τc;τenv₁ -> e ▷ τin >=> τout ⊣ τc;τenv₂.
  Proof.
    induction e ; try reflexivity; simpl in *; try congruence; try contradiction; intros.
    - inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0.
      econstructor; eauto.
    - inversion H0; clear H0.
      econstructor; eauto.
  Qed.

  Lemma tnraenv_core_ignores_id_swap {m:basic_model} (e:nraenv_core) :
    nraenv_core_ignores_id e ->
    forall τc (τin₁ τin₂ τout τenv:rtype),
    e ▷ τin₁ >=> τout ⊣ τc;τenv -> e ▷ τin₂ >=> τout ⊣ τc;τenv.
  Proof.
    induction e ; try reflexivity; simpl in *; try congruence; try contradiction; intros.
    - inversion H0; clear H0; intros.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H0; clear H0; subst.
      inversion H; clear H; subst.
      econstructor; eauto.
    - inversion H0; clear H0; subst.
      inversion H; clear H; subst.
      econstructor; eauto.
    - inversion H0; clear H0. econstructor; eauto.
    - inversion H0; clear H0. econstructor; eauto.
    - inversion H; clear H.
      inversion H0; clear H0; subst.
      econstructor; eauto.
    - inversion H0; clear H0; subst.
      econstructor; eauto.
  Qed.

End TcNRAEnvIgnore.

