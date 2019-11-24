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

Require Import Bool.
Require Import List.
Require Import String.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNRAEnvIgnore.
Require Import NRAEnv.

Section NRAEnvIgnore.
  (* Some of algebraic equivalences for NRA with environment *)
  (* Those are valid without type *)

  Local Open Scope nraenv_scope.
  
  (** Some infrastructure for rewrites *)

  Context {fruntime:foreign_runtime}.

  Fixpoint is_nra (e:nraenv) : Prop :=
    match e with
    | NRAEnvGetConstant _ => False
    | NRAEnvID => True
    | NRAEnvConst rd => True
    | NRAEnvBinop bop e1 e2 => (is_nra e1) /\ (is_nra e2)
    | NRAEnvUnop uop e1 => is_nra e1
    | NRAEnvMap e1 e2 => (is_nra e1) /\ (is_nra e2)
    | NRAEnvMapProduct e1 e2 => (is_nra e1) /\ (is_nra e2)
    | NRAEnvProduct e1 e2 => (is_nra e1) /\ (is_nra e2)
    | NRAEnvSelect e1 e2 => (is_nra e1) /\ (is_nra e2)
    | NRAEnvDefault e1 e2 => (is_nra e1) /\ (is_nra e2)
    | NRAEnvEither e1 e2 => (is_nra e1) /\ (is_nra e2)
    | NRAEnvEitherConcat e1 e2 => (is_nra e1) /\ (is_nra e2)
    | NRAEnvApp e1 e2 => (is_nra e1) /\ (is_nra e2)
    | NRAEnvEnv => False
    | NRAEnvAppEnv e1 e2 => False
    | NRAEnvMapEnv e1 => False
    (* Those are additional operators *)
    | NRAEnvFlatMap e1 e2 => (is_nra e1) /\ (is_nra e2)
    | NRAEnvJoin e1 e2 e3 =>  (is_nra e1) /\ (is_nra e2) /\ (is_nra e3)
    | NRAEnvNaturalJoin e1 e2 =>  (is_nra e1) /\ (is_nra e2)
    | NRAEnvProject _ e1 => (is_nra e1)
    | NRAEnvGroupBy _ _ e1 => (is_nra e1)
    | NRAEnvUnnest _ _ e1 => (is_nra e1)
    end.

  Fixpoint is_nra_fun (e:nraenv) : bool :=
    match e with
    | NRAEnvGetConstant _ => false
    | NRAEnvID => true
    | NRAEnvConst rd => true
    | NRAEnvBinop bop e1 e2 => andb (is_nra_fun e1) (is_nra_fun e2)
    | NRAEnvUnop uop e1 => is_nra_fun e1
    | NRAEnvMap e1 e2 => andb (is_nra_fun e1) (is_nra_fun e2)
    | NRAEnvMapProduct e1 e2 => andb (is_nra_fun e1) (is_nra_fun e2)
    | NRAEnvProduct e1 e2 => andb (is_nra_fun e1) (is_nra_fun e2)
    | NRAEnvSelect e1 e2 => andb (is_nra_fun e1) (is_nra_fun e2)
    | NRAEnvDefault e1 e2 => andb (is_nra_fun e1) (is_nra_fun e2)
    | NRAEnvEither e1 e2 => andb (is_nra_fun e1) (is_nra_fun e2)
    | NRAEnvEitherConcat e1 e2 => andb (is_nra_fun e1) (is_nra_fun e2)
    | NRAEnvApp e1 e2 => andb (is_nra_fun e1) (is_nra_fun e2)
    | NRAEnvEnv => false
    | NRAEnvAppEnv e1 e2 => false
    | NRAEnvMapEnv e1 => false
    (* Those are additional operators *)
    | NRAEnvFlatMap e1 e2 => andb (is_nra_fun e1) (is_nra_fun e2)
    | NRAEnvJoin e1 e2 e3 =>  andb (is_nra_fun e1) (andb (is_nra_fun e2) (is_nra_fun e3))
    | NRAEnvNaturalJoin e1 e2 =>  andb (is_nra_fun e1) (is_nra_fun e2)
    | NRAEnvProject _ e1 => (is_nra_fun e1)
    | NRAEnvGroupBy _ _ e1 => (is_nra_fun e1)
    | NRAEnvUnnest _ _ e1 => (is_nra_fun e1)
    end.

  Lemma is_nra_eq (e:nraenv):
    is_nra e <-> (is_nra_fun e = true).
  Proof.
    induction e; split; simpl; intros; try auto; try congruence;
    try (rewrite IHe1 in H; rewrite IHe2 in H;
         elim H; clear H; intros;
         rewrite H; rewrite H0; reflexivity);
    try (rewrite andb_true_inversion in H;
         elim H; clear H; intros;
         rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
         split; assumption);
    try (rewrite IHe in H; assumption);
    try (rewrite <- IHe in H; assumption).
    - rewrite IHe1 in H; rewrite IHe2 in H; rewrite IHe3 in H.
      elim H; clear H; intros.
      elim H0; clear H0; intros.
      rewrite H; rewrite H0; rewrite H1.
      auto.
    - rewrite andb_true_inversion in H.
      rewrite andb_true_inversion in H.
      elim H; clear H; intros.
      elim H0; clear H0; intros.
      rewrite <- IHe1 in H; rewrite <- IHe2 in H0; rewrite <- IHe3 in H1.
      auto.
  Qed.

  Fixpoint nraenv_ignores_env (e:nraenv) : Prop :=
    match e with
    | NRAEnvGetConstant _ => True
    | NRAEnvID => True
    | NRAEnvConst rd => True
    | NRAEnvBinop bop e1 e2 => (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2)
    | NRAEnvUnop uop e1 => nraenv_ignores_env e1
    | NRAEnvMap e1 e2 => (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2)
    | NRAEnvMapProduct e1 e2 => (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2)
    | NRAEnvProduct e1 e2 => (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2)
    | NRAEnvSelect e1 e2 => (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2)
    | NRAEnvDefault e1 e2 => (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2)
    | NRAEnvEither e1 e2 => (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2)
    | NRAEnvEitherConcat e1 e2 => (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2)
    | NRAEnvApp e1 e2 => (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2)
    | NRAEnvEnv => False
    | NRAEnvAppEnv e1 e2 => (nraenv_ignores_env e2)
    | NRAEnvMapEnv e1 => False
    (* Those are additional operators *)
    | NRAEnvFlatMap e1 e2 => (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2)
    | NRAEnvJoin e1 e2 e3 =>  (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2) /\ (nraenv_ignores_env e3)
    | NRAEnvNaturalJoin e1 e2 =>  (nraenv_ignores_env e1) /\ (nraenv_ignores_env e2)
    | NRAEnvProject _ e1 => (nraenv_ignores_env e1)
    | NRAEnvGroupBy _ _ e1 => (nraenv_ignores_env e1)
    | NRAEnvUnnest _ _ e1 => (nraenv_ignores_env e1)
    end.

  (* Java equivalent: NraOptimizer.nraenv_ignores_env_fun *)
  Fixpoint nraenv_ignores_env_fun (e:nraenv) : bool :=
    match e with
    | NRAEnvGetConstant _ => true
    | NRAEnvID => true
    | NRAEnvConst rd => true
    | NRAEnvBinop bop e1 e2 => andb (nraenv_ignores_env_fun e1) (nraenv_ignores_env_fun e2)
    | NRAEnvUnop uop e1 => nraenv_ignores_env_fun e1
    | NRAEnvMap e1 e2 => andb (nraenv_ignores_env_fun e1) (nraenv_ignores_env_fun e2)
    | NRAEnvMapProduct e1 e2 => andb (nraenv_ignores_env_fun e1) (nraenv_ignores_env_fun e2)
    | NRAEnvProduct e1 e2 => andb (nraenv_ignores_env_fun e1) (nraenv_ignores_env_fun e2)
    | NRAEnvSelect e1 e2 => andb (nraenv_ignores_env_fun e1) (nraenv_ignores_env_fun e2)
    | NRAEnvDefault e1 e2 => andb (nraenv_ignores_env_fun e1) (nraenv_ignores_env_fun e2)
    | NRAEnvEither e1 e2 => andb (nraenv_ignores_env_fun e1) (nraenv_ignores_env_fun e2)
    | NRAEnvEitherConcat e1 e2 => andb (nraenv_ignores_env_fun e1) (nraenv_ignores_env_fun e2)
    | NRAEnvApp e1 e2 => andb (nraenv_ignores_env_fun e1) (nraenv_ignores_env_fun e2)
    | NRAEnvEnv => false
    | NRAEnvAppEnv e1 e2 => (nraenv_ignores_env_fun e2)
    | NRAEnvMapEnv e1 => false
    (* Those are additional operators *)
    | NRAEnvFlatMap e1 e2 => andb (nraenv_ignores_env_fun e1) (nraenv_ignores_env_fun e2)
    | NRAEnvJoin e1 e2 e3 =>  andb (nraenv_ignores_env_fun e1) (andb (nraenv_ignores_env_fun e2) (nraenv_ignores_env_fun e3))
    | NRAEnvNaturalJoin e1 e2 =>  andb (nraenv_ignores_env_fun e1) (nraenv_ignores_env_fun e2)
    | NRAEnvProject _ e1 => (nraenv_ignores_env_fun e1)
    | NRAEnvGroupBy _ _ e1 => (nraenv_ignores_env_fun e1)
    | NRAEnvUnnest _ _ e1 => (nraenv_ignores_env_fun e1)
    end.

  Lemma nraenv_ignores_env_eq (e:nraenv):
    nraenv_ignores_env e <-> (nraenv_ignores_env_fun e = true).
  Proof.
    induction e; split; simpl; intros; try auto; try congruence;
    try (rewrite IHe1 in H; rewrite IHe2 in H;
         elim H; clear H; intros;
         rewrite H; rewrite H0; reflexivity);
    try (rewrite andb_true_inversion in H;
         elim H; clear H; intros;
         rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
         split; assumption);
    try (rewrite IHe in H; assumption);
    try (rewrite <- IHe in H; assumption).
    - rewrite <- IHe2; assumption.
    - rewrite <- IHe2 in H; assumption.
    - rewrite IHe1 in H; rewrite IHe2 in H; rewrite IHe3 in H.
      elim H; clear H; intros.
      elim H0; clear H0; intros.
      rewrite H; rewrite H0; rewrite H1.
      auto.
    - rewrite andb_true_inversion in H.
      rewrite andb_true_inversion in H.
      elim H; clear H; intros.
      elim H0; clear H0; intros.
      rewrite <- IHe1 in H; rewrite <- IHe2 in H0; rewrite <- IHe3 in H1.
      auto.
  Qed.

  (* Fixed environment ! *)

  Fixpoint fixed_env (e:nraenv) : Prop :=
    match e with
      | NRAEnvID => True
      | NRAEnvConst rd => True
      | NRAEnvBinop bop e1 e2 => (fixed_env e1) /\ (fixed_env e2)
      | NRAEnvUnop uop e1 => fixed_env e1
      | NRAEnvMap e1 e2 => (fixed_env e1) /\ (fixed_env e2)
      | NRAEnvMapProduct e1 e2 => (fixed_env e1) /\ (fixed_env e2)
      | NRAEnvProduct e1 e2 => (fixed_env e1) /\ (fixed_env e2)
      | NRAEnvSelect e1 e2 => (fixed_env e1) /\ (fixed_env e2)
      | NRAEnvDefault e1 e2 => (fixed_env e1) /\ (fixed_env e2)
      | NRAEnvEither e1 e2 => (fixed_env e1) /\ (fixed_env e2)
      | NRAEnvEitherConcat e1 e2 => (fixed_env e1) /\ (fixed_env e2)
      | NRAEnvApp e1 e2 => (fixed_env e1) /\ (fixed_env e2)
      | NRAEnvGetConstant _ => True 
      | NRAEnvEnv => True (* That's the difference with ignore... *)
      | NRAEnvAppEnv e1 e2 => False (* Changes the environment *)
      | NRAEnvMapEnv e1 => False (* Changes the environment *)
      (* Those are additional operators *)
      | NRAEnvFlatMap e1 e2 => (fixed_env e1) /\ (fixed_env e2)
      | NRAEnvJoin e1 e2 e3 =>  (fixed_env e1) /\ (fixed_env e2) /\ (fixed_env e3)
      | NRAEnvNaturalJoin e1 e2 =>  (fixed_env e1) /\ (fixed_env e2)
      | NRAEnvProject _ e1 => (fixed_env e1)
      | NRAEnvGroupBy _ _ e1 => (fixed_env e1)
      | NRAEnvUnnest _ _ e1 => (fixed_env e1)
    end.

  Fixpoint fixed_env_fun (e:nraenv) : bool :=
    match e with
      | NRAEnvID => true
      | NRAEnvConst rd => true
      | NRAEnvBinop bop e1 e2 => andb (fixed_env_fun e1) (fixed_env_fun e2)
      | NRAEnvUnop uop e1 => fixed_env_fun e1
      | NRAEnvMap e1 e2 => andb (fixed_env_fun e1) (fixed_env_fun e2)
      | NRAEnvMapProduct e1 e2 => andb (fixed_env_fun e1) (fixed_env_fun e2)
      | NRAEnvProduct e1 e2 => andb (fixed_env_fun e1) (fixed_env_fun e2)
      | NRAEnvSelect e1 e2 => andb (fixed_env_fun e1) (fixed_env_fun e2)
      | NRAEnvDefault e1 e2 => andb (fixed_env_fun e1) (fixed_env_fun e2)
      | NRAEnvEither e1 e2 => andb (fixed_env_fun e1) (fixed_env_fun e2)
      | NRAEnvEitherConcat e1 e2 => andb (fixed_env_fun e1) (fixed_env_fun e2)
      | NRAEnvApp e1 e2 => andb (fixed_env_fun e1) (fixed_env_fun e2)
      | NRAEnvGetConstant _ => true
      | NRAEnvEnv => true
      | NRAEnvAppEnv e1 e2 => false
      | NRAEnvMapEnv e1 => false
      (* Those are additional operators *)
      | NRAEnvFlatMap e1 e2 => andb (fixed_env_fun e1) (fixed_env_fun e2)
      | NRAEnvJoin e1 e2 e3 =>  andb (fixed_env_fun e1) (andb (fixed_env_fun e2) (fixed_env_fun e3))
      | NRAEnvNaturalJoin e1 e2 =>  andb (fixed_env_fun e1) (fixed_env_fun e2)
      | NRAEnvProject _ e1 => (fixed_env_fun e1)
      | NRAEnvGroupBy _ _ e1 => (fixed_env_fun e1)
      | NRAEnvUnnest _ _ e1 => (fixed_env_fun e1)
    end.

  Lemma fixed_env_eq (e:nraenv):
    fixed_env e <-> (fixed_env_fun e = true).
  Proof.
    induction e; split; simpl; intros; try auto; try congruence;
    try (rewrite IHe1 in H; rewrite IHe2 in H;
         elim H; clear H; intros;
         rewrite H; rewrite H0; reflexivity);
    try (rewrite andb_true_inversion in H;
         elim H; clear H; intros;
         rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
         split; assumption);
    try (rewrite IHe in H; assumption);
    try (rewrite <- IHe in H; assumption).
    - rewrite IHe1 in H; rewrite IHe2 in H; rewrite IHe3 in H.
      elim H; clear H; intros.
      elim H0; clear H0; intros.
      rewrite H; rewrite H0; rewrite H1.
      auto.
    - rewrite andb_true_inversion in H.
      rewrite andb_true_inversion in H.
      elim H; clear H; intros.
      elim H0; clear H0; intros.
      rewrite <- IHe1 in H; rewrite <- IHe2 in H0; rewrite <- IHe3 in H1.
      auto.
  Qed.

  (* Nraenv_Ignores ID ... *)
  
  Fixpoint nraenv_ignores_id (e:nraenv) : Prop :=
    match e with
      | NRAEnvID => False
      | NRAEnvConst rd => True
      | NRAEnvBinop bop e1 e2 => (nraenv_ignores_id e1) /\ (nraenv_ignores_id e2)
      | NRAEnvUnop uop e1 => nraenv_ignores_id e1
      | NRAEnvMap e1 e2 => nraenv_ignores_id e2
      | NRAEnvMapProduct e1 e2 => nraenv_ignores_id e2
      | NRAEnvProduct e1 e2 => (nraenv_ignores_id e1) /\ (nraenv_ignores_id e2)
      | NRAEnvSelect e1 e2 => (nraenv_ignores_id e2)
      | NRAEnvDefault e1 e2 => (nraenv_ignores_id e1) /\ (nraenv_ignores_id e2)
      | NRAEnvEither e1 e2 => False
      | NRAEnvEitherConcat e1 e2 => (nraenv_ignores_id e1) /\ (nraenv_ignores_id e2)
      | NRAEnvApp e1 e2 => (nraenv_ignores_id e2)
      | NRAEnvGetConstant _ => True
      | NRAEnvEnv => True
      | NRAEnvAppEnv e1 e2 => (nraenv_ignores_id e1) /\ (nraenv_ignores_id e2)
      | NRAEnvMapEnv e1 => (nraenv_ignores_id e1)
      (* Those are additional operators *)
      | NRAEnvFlatMap e1 e2 => (nraenv_ignores_id e1) /\ (nraenv_ignores_id e2)
      | NRAEnvJoin e1 e2 e3 =>  (nraenv_ignores_id e1) /\ (nraenv_ignores_id e2) /\ (nraenv_ignores_id e3)
      | NRAEnvNaturalJoin e1 e2 =>  (nraenv_ignores_id e1) /\ (nraenv_ignores_id e2)
      | NRAEnvProject _ e1 => (nraenv_ignores_id e1)
      | NRAEnvGroupBy _ _ e1 => (nraenv_ignores_id e1)
      | NRAEnvUnnest _ _ e1 => (nraenv_ignores_id e1)
    end.

  (* Java equivalent: NraOptimizer.nraenv_ignores_id_fun *)
  Fixpoint nraenv_ignores_id_fun (e:nraenv) : bool :=
    match e with
      | NRAEnvID => false
      | NRAEnvConst rd => true
      | NRAEnvBinop bop e1 e2 => andb (nraenv_ignores_id_fun e1) (nraenv_ignores_id_fun e2)
      | NRAEnvUnop uop e1 => nraenv_ignores_id_fun e1
      | NRAEnvMap e1 e2 => nraenv_ignores_id_fun e2
      | NRAEnvMapProduct e1 e2 => nraenv_ignores_id_fun e2
      | NRAEnvProduct e1 e2 => andb (nraenv_ignores_id_fun e1) (nraenv_ignores_id_fun e2)
      | NRAEnvSelect e1 e2 => (nraenv_ignores_id_fun e2)
      | NRAEnvDefault e1 e2 => andb (nraenv_ignores_id_fun e1) (nraenv_ignores_id_fun e2)
      | NRAEnvEither e1 e2 => false
      | NRAEnvEitherConcat e1 e2 => andb (nraenv_ignores_id_fun e1) (nraenv_ignores_id_fun e2)
      | NRAEnvApp e1 e2 => (nraenv_ignores_id_fun e2)
      | NRAEnvGetConstant _ => true
      | NRAEnvEnv => true
      | NRAEnvAppEnv e1 e2 => andb (nraenv_ignores_id_fun e1) (nraenv_ignores_id_fun e2)
      | NRAEnvMapEnv e1 => (nraenv_ignores_id_fun e1)
      (* Those are additional operators *)
      | NRAEnvFlatMap e1 e2 => andb (nraenv_ignores_id_fun e1) (nraenv_ignores_id_fun e2)
      | NRAEnvJoin e1 e2 e3 =>  andb (nraenv_ignores_id_fun e1) (andb (nraenv_ignores_id_fun e2) (nraenv_ignores_id_fun e3))
      | NRAEnvNaturalJoin e1 e2 =>  andb (nraenv_ignores_id_fun e1) (nraenv_ignores_id_fun e2)
      | NRAEnvProject _ e1 => (nraenv_ignores_id_fun e1)
      | NRAEnvGroupBy _ _ e1 => (nraenv_ignores_id_fun e1)
      | NRAEnvUnnest _ _ e1 => (nraenv_ignores_id_fun e1)
    end.

  Lemma nraenv_ignores_id_eq (e:nraenv):
    nraenv_ignores_id e <-> (nraenv_ignores_id_fun e = true).
  Proof.
    induction e; split; simpl; intros; try auto; try congruence;
    try (rewrite IHe1 in H; rewrite IHe2 in H;
         elim H; clear H; intros;
         rewrite H; rewrite H0; reflexivity);
    try (rewrite andb_true_inversion in H;
         elim H; clear H; intros;
         rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
         split; assumption);
    try (rewrite IHe in H; assumption);
    try (rewrite <- IHe in H; assumption);
    try (rewrite IHe2 in H; assumption);
    try (rewrite <- IHe2 in H; assumption).
    - rewrite IHe1 in H; rewrite IHe2 in H; rewrite IHe3 in H.
      elim H; clear H; intros.
      elim H0; clear H0; intros.
      rewrite H; rewrite H0; rewrite H1.
      auto.
    - rewrite andb_true_inversion in H.
      rewrite andb_true_inversion in H.
      elim H; clear H; intros.
      elim H0; clear H0; intros.
      rewrite <- IHe1 in H; rewrite <- IHe2 in H0; rewrite <- IHe3 in H1.
      auto.
  Qed.

  Lemma nraenv_ignores_env_nraenv_core_eq (e:nraenv) :
    nraenv_ignores_env e ->
    nraenv_core_ignores_env (nraenv_to_nraenv_core e).
  Proof.
    intros.
    induction e; simpl in *; auto;
    try (elim H; clear H; intros; auto).
    - try (elim H0; clear H0; intros; auto).
  Qed.
  
  Lemma nraenv_ignores_env_swap (e:nraenv) :
    nraenv_ignores_env e -> forall (h:list (string*string)) c,
                               forall (env1 env2:data), forall x:data,
                       h ⊢ e @ₓ x ⊣ c;env1 = h ⊢ e @ₓ x ⊣ c;env2.
  Proof.
    intros.
    unfold nraenv_eval.
    apply nraenv_core_ignores_env_swap.
    apply nraenv_ignores_env_nraenv_core_eq.
    apply H.
  Qed.
  
  Lemma nraenv_ignores_id_nraenv_core_eq (e:nraenv) :
    nraenv_ignores_id e ->
    nraenv_core_ignores_id (nraenv_to_nraenv_core e).
  Proof.
    intros.
    induction e; simpl in *; auto;
    try (elim H; clear H; intros; auto).
    - try (elim H0; clear H0; intros; auto).
  Qed.
  
  Lemma nraenv_ignores_id_swap (e:nraenv) :
    nraenv_ignores_id e -> forall h:list (string*string), forall c,
      forall env:data, forall x1 x2:data,
          h ⊢ e @ₓ x1 ⊣ c;env = h ⊢ e @ₓ x2 ⊣ c;env.
  Proof.
    intros.
    unfold nraenv_eval.
    apply nraenv_core_ignores_id_swap.
    apply nraenv_ignores_id_nraenv_core_eq.
    apply H.
  Qed.

End NRAEnvIgnore.

