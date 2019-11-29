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
Require Import NRA.
Require Import NRASugar.
Require Import NRAEq.
Require Import cNRAEnv.

Section cNRAEnvIgnore.
  (* Some of algebraic equivalences for NRA with environment *)
  (* Those are valid without type *)

  Local Open Scope nra_scope.
  Local Open Scope nraenv_core_scope.
  
  (** Some infrastructure for rewrites *)

  Context {fruntime:foreign_runtime}.

  Fixpoint nraenv_core_is_nra (e:nraenv_core) : Prop :=
    match e with
    | cNRAEnvID => True
    | cNRAEnvConst rd => True
    | cNRAEnvBinop bop e1 e2 => (nraenv_core_is_nra e1) /\ (nraenv_core_is_nra e2)
    | cNRAEnvUnop uop e1 => nraenv_core_is_nra e1
    | cNRAEnvMap e1 e2 => (nraenv_core_is_nra e1) /\ (nraenv_core_is_nra e2)
    | cNRAEnvMapProduct e1 e2 => (nraenv_core_is_nra e1) /\ (nraenv_core_is_nra e2)
    | cNRAEnvProduct e1 e2 => (nraenv_core_is_nra e1) /\ (nraenv_core_is_nra e2)
    | cNRAEnvSelect e1 e2 => (nraenv_core_is_nra e1) /\ (nraenv_core_is_nra e2)
    | cNRAEnvDefault e1 e2 => (nraenv_core_is_nra e1) /\ (nraenv_core_is_nra e2)
    | cNRAEnvEither e1 e2 => (nraenv_core_is_nra e1) /\ (nraenv_core_is_nra e2)
    | cNRAEnvEitherConcat e1 e2 => (nraenv_core_is_nra e1) /\ (nraenv_core_is_nra e2)
    | cNRAEnvApp e1 e2 => (nraenv_core_is_nra e1) /\ (nraenv_core_is_nra e2)
    | cNRAEnvGetConstant _ => True
    | cNRAEnvEnv => False
    | cNRAEnvAppEnv e1 e2 => False
    | cNRAEnvMapEnv e1 => False
    end.

  Fixpoint nraenv_core_is_nra_fun (e:nraenv_core) : bool :=
    match e with
    | cNRAEnvID => true
    | cNRAEnvConst rd => true
    | cNRAEnvBinop bop e1 e2 => andb (nraenv_core_is_nra_fun e1) (nraenv_core_is_nra_fun e2)
    | cNRAEnvUnop uop e1 => nraenv_core_is_nra_fun e1
    | cNRAEnvMap e1 e2 => andb (nraenv_core_is_nra_fun e1) (nraenv_core_is_nra_fun e2)
    | cNRAEnvMapProduct e1 e2 => andb (nraenv_core_is_nra_fun e1) (nraenv_core_is_nra_fun e2)
    | cNRAEnvProduct e1 e2 => andb (nraenv_core_is_nra_fun e1) (nraenv_core_is_nra_fun e2)
    | cNRAEnvSelect e1 e2 => andb (nraenv_core_is_nra_fun e1) (nraenv_core_is_nra_fun e2)
    | cNRAEnvDefault e1 e2 => andb (nraenv_core_is_nra_fun e1) (nraenv_core_is_nra_fun e2)
    | cNRAEnvEither e1 e2 => andb (nraenv_core_is_nra_fun e1) (nraenv_core_is_nra_fun e2)
    | cNRAEnvEitherConcat e1 e2 => andb (nraenv_core_is_nra_fun e1) (nraenv_core_is_nra_fun e2)
    | cNRAEnvApp e1 e2 => andb (nraenv_core_is_nra_fun e1) (nraenv_core_is_nra_fun e2)
    | cNRAEnvGetConstant _ => true
    | cNRAEnvEnv => false
    | cNRAEnvAppEnv e1 e2 => false
    | cNRAEnvMapEnv e1 => false
    end.

  Lemma nraenv_core_is_nra_eq (e:nraenv_core):
    nraenv_core_is_nra e <-> (nraenv_core_is_nra_fun e = true).
  Proof.
    induction e; split; simpl; intros; try auto; try congruence;
      try (rewrite IHe1 in H; rewrite IHe2 in H;
           elim H; clear H; intros;
           rewrite H; rewrite H0; reflexivity);
      try (rewrite andb_true_inversion in H;
           elim H; clear H; intros;
           rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
           split; assumption).
    - rewrite IHe in H; assumption.
    - rewrite <- IHe in H; assumption.
  Qed.

  Fixpoint nraenv_core_ignores_env (e:nraenv_core) : Prop :=
    match e with
    | cNRAEnvID => True
    | cNRAEnvConst rd => True
    | cNRAEnvBinop bop e1 e2 => (nraenv_core_ignores_env e1) /\ (nraenv_core_ignores_env e2)
    | cNRAEnvUnop uop e1 => nraenv_core_ignores_env e1
    | cNRAEnvMap e1 e2 => (nraenv_core_ignores_env e1) /\ (nraenv_core_ignores_env e2)
    | cNRAEnvMapProduct e1 e2 => (nraenv_core_ignores_env e1) /\ (nraenv_core_ignores_env e2)
    | cNRAEnvProduct e1 e2 => (nraenv_core_ignores_env e1) /\ (nraenv_core_ignores_env e2)
    | cNRAEnvSelect e1 e2 => (nraenv_core_ignores_env e1) /\ (nraenv_core_ignores_env e2)
    | cNRAEnvDefault e1 e2 => (nraenv_core_ignores_env e1) /\ (nraenv_core_ignores_env e2)
    | cNRAEnvEither e1 e2 => (nraenv_core_ignores_env e1) /\ (nraenv_core_ignores_env e2)
    | cNRAEnvEitherConcat e1 e2 => (nraenv_core_ignores_env e1) /\ (nraenv_core_ignores_env e2)
    | cNRAEnvApp e1 e2 => (nraenv_core_ignores_env e1) /\ (nraenv_core_ignores_env e2)
    | cNRAEnvGetConstant _ => True
    | cNRAEnvEnv => False
    | cNRAEnvAppEnv e1 e2 => (nraenv_core_ignores_env e2)
    | cNRAEnvMapEnv e1 => False
    end.

  (* Java equivalent: NraOptimizer.nraenv_core_ignores_env_fun *)
  Fixpoint nraenv_core_ignores_env_fun (e:nraenv_core) : bool :=
    match e with
    | cNRAEnvID => true
    | cNRAEnvConst rd => true
    | cNRAEnvBinop bop e1 e2 => andb (nraenv_core_ignores_env_fun e1) (nraenv_core_ignores_env_fun e2)
    | cNRAEnvUnop uop e1 => nraenv_core_ignores_env_fun e1
    | cNRAEnvMap e1 e2 => andb (nraenv_core_ignores_env_fun e1) (nraenv_core_ignores_env_fun e2)
    | cNRAEnvMapProduct e1 e2 => andb (nraenv_core_ignores_env_fun e1) (nraenv_core_ignores_env_fun e2)
    | cNRAEnvProduct e1 e2 => andb (nraenv_core_ignores_env_fun e1) (nraenv_core_ignores_env_fun e2)
    | cNRAEnvSelect e1 e2 => andb (nraenv_core_ignores_env_fun e1) (nraenv_core_ignores_env_fun e2)
    | cNRAEnvDefault e1 e2 => andb (nraenv_core_ignores_env_fun e1) (nraenv_core_ignores_env_fun e2)
    | cNRAEnvEither e1 e2 => andb (nraenv_core_ignores_env_fun e1) (nraenv_core_ignores_env_fun e2)
    | cNRAEnvEitherConcat e1 e2 => andb (nraenv_core_ignores_env_fun e1) (nraenv_core_ignores_env_fun e2)
    | cNRAEnvApp e1 e2 => andb (nraenv_core_ignores_env_fun e1) (nraenv_core_ignores_env_fun e2)
    | cNRAEnvGetConstant _ => true
    | cNRAEnvEnv => false
    | cNRAEnvAppEnv e1 e2 => (nraenv_core_ignores_env_fun e2)
    | cNRAEnvMapEnv e1 => false
    end.

  Lemma nraenv_core_ignores_env_eq (e:nraenv_core):
    nraenv_core_ignores_env e <-> (nraenv_core_ignores_env_fun e = true).
  Proof.
    induction e; split; simpl; intros; try auto; try congruence;
      try (rewrite IHe1 in H; rewrite IHe2 in H;
           elim H; clear H; intros;
           rewrite H; rewrite H0; reflexivity);
      try (rewrite andb_true_inversion in H;
           elim H; clear H; intros;
           rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
           split; assumption).
    - rewrite IHe in H; assumption.
    - rewrite <- IHe in H; assumption.
    - rewrite <- IHe2; assumption.
    - rewrite <- IHe2 in H; assumption.
  Qed.

  (* Fixed environment ! *)

  Fixpoint nraenv_core_fixed_env (e:nraenv_core) : Prop :=
    match e with
    | cNRAEnvID => True
    | cNRAEnvConst rd => True
    | cNRAEnvBinop bop e1 e2 => (nraenv_core_fixed_env e1) /\ (nraenv_core_fixed_env e2)
    | cNRAEnvUnop uop e1 => nraenv_core_fixed_env e1
    | cNRAEnvMap e1 e2 => (nraenv_core_fixed_env e1) /\ (nraenv_core_fixed_env e2)
    | cNRAEnvMapProduct e1 e2 => (nraenv_core_fixed_env e1) /\ (nraenv_core_fixed_env e2)
    | cNRAEnvProduct e1 e2 => (nraenv_core_fixed_env e1) /\ (nraenv_core_fixed_env e2)
    | cNRAEnvSelect e1 e2 => (nraenv_core_fixed_env e1) /\ (nraenv_core_fixed_env e2)
    | cNRAEnvDefault e1 e2 => (nraenv_core_fixed_env e1) /\ (nraenv_core_fixed_env e2)
    | cNRAEnvEither e1 e2 => (nraenv_core_fixed_env e1) /\ (nraenv_core_fixed_env e2)
    | cNRAEnvEitherConcat e1 e2 => (nraenv_core_fixed_env e1) /\ (nraenv_core_fixed_env e2)
    | cNRAEnvApp e1 e2 => (nraenv_core_fixed_env e1) /\ (nraenv_core_fixed_env e2)
    | cNRAEnvGetConstant _ => True 
    | cNRAEnvEnv => True (* That's the difference with ignore... *)
    | cNRAEnvAppEnv e1 e2 => False (* Changes the environment *)
    | cNRAEnvMapEnv e1 => False (* Changes the environment *)
    end.

  Fixpoint nraenv_core_fixed_env_fun (e:nraenv_core) : bool :=
    match e with
    | cNRAEnvID => true
    | cNRAEnvConst rd => true
    | cNRAEnvBinop bop e1 e2 => andb (nraenv_core_fixed_env_fun e1) (nraenv_core_fixed_env_fun e2)
    | cNRAEnvUnop uop e1 => nraenv_core_fixed_env_fun e1
    | cNRAEnvMap e1 e2 => andb (nraenv_core_fixed_env_fun e1) (nraenv_core_fixed_env_fun e2)
    | cNRAEnvMapProduct e1 e2 => andb (nraenv_core_fixed_env_fun e1) (nraenv_core_fixed_env_fun e2)
    | cNRAEnvProduct e1 e2 => andb (nraenv_core_fixed_env_fun e1) (nraenv_core_fixed_env_fun e2)
    | cNRAEnvSelect e1 e2 => andb (nraenv_core_fixed_env_fun e1) (nraenv_core_fixed_env_fun e2)
    | cNRAEnvDefault e1 e2 => andb (nraenv_core_fixed_env_fun e1) (nraenv_core_fixed_env_fun e2)
    | cNRAEnvEither e1 e2 => andb (nraenv_core_fixed_env_fun e1) (nraenv_core_fixed_env_fun e2)
    | cNRAEnvEitherConcat e1 e2 => andb (nraenv_core_fixed_env_fun e1) (nraenv_core_fixed_env_fun e2)
    | cNRAEnvApp e1 e2 => andb (nraenv_core_fixed_env_fun e1) (nraenv_core_fixed_env_fun e2)
    | cNRAEnvGetConstant _ => true
    | cNRAEnvEnv => true
    | cNRAEnvAppEnv e1 e2 => false
    | cNRAEnvMapEnv e1 => false
    end.

  Lemma nraenv_core_fixed_env_eq (e:nraenv_core):
    nraenv_core_fixed_env e <-> (nraenv_core_fixed_env_fun e = true).
  Proof.
    induction e; split; simpl; intros; try auto; try congruence;
      try (rewrite IHe1 in H; rewrite IHe2 in H;
           elim H; clear H; intros;
           rewrite H; rewrite H0; reflexivity);
      try (rewrite andb_true_inversion in H;
           elim H; clear H; intros;
           rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
           split; assumption).
    - rewrite IHe in H; assumption.
    - rewrite <- IHe in H; assumption.
  Qed.

  (* Ignores ID ... *)
  
  Fixpoint nraenv_core_ignores_id (e:nraenv_core) : Prop :=
    match e with
    | cNRAEnvID => False
    | cNRAEnvConst rd => True
    | cNRAEnvBinop bop e1 e2 => (nraenv_core_ignores_id e1) /\ (nraenv_core_ignores_id e2)
    | cNRAEnvUnop uop e1 => nraenv_core_ignores_id e1
    | cNRAEnvMap e1 e2 => nraenv_core_ignores_id e2
    | cNRAEnvMapProduct e1 e2 => nraenv_core_ignores_id e2
    | cNRAEnvProduct e1 e2 => (nraenv_core_ignores_id e1) /\ (nraenv_core_ignores_id e2)
    | cNRAEnvSelect e1 e2 => (nraenv_core_ignores_id e2)
    | cNRAEnvDefault e1 e2 => (nraenv_core_ignores_id e1) /\ (nraenv_core_ignores_id e2)
    | cNRAEnvEither e1 e2 => False
    | cNRAEnvEitherConcat e1 e2 => (nraenv_core_ignores_id e1) /\ (nraenv_core_ignores_id e2)
    | cNRAEnvApp e1 e2 => (nraenv_core_ignores_id e2)
    | cNRAEnvGetConstant _ => True
    | cNRAEnvEnv => True
    | cNRAEnvAppEnv e1 e2 => (nraenv_core_ignores_id e1) /\ (nraenv_core_ignores_id e2)
    | cNRAEnvMapEnv e1 => (nraenv_core_ignores_id e1)
    end.

  (* Java equivalent: NraOptimizer.nraenv_core_ignores_id_fun *)
  Fixpoint nraenv_core_ignores_id_fun (e:nraenv_core) : bool :=
    match e with
    | cNRAEnvID => false
    | cNRAEnvConst rd => true
    | cNRAEnvBinop bop e1 e2 => andb (nraenv_core_ignores_id_fun e1) (nraenv_core_ignores_id_fun e2)
    | cNRAEnvUnop uop e1 => nraenv_core_ignores_id_fun e1
    | cNRAEnvMap e1 e2 => nraenv_core_ignores_id_fun e2
    | cNRAEnvMapProduct e1 e2 => nraenv_core_ignores_id_fun e2
    | cNRAEnvProduct e1 e2 => andb (nraenv_core_ignores_id_fun e1) (nraenv_core_ignores_id_fun e2)
    | cNRAEnvSelect e1 e2 => (nraenv_core_ignores_id_fun e2)
    | cNRAEnvDefault e1 e2 => andb (nraenv_core_ignores_id_fun e1) (nraenv_core_ignores_id_fun e2)
    | cNRAEnvEither e1 e2 => false
    | cNRAEnvEitherConcat e1 e2 => andb (nraenv_core_ignores_id_fun e1) (nraenv_core_ignores_id_fun e2)
    | cNRAEnvApp e1 e2 => (nraenv_core_ignores_id_fun e2)
    | cNRAEnvGetConstant _ => true
    | cNRAEnvEnv => true
    | cNRAEnvAppEnv e1 e2 => andb (nraenv_core_ignores_id_fun e1) (nraenv_core_ignores_id_fun e2)
    | cNRAEnvMapEnv e1 => (nraenv_core_ignores_id_fun e1)
    end.
  
  Lemma nraenv_core_ignores_id_eq (e:nraenv_core):
    nraenv_core_ignores_id e <-> (nraenv_core_ignores_id_fun e = true).
  Proof.
    induction e; split; simpl; intros; try auto; try congruence.
    - rewrite IHe1 in H; rewrite IHe2 in H;
        elim H; clear H; intros;
          rewrite H; rewrite H0; reflexivity.
    - rewrite andb_true_inversion in H;
        elim H; clear H; intros;
          rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
            split; assumption.
    - rewrite IHe in H; assumption.
    - rewrite <- IHe in H; assumption.
    - rewrite IHe2 in H; assumption.
    - rewrite <- IHe2 in H; assumption.
    - rewrite IHe2 in H; assumption.
    - rewrite <- IHe2 in H; assumption.
    - rewrite IHe1 in H; rewrite IHe2 in H;
        elim H; clear H; intros;
          rewrite H; rewrite H0; reflexivity.
    - rewrite andb_true_inversion in H;
        elim H; clear H; intros;
          rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
            split; assumption.
    - rewrite IHe2 in H; assumption.
    - rewrite <- IHe2 in H; assumption.
    - rewrite IHe1 in H; rewrite IHe2 in H;
        elim H; clear H; intros;
          rewrite H; rewrite H0; reflexivity.
    - rewrite andb_true_inversion in H;
        elim H; clear H; intros;
          rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
            split; assumption.
    - rewrite IHe1 in H; rewrite IHe2 in H;
        elim H; clear H; intros;
          rewrite H; rewrite H0; reflexivity.
    - rewrite andb_true_inversion in H;
        elim H; clear H; intros;
          rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
            split; assumption.
    - intuition.
    - intuition.
    - intuition.
    - rewrite andb_true_inversion in H;
        elim H; clear H; intros;
          rewrite <- IHe1 in H; rewrite <- IHe2 in H0;
            split; assumption.
    - rewrite <- IHe; assumption.
    - rewrite IHe; assumption.
  Qed.
  
  Fixpoint nraenv_core_deenv_nra (ae:nraenv_core) : nra :=
    match ae with
    | cNRAEnvID => NRAID
    | cNRAEnvConst d => NRAConst d
    | cNRAEnvBinop b ae1 ae2 => NRABinop b (nraenv_core_deenv_nra ae1) (nraenv_core_deenv_nra ae2)
    | cNRAEnvUnop u ae1 => NRAUnop u (nraenv_core_deenv_nra ae1)
    | cNRAEnvMap ea1 ea2 => NRAMap (nraenv_core_deenv_nra ea1) (nraenv_core_deenv_nra ea2)
    | cNRAEnvMapProduct ea1 ea2 => NRAMapProduct (nraenv_core_deenv_nra ea1) (nraenv_core_deenv_nra ea2)
    | cNRAEnvProduct ea1 ea2 => NRAProduct (nraenv_core_deenv_nra ea1) (nraenv_core_deenv_nra ea2)
    | cNRAEnvSelect ea1 ea2 => NRASelect (nraenv_core_deenv_nra ea1) (nraenv_core_deenv_nra ea2)
    | cNRAEnvDefault ea1 ea2 => NRADefault (nraenv_core_deenv_nra ea1) (nraenv_core_deenv_nra ea2)
    | cNRAEnvEither ea1 ea2 => NRAEither (nraenv_core_deenv_nra ea1) (nraenv_core_deenv_nra ea2)
    | cNRAEnvEitherConcat ea1 ea2 => NRAEitherConcat (nraenv_core_deenv_nra ea1) (nraenv_core_deenv_nra ea2)
    | cNRAEnvApp ea1 ea2 => NRAApp (nraenv_core_deenv_nra ea1) (nraenv_core_deenv_nra ea2)
    | cNRAEnvGetConstant s => NRAGetConstant s
    | cNRAEnvEnv => NRAID
    | cNRAEnvAppEnv ea1 ea2 => NRAID
    | cNRAEnvMapEnv ea1 => NRAID
    end.

  Lemma nraenv_core_ignores_env_swap (e:nraenv_core) :
    nraenv_core_ignores_env e -> forall (h:list (string*string)) c,
                               forall (env1 env2:data), forall x:data,
                       h ⊢ₑ e @ₑ x ⊣ c;env1 = h ⊢ₑ e @ₑ x ⊣ c;env2.
  Proof.
    intros H h c.
    simpl.
    revert H h.
    induction e; try reflexivity; simpl in *; try congruence; intros.
    - inversion H; clear H.
      rewrite (IHe1 H0 h env1 env2); rewrite (IHe2 H1 h env1 env2); reflexivity.
    - rewrite (IHe H h env1 env2); reflexivity.
    - inversion H; clear H.
      rewrite (IHe2 H1 h env1 env2); clear IHe2 H1.
      generalize ((nraenv_core_eval h c e2 env2)); intros.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      induction l; try reflexivity; simpl.
      rewrite (IHe1 H0 h env1 env2); clear IHe1 H0.
      destruct (nraenv_core_eval h c e1 env2 a); intros; trivial.
      unfold lift in *; simpl in *.
      revert IHl.
      generalize (lift_map (nraenv_core_eval h c e1 env1) l); 
        generalize (lift_map (nraenv_core_eval h c e1 env2) l); intros.
      destruct o1; destruct o0; simpl; congruence.
    - inversion H; clear H.
      rewrite (IHe2 H1 h env1 env2); clear IHe2 H1.
      generalize (h ⊢ₑ e2 @ₑ x ⊣ c;env2); intros.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      induction l; try reflexivity; simpl.
      unfold lift in *; simpl.
      unfold omap_product in *; simpl.
      unfold oncoll_map_concat in *; simpl.
      rewrite (IHe1 H0 h env1 env2); clear IHe1 H0.
      generalize (h ⊢ₑ e1 @ₑ a ⊣ c;env2); intros.
      destruct o; try reflexivity; simpl.
      revert IHl.
      generalize (lift_flat_map
                    (fun a0 : data =>
                       match h ⊢ₑ e1 @ₑ a0 ⊣ c;env1 with
                       | Some (dcoll y) => omap_concat a0 y
                       | _ => None
                       end) l
                 ); generalize (lift_flat_map
                                  (fun a0 : data =>
                                     match h ⊢ₑ e1 @ₑ a0 ⊣ c;env2 with
                                     | Some (dcoll y) => omap_concat a0 y
                                     | _ => None
                                     end) l
                               ); intros.
      destruct o; destruct o0; try congruence.
      inversion IHl; reflexivity.
    - inversion H; clear H.
      rewrite (IHe1 H0 h env1 env2); rewrite (IHe2 H1 h env1 env2); reflexivity.
    - inversion H; clear H.
      rewrite (IHe2 H1 h env1 env2); clear IHe2 H1.
      generalize (h ⊢ₑ e2 @ₑ x ⊣ c;env2); intros.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      induction l; try reflexivity; simpl.
      rewrite (IHe1 H0 h env1 env2); clear IHe1 H0.
      generalize (h ⊢ₑ e1 @ₑ a ⊣ c;env2); intros.
      destruct o; try reflexivity; simpl.
      unfold lift in *; simpl in *.
      revert IHl.
      generalize (lift_filter
                    (fun x' : data =>
                       match h ⊢ₑ e1 @ₑx' ⊣ c;env1 with
                       | Some (dbool b) => Some b
                       | _ => None
                       end) l
                 ); generalize (lift_filter
                                  (fun x' : data =>
                                     match h ⊢ₑ e1 @ₑ x' ⊣ c;env2 with
                                     | Some (dbool b) => Some b
                                     | _ => None
                                     end) l
                               ); intros.
      destruct o; destruct o0; try congruence.
      inversion IHl; reflexivity.
    - inversion H; clear H.
      rewrite (IHe1 H0 h env1 env2); rewrite (IHe2 H1 h env1 env2); reflexivity.
    - destruct x; simpl; intuition.
    - inversion H; clear H.
      unfold olift; simpl.
      rewrite (IHe2 H1 h env1 env2).
      destruct (h ⊢ₑ e2 @ₑ x ⊣ c;env2);
        rewrite (IHe1 H0 h env1 env2); reflexivity.
    - inversion H; clear H.
      unfold olift; simpl.
      rewrite (IHe2 H1 h env1 env2).
      destruct (h ⊢ₑ e2 @ₑ x ⊣ c;env2).
      rewrite (IHe1 H0 h env1 env2); reflexivity. reflexivity.
    - contradiction.
    - rewrite (IHe2 H h env1 env2 x).
      reflexivity.
    - contradiction.
  Qed.
  
  Lemma nraenv_core_ignores_id_swap (e:nraenv_core) :
    nraenv_core_ignores_id e -> forall h:list (string*string), forall c,
        forall env:data, forall x1 x2:data,
            h ⊢ₑ e @ₑ x1 ⊣ c;env = h ⊢ₑ e @ₑ x2 ⊣ c;env.
  Proof.
    intros H h c.
    revert H h.
    induction e; try reflexivity; simpl in *; try congruence; intros.
    - contradiction.
    - inversion H; clear H.
      rewrite (IHe1 H0 h env x1 x2); rewrite (IHe2 H1 h env x1 x2); reflexivity.
    - rewrite (IHe H h env x1 x2); reflexivity.
    - rewrite (IHe2 H h env x1 x2); clear IHe2 H; reflexivity.
    - rewrite (IHe2 H h env x1 x2); clear IHe2 H; reflexivity.
    - inversion H; clear H.
      rewrite (IHe1 H0 h env x1 x2); rewrite (IHe2 H1 h env x1 x2); reflexivity.
    - rewrite (IHe2 H h env x1 x2); clear IHe2 H; reflexivity.
    - inversion H; clear H.
      rewrite (IHe1 H0 h env x1 x2); rewrite (IHe2 H1 h env x1 x2); reflexivity.
    - intuition.
    - inversion H; clear H.
      rewrite (IHe1 H0 h env x1 x2); rewrite (IHe2 H1 h env x1 x2); reflexivity.
    - rewrite (IHe2 H h env x1 x2); reflexivity.
    - inversion H; clear H.
      rewrite (IHe2 H1 h env x1 x2).
      destruct (h ⊢ₑ e2 @ₑ x2 ⊣ c;env); try reflexivity; simpl.
      erewrite IHe1 by trivial; reflexivity.
    - destruct env; try reflexivity; simpl.
      f_equal.
      apply lift_map_ext; intros.
      rewrite (IHe H h x x1 x2); reflexivity.
  Qed.

  Lemma nraenv_core_is_nra_deenv (h:list (string*string)) c (e:nraenv_core) (d1 d2:data) :
    nraenv_core_is_nra e ->
        h ⊢ (nra_of_nraenv_core e) @ₐ (nra_context_data d1 d2) ⊣ c =
        h ⊢ (nraenv_core_deenv_nra e) @ₐ d2 ⊣ c.
  Proof.
    intros.
    revert d1 d2; induction e; try reflexivity; simpl in *; try (inversion H; congruence); simpl; intros.
    - inversion H; clear H.
      specialize (IHe1 H0); clear H0.
      specialize (IHe2 H1); clear H1.
      rewrite IHe1; rewrite IHe2; reflexivity.
    - specialize (IHe H); clear H.
      rewrite IHe; reflexivity.
    - inversion H; clear H.
      specialize (IHe1 H0); clear H0.
      specialize (IHe2 H1); clear H1.
      rewrite IHe2; clear IHe2.
      unfold olift, olift2; simpl.
      generalize (nra_eval h c (nraenv_core_deenv_nra e2) d2); intros; simpl; clear e2.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      unfold lift, omap_product, oncoll_map_concat; simpl.
      rewrite lift_map_map_rec1 in *; simpl.
      rewrite omap_concat_map_rec in *; simpl.
      rewrite app_nil_r.
      rewrite lift_map_remove1; simpl.
      unfold nra_context_data in *.
      induction l; try reflexivity; simpl.
      rewrite IHe1; simpl.
      destruct (nra_eval h c (nraenv_core_deenv_nra e1) a); try reflexivity.
      unfold lift; simpl.
      revert IHl.
      generalize (lift_map (nra_eval h c (nra_of_nraenv_core e1))
                       (map (fun x : data => drec (("PBIND"%string, d1) :: ("PDATA"%string, x) :: nil)) l));
        generalize (lift_map (nra_eval h c (nraenv_core_deenv_nra e1)) l); intros.
      destruct o; destruct o0; try congruence.
    - inversion H; clear H.
      specialize (IHe1 H0); clear H0.
      specialize (IHe2 H1); clear H1.
      rewrite IHe2; clear IHe2.
      unfold olift, olift2; simpl.
      generalize (nra_eval h c (nraenv_core_deenv_nra e2) d2); intros; simpl; clear e2.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      unfold lift, omap_product, oncoll_map_concat; simpl.
      rewrite lift_map_map_rec1 in *; simpl.
      rewrite omap_concat_map_rec in *; simpl.
      rewrite app_nil_r in *.
      rewrite lift_map_remove1 in *; simpl.
      unfold nra_context_data in *.
      induction l; try reflexivity; simpl.
      rewrite IHe1; simpl; clear IHe1.
      generalize (nra_eval h c (nraenv_core_deenv_nra e1) a); intros.
      destruct o; try reflexivity.
      destruct d; try reflexivity.
      unfold lift_oncoll in *; simpl in *.
      rewrite lift_map_map_rec1 in *; simpl in *.
      rewrite omap_concat_map_rec2 in *; simpl in *.
      unfold lift in *; simpl in *.
      revert IHl.
      generalize (
                 lift_flat_map
         (fun a0 : data =>
          match
            match nra_eval h c (nra_of_nraenv_core e1) a0 with
            | Some (dcoll l1) =>
                match
                  lift_map (fun x : data => Some (drec (("PDATA2"%string, x) :: nil))) l1
                with
                | Some a' => Some (dcoll a')
                | None => None
                end
            | _ => None
            end
          with
          | Some (dcoll y) => omap_concat a0 y
          | _ => None
          end) (map (fun x : data => drec (("PBIND"%string, d1) :: ("PDATA"%string, x) :: nil)) l)

        ); generalize (
     lift_flat_map
       (fun a0 : data =>
        match nra_eval h c (nraenv_core_deenv_nra e1) a0 with
        | Some (dcoll y) => omap_concat a0 y
        | _ => None
        end) l
             ); intros.
      destruct o; destruct o0; try reflexivity; try congruence; simpl; try rewrite lift_map_map_unnest2; simpl in *.
      * generalize lift_map_map_unnest2; intros HH.
        unfold olift2 in HH.
        rewrite HH; clear HH.
        revert IHl.
        unfold olift2 in *; simpl in *.
        generalize (     lift_map
       (fun x : data =>
        match
          match x with
          | drec r => edot r "PDATA"
          | _ => None
          end
        with
        | Some d3 =>
            match
              match x with
              | drec r => edot r "PDATA2"
              | _ => None
              end
            with
            | Some d4 =>
                match d3 with
                | drec r1 =>
                    match d4 with
                    | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                    | _ => None
                    end
                | _ => None
                end
            | None => None
            end
        | None => None
        end) l2); intros.
        destruct o; try reflexivity; try congruence; simpl.
        inversion IHl.
        subst.
        reflexivity.
      * generalize lift_map_map_unnest2; intros HH.
        unfold olift2 in HH.
        rewrite HH; clear HH.
        revert IHl.
        unfold olift2 in *; simpl in *.
        generalize (     lift_map
       (fun x : data =>
        match
          match x with
          | drec r => edot r "PDATA"
          | _ => None
          end
        with
        | Some d3 =>
            match
              match x with
              | drec r => edot r "PDATA2"
              | _ => None
              end
            with
            | Some d4 =>
                match d3 with
                | drec r1 =>
                    match d4 with
                    | drec r2 => Some (drec (rec_sort (r1 ++ r2)))
                    | _ => None
                    end
                | _ => None
                end
            | None => None
            end
        | None => None
        end) l1); intros.
        destruct o; try reflexivity; congruence.
      * destruct (omap_concat a l0); congruence.
    - inversion H; clear H.
      specialize (IHe1 H0); clear H0.
      specialize (IHe2 H1); clear H1.
      rewrite IHe1; rewrite IHe2; reflexivity.
    - inversion H; clear H.
      specialize (IHe1 H0); clear H0.
      specialize (IHe2 H1); clear H1.
      rewrite IHe2; clear IHe2.
      unfold olift, olift2; simpl.
      generalize (nra_eval h c (nraenv_core_deenv_nra e2) d2); intros; simpl; clear e2.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      unfold lift, omap_product, oncoll_map_concat; simpl.
      rewrite lift_map_map_rec1 in *; simpl.
      rewrite omap_concat_map_rec in *; simpl.
      rewrite app_nil_r in *.
      rewrite lift_map_remove1 in *; simpl.
      unfold nra_context_data in *.
      induction l; try reflexivity; simpl.
      rewrite IHe1; simpl; clear IHe1.
      generalize (nra_eval h c (nraenv_core_deenv_nra e1) a); intros.
      destruct o; try reflexivity.
      destruct d; try reflexivity.
      unfold lift_oncoll in *; simpl in *.
      revert IHl.
      generalize (lift_filter
         (fun x' : data =>
          match nra_eval h c (nra_of_nraenv_core e1) x' with
          | Some (dbool b0) => Some b0
          | _ => None
          end) (map (fun x : data => drec (("PBIND"%string, d1) :: ("PDATA"%string, x) :: nil)) l)
                 ); intros.
      destruct o; try reflexivity; try congruence; simpl.
      * destruct b; try reflexivity.
        rewrite lift_map_one1.
        revert IHl.
        generalize (lift_map
         (fun x : data =>
          match x with
          | drec r => edot r "PDATA"
          | _ => None
          end) l0);
        generalize (lift_filter
       (fun x' : data =>
        match nra_eval h c (nraenv_core_deenv_nra e1) x' with
        | Some (dbool b) => Some b
        | _ => None
        end) l
                                 ); intros.
        destruct o; destruct o0; try reflexivity; try congruence; simpl.
        revert IHl.
        generalize (lift_map
         (fun x : data =>
          match x with
          | drec r => edot r "PDATA"
          | _ => None
          end) l0);
        generalize (lift_filter
       (fun x' : data =>
        match nra_eval h c (nraenv_core_deenv_nra e1) x' with
        | Some (dbool b) => Some b
        | _ => None
        end) l
                                 ); intros.
        destruct o; destruct o0; try reflexivity; congruence.
      * revert IHl.
        generalize (lift_filter
       (fun x' : data =>
        match nra_eval h c (nraenv_core_deenv_nra e1) x' with
        | Some (dbool b0) => Some b0
        | _ => None
        end) l); intros.
        destruct o; congruence.
    - inversion H; clear H.
      specialize (IHe1 H0); clear H0.
      specialize (IHe2 H1); clear H1.
      rewrite IHe1; rewrite IHe2; reflexivity.
    - destruct H as [i1 i2].
      destruct d2; trivial; simpl.
      + apply IHe1; trivial.
      + apply IHe2; trivial.
    - inversion H; clear H.
      specialize (IHe1 H0); clear H0.
      specialize (IHe2 H1); clear H1.
      rewrite IHe2; simpl; clear IHe2.
      generalize (nra_eval h c (nraenv_core_deenv_nra e2) d2); intros; simpl.
      destruct o; try reflexivity; simpl;
      unfold nra_context_data in *;
      rewrite IHe1; reflexivity.
    - inversion H; clear H.
      specialize (IHe1 H0); clear H0.
      specialize (IHe2 H1); clear H1.
      rewrite IHe2; simpl; clear IHe2.
      generalize (nra_eval h c (nraenv_core_deenv_nra e2) d2); intros; simpl.
      destruct o; try reflexivity; simpl.
      unfold nra_context_data in *;
        rewrite IHe1; reflexivity.
  Qed.

  (* TODO: try to define cNRAEnvEitherConcat. *)
  (* TODO: this (and the Proper) should move *)
  Fixpoint nraenv_core_of_nra (a:nra) : nraenv_core :=
    match a with
      | NRAGetConstant s => cNRAEnvGetConstant s
      | NRAID => cNRAEnvID
      | NRAConst d => cNRAEnvConst d
      | NRABinop b e1 e2 => cNRAEnvBinop b (nraenv_core_of_nra e1) (nraenv_core_of_nra e2)
      | NRAUnop u e1 => cNRAEnvUnop u (nraenv_core_of_nra e1)
      | NRAMap e1 e2 => cNRAEnvMap (nraenv_core_of_nra e1) (nraenv_core_of_nra e2)
      | NRAMapProduct e1 e2 => cNRAEnvMapProduct (nraenv_core_of_nra e1) (nraenv_core_of_nra e2)
      | NRAProduct e1 e2 => cNRAEnvProduct (nraenv_core_of_nra e1) (nraenv_core_of_nra e2)
      | NRASelect e1 e2 => cNRAEnvSelect (nraenv_core_of_nra e1) (nraenv_core_of_nra e2)
      | NRADefault e1 e2 => cNRAEnvDefault (nraenv_core_of_nra e1) (nraenv_core_of_nra e2)
      | NRAEither opl opr => cNRAEnvEither (nraenv_core_of_nra opl) (nraenv_core_of_nra opr)
      | NRAEitherConcat op1 op2 => cNRAEnvEitherConcat (nraenv_core_of_nra op1) (nraenv_core_of_nra op2)
      | NRAApp e1 e2 => cNRAEnvApp (nraenv_core_of_nra e1) (nraenv_core_of_nra e2)
    end.

  Lemma nraenv_core_eval_of_nra h c e d env :
    nra_eval h c e d = nraenv_core_eval h c (nraenv_core_of_nra e) env d.
  Proof.
    revert d env.
    induction e; simpl; trivial; intros;
    try rewrite <- IHe;
    try rewrite <- IHe1; try rewrite <- IHe2; trivial;
    repeat (first [
                apply olift_ext
              | apply lift_oncoll_ext
              | apply lift_dcoll_inversion
              | apply lift_map_ext
              | apply omap_product_ext
              | apply lift_filter_ext]; intros); trivial.
    - rewrite <- IHe1; trivial.
    - match_destr.
  Qed.
  
  Lemma nraenv_core_of_nra_is_nra x : nraenv_core_is_nra (nraenv_core_of_nra x).
  Proof.
    induction x; simpl; auto.
  Qed.

  Lemma nraenv_core_deenv_nra_of_nra x : nraenv_core_deenv_nra (nraenv_core_of_nra x) = x.
  Proof.
    induction x; simpl; try congruence.
  Qed.
    
End cNRAEnvIgnore.

