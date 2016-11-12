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

Section RAlgEnvIgnore.

  Require Import Bool List String.
  Require Import Utils BasicRuntime.
  Require Import RAlg RAlgEq RAlgEnv.

  (* Some of algebraic equivalences for NRA with environment *)
  (* Those are valid without type *)

  Local Open Scope alg_scope.
  Local Open Scope algenv_scope.
  
  (** Some infrastructure for rewrites *)

  Context {fruntime:foreign_runtime}.

  Fixpoint algenv_is_nra (e:algenv) : Prop :=
    match e with
      | ANID => True
      | ANConst rd => True
      | ANBinop bop e1 e2 => (algenv_is_nra e1) /\ (algenv_is_nra e2)
      | ANUnop uop e1 => algenv_is_nra e1
      | ANMap e1 e2 => (algenv_is_nra e1) /\ (algenv_is_nra e2)
      | ANMapConcat e1 e2 => (algenv_is_nra e1) /\ (algenv_is_nra e2)
      | ANProduct e1 e2 => (algenv_is_nra e1) /\ (algenv_is_nra e2)
      | ANSelect e1 e2 => (algenv_is_nra e1) /\ (algenv_is_nra e2)
      | ANDefault e1 e2 => (algenv_is_nra e1) /\ (algenv_is_nra e2)
      | ANEither e1 e2 => (algenv_is_nra e1) /\ (algenv_is_nra e2)
      | ANEitherConcat e1 e2 => (algenv_is_nra e1) /\ (algenv_is_nra e2)
      | ANApp e1 e2 => (algenv_is_nra e1) /\ (algenv_is_nra e2)
      | ANGetConstant _ => False
      | ANEnv => False
      | ANAppEnv e1 e2 => False
      | ANMapEnv e1 => False
    end.

  Fixpoint algenv_is_nra_fun (e:algenv) : bool :=
    match e with
      | ANID => true
      | ANConst rd => true
      | ANBinop bop e1 e2 => andb (algenv_is_nra_fun e1) (algenv_is_nra_fun e2)
      | ANUnop uop e1 => algenv_is_nra_fun e1
      | ANMap e1 e2 => andb (algenv_is_nra_fun e1) (algenv_is_nra_fun e2)
      | ANMapConcat e1 e2 => andb (algenv_is_nra_fun e1) (algenv_is_nra_fun e2)
      | ANProduct e1 e2 => andb (algenv_is_nra_fun e1) (algenv_is_nra_fun e2)
      | ANSelect e1 e2 => andb (algenv_is_nra_fun e1) (algenv_is_nra_fun e2)
      | ANDefault e1 e2 => andb (algenv_is_nra_fun e1) (algenv_is_nra_fun e2)
      | ANEither e1 e2 => andb (algenv_is_nra_fun e1) (algenv_is_nra_fun e2)
      | ANEitherConcat e1 e2 => andb (algenv_is_nra_fun e1) (algenv_is_nra_fun e2)
      | ANApp e1 e2 => andb (algenv_is_nra_fun e1) (algenv_is_nra_fun e2)
      | ANGetConstant _ => false
      | ANEnv => false
      | ANAppEnv e1 e2 => false
      | ANMapEnv e1 => false
    end.

  Lemma algenv_is_nra_eq (e:algenv):
    algenv_is_nra e <-> (algenv_is_nra_fun e = true).
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

  Fixpoint algenv_ignores_env (e:algenv) : Prop :=
    match e with
      | ANID => True
      | ANConst rd => True
      | ANBinop bop e1 e2 => (algenv_ignores_env e1) /\ (algenv_ignores_env e2)
      | ANUnop uop e1 => algenv_ignores_env e1
      | ANMap e1 e2 => (algenv_ignores_env e1) /\ (algenv_ignores_env e2)
      | ANMapConcat e1 e2 => (algenv_ignores_env e1) /\ (algenv_ignores_env e2)
      | ANProduct e1 e2 => (algenv_ignores_env e1) /\ (algenv_ignores_env e2)
      | ANSelect e1 e2 => (algenv_ignores_env e1) /\ (algenv_ignores_env e2)
      | ANDefault e1 e2 => (algenv_ignores_env e1) /\ (algenv_ignores_env e2)
      | ANEither e1 e2 => (algenv_ignores_env e1) /\ (algenv_ignores_env e2)
      | ANEitherConcat e1 e2 => (algenv_ignores_env e1) /\ (algenv_ignores_env e2)
      | ANApp e1 e2 => (algenv_ignores_env e1) /\ (algenv_ignores_env e2)
      | ANGetConstant _ => True
      | ANEnv => False
      | ANAppEnv e1 e2 => (algenv_ignores_env e2)
      | ANMapEnv e1 => False
    end.

  (* Java equivalent: NraOptimizer.algenv_ignores_env_fun *)
  Fixpoint algenv_ignores_env_fun (e:algenv) : bool :=
    match e with
      | ANID => true
      | ANConst rd => true
      | ANBinop bop e1 e2 => andb (algenv_ignores_env_fun e1) (algenv_ignores_env_fun e2)
      | ANUnop uop e1 => algenv_ignores_env_fun e1
      | ANMap e1 e2 => andb (algenv_ignores_env_fun e1) (algenv_ignores_env_fun e2)
      | ANMapConcat e1 e2 => andb (algenv_ignores_env_fun e1) (algenv_ignores_env_fun e2)
      | ANProduct e1 e2 => andb (algenv_ignores_env_fun e1) (algenv_ignores_env_fun e2)
      | ANSelect e1 e2 => andb (algenv_ignores_env_fun e1) (algenv_ignores_env_fun e2)
      | ANDefault e1 e2 => andb (algenv_ignores_env_fun e1) (algenv_ignores_env_fun e2)
      | ANEither e1 e2 => andb (algenv_ignores_env_fun e1) (algenv_ignores_env_fun e2)
      | ANEitherConcat e1 e2 => andb (algenv_ignores_env_fun e1) (algenv_ignores_env_fun e2)
      | ANApp e1 e2 => andb (algenv_ignores_env_fun e1) (algenv_ignores_env_fun e2)
      | ANGetConstant _ => true
      | ANEnv => false
      | ANAppEnv e1 e2 => (algenv_ignores_env_fun e2)
      | ANMapEnv e1 => false
    end.

  Lemma algenv_ignores_env_eq (e:algenv):
    algenv_ignores_env e <-> (algenv_ignores_env_fun e = true).
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

  Fixpoint algenv_fixed_env (e:algenv) : Prop :=
    match e with
      | ANID => True
      | ANConst rd => True
      | ANBinop bop e1 e2 => (algenv_fixed_env e1) /\ (algenv_fixed_env e2)
      | ANUnop uop e1 => algenv_fixed_env e1
      | ANMap e1 e2 => (algenv_fixed_env e1) /\ (algenv_fixed_env e2)
      | ANMapConcat e1 e2 => (algenv_fixed_env e1) /\ (algenv_fixed_env e2)
      | ANProduct e1 e2 => (algenv_fixed_env e1) /\ (algenv_fixed_env e2)
      | ANSelect e1 e2 => (algenv_fixed_env e1) /\ (algenv_fixed_env e2)
      | ANDefault e1 e2 => (algenv_fixed_env e1) /\ (algenv_fixed_env e2)
      | ANEither e1 e2 => (algenv_fixed_env e1) /\ (algenv_fixed_env e2)
      | ANEitherConcat e1 e2 => (algenv_fixed_env e1) /\ (algenv_fixed_env e2)
      | ANApp e1 e2 => (algenv_fixed_env e1) /\ (algenv_fixed_env e2)
      | ANGetConstant _ => True 
      | ANEnv => True (* That's the difference with ignore... *)
      | ANAppEnv e1 e2 => False (* Changes the environment *)
      | ANMapEnv e1 => False (* Changes the environment *)
    end.

  Fixpoint algenv_fixed_env_fun (e:algenv) : bool :=
    match e with
      | ANID => true
      | ANConst rd => true
      | ANBinop bop e1 e2 => andb (algenv_fixed_env_fun e1) (algenv_fixed_env_fun e2)
      | ANUnop uop e1 => algenv_fixed_env_fun e1
      | ANMap e1 e2 => andb (algenv_fixed_env_fun e1) (algenv_fixed_env_fun e2)
      | ANMapConcat e1 e2 => andb (algenv_fixed_env_fun e1) (algenv_fixed_env_fun e2)
      | ANProduct e1 e2 => andb (algenv_fixed_env_fun e1) (algenv_fixed_env_fun e2)
      | ANSelect e1 e2 => andb (algenv_fixed_env_fun e1) (algenv_fixed_env_fun e2)
      | ANDefault e1 e2 => andb (algenv_fixed_env_fun e1) (algenv_fixed_env_fun e2)
      | ANEither e1 e2 => andb (algenv_fixed_env_fun e1) (algenv_fixed_env_fun e2)
      | ANEitherConcat e1 e2 => andb (algenv_fixed_env_fun e1) (algenv_fixed_env_fun e2)
      | ANApp e1 e2 => andb (algenv_fixed_env_fun e1) (algenv_fixed_env_fun e2)
      | ANGetConstant _ => true
      | ANEnv => true
      | ANAppEnv e1 e2 => false
      | ANMapEnv e1 => false
    end.

  Lemma algenv_fixed_env_eq (e:algenv):
    algenv_fixed_env e <-> (algenv_fixed_env_fun e = true).
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
  
  Fixpoint algenv_ignores_id (e:algenv) : Prop :=
    match e with
      | ANID => False
      | ANConst rd => True
      | ANBinop bop e1 e2 => (algenv_ignores_id e1) /\ (algenv_ignores_id e2)
      | ANUnop uop e1 => algenv_ignores_id e1
      | ANMap e1 e2 => algenv_ignores_id e2
      | ANMapConcat e1 e2 => algenv_ignores_id e2
      | ANProduct e1 e2 => (algenv_ignores_id e1) /\ (algenv_ignores_id e2)
      | ANSelect e1 e2 => (algenv_ignores_id e2)
      | ANDefault e1 e2 => (algenv_ignores_id e1) /\ (algenv_ignores_id e2)
      | ANEither e1 e2 => False
      | ANEitherConcat e1 e2 => (algenv_ignores_id e1) /\ (algenv_ignores_id e2)
      | ANApp e1 e2 => (algenv_ignores_id e2)
      | ANGetConstant _ => True
      | ANEnv => True
      | ANAppEnv e1 e2 => (algenv_ignores_id e1) /\ (algenv_ignores_id e2)
      | ANMapEnv e1 => (algenv_ignores_id e1)
    end.

  (* Java equivalent: NraOptimizer.algenv_ignores_id_fun *)
  Fixpoint algenv_ignores_id_fun (e:algenv) : bool :=
    match e with
      | ANID => false
      | ANConst rd => true
      | ANBinop bop e1 e2 => andb (algenv_ignores_id_fun e1) (algenv_ignores_id_fun e2)
      | ANUnop uop e1 => algenv_ignores_id_fun e1
      | ANMap e1 e2 => algenv_ignores_id_fun e2
      | ANMapConcat e1 e2 => algenv_ignores_id_fun e2
      | ANProduct e1 e2 => andb (algenv_ignores_id_fun e1) (algenv_ignores_id_fun e2)
      | ANSelect e1 e2 => (algenv_ignores_id_fun e2)
      | ANDefault e1 e2 => andb (algenv_ignores_id_fun e1) (algenv_ignores_id_fun e2)
      | ANEither e1 e2 => false
      | ANEitherConcat e1 e2 => andb (algenv_ignores_id_fun e1) (algenv_ignores_id_fun e2)
      | ANApp e1 e2 => (algenv_ignores_id_fun e2)
      | ANGetConstant _ => true
      | ANEnv => true
      | ANAppEnv e1 e2 => andb (algenv_ignores_id_fun e1) (algenv_ignores_id_fun e2)
      | ANMapEnv e1 => (algenv_ignores_id_fun e1)
    end.

  Lemma algenv_ignores_id_eq (e:algenv):
    algenv_ignores_id e <-> (algenv_ignores_id_fun e = true).
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
  
  Fixpoint algenv_deenv_alg (ae:algenv) : alg :=
    match ae with
      | ANID => AID
      | ANConst d => AConst d
      | ANBinop b ae1 ae2 => ABinop b (algenv_deenv_alg ae1) (algenv_deenv_alg ae2)
      | ANUnop u ae1 => AUnop u (algenv_deenv_alg ae1)
      | ANMap ea1 ea2 => AMap (algenv_deenv_alg ea1) (algenv_deenv_alg ea2)
      | ANMapConcat ea1 ea2 => AMapConcat (algenv_deenv_alg ea1) (algenv_deenv_alg ea2)
      | ANProduct ea1 ea2 => AProduct (algenv_deenv_alg ea1) (algenv_deenv_alg ea2)
      | ANSelect ea1 ea2 => ASelect (algenv_deenv_alg ea1) (algenv_deenv_alg ea2)
      | ANDefault ea1 ea2 => ADefault (algenv_deenv_alg ea1) (algenv_deenv_alg ea2)
      | ANEither ea1 ea2 => AEither (algenv_deenv_alg ea1) (algenv_deenv_alg ea2)
      | ANEitherConcat ea1 ea2 => AEitherConcat (algenv_deenv_alg ea1) (algenv_deenv_alg ea2)
      | ANApp ea1 ea2 => AApp (algenv_deenv_alg ea1) (algenv_deenv_alg ea2)
      | ANGetConstant _ => AID
      | ANEnv => AID
      | ANAppEnv ea1 ea2 => AID
      | ANMapEnv ea1 => AID
    end.

  Lemma algenv_ignores_env_swap (e:algenv) :
    algenv_ignores_env e -> forall (h:list (string*string)) c,
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
      generalize ((fun_of_algenv h c e2 env2)); intros.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      induction l; try reflexivity; simpl.
      rewrite (IHe1 H0 h env1 env2); clear IHe1 H0.
      destruct (fun_of_algenv h c e1 env2 a); intros; trivial.
      unfold lift in *; simpl in *.
      revert IHl.
      generalize (rmap (fun_of_algenv h c e1 env1) l); 
        generalize (rmap (fun_of_algenv h c e1 env2) l); intros.
      destruct o1; destruct o0; simpl; congruence.
    - inversion H; clear H.
      rewrite (IHe2 H1 h env1 env2); clear IHe2 H1.
      generalize (h ⊢ₑ e2 @ₑ x ⊣ c;env2); intros.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      induction l; try reflexivity; simpl.
      unfold lift in *; simpl.
      unfold rmap_concat in *; simpl.
      unfold oomap_concat in *; simpl.
      rewrite (IHe1 H0 h env1 env2); clear IHe1 H0.
      generalize (h ⊢ₑ e1 @ₑ a ⊣ c;env2); intros.
      destruct o; try reflexivity; simpl.
      revert IHl.
      generalize (oflat_map
       (fun a0 : data =>
        match h ⊢ₑ e1 @ₑ a0 ⊣ c;env1 with
        | Some (dcoll y) => omap_concat a0 y
        | _ => None
        end) l
        ); generalize (oflat_map
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
  
  Lemma algenv_ignores_id_swap (e:algenv) :
    algenv_ignores_id e -> forall h:list (string*string), forall c,
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
      apply rmap_ext; intros.
      rewrite (IHe H h x x1 x2); reflexivity.
  Qed.

  Require Import RAlgSugar.
  Lemma algenv_is_nra_deenv (h:list (string*string)) c (e:algenv) (d1 d2:data) :
    algenv_is_nra e ->
        h ⊢ (alg_of_algenv e) @ₐ (pat_context_data c d1 d2) =
        h ⊢ (algenv_deenv_alg e) @ₐ d2.
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
      generalize (fun_of_alg h (algenv_deenv_alg e2) d2); intros; simpl; clear e2.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      unfold lift, rmap_concat, oomap_concat; simpl.
      rewrite rmap_map_rec1 in *; simpl.
      rewrite omap_concat_map_rec in *; simpl.
      rewrite app_nil_r.
      rewrite rmap_remove1; simpl.
      unfold pat_context_data in *.
      induction l; try reflexivity; simpl.
      rewrite IHe1; simpl.
      destruct (fun_of_alg h (algenv_deenv_alg e1) a); try reflexivity.
      unfold lift; simpl.
      revert IHl.
      generalize (rmap (fun_of_alg h (alg_of_algenv e1))
                       (map (fun x : data => drec (("PBIND"%string, d1) :: ("PCONST"%string, c):: ("PDATA"%string, x) :: nil)) l));
        generalize (rmap (fun_of_alg h (algenv_deenv_alg e1)) l); intros.
      destruct o; destruct o0; try congruence.
    - inversion H; clear H.
      specialize (IHe1 H0); clear H0.
      specialize (IHe2 H1); clear H1.
      rewrite IHe2; clear IHe2.
      unfold olift, olift2; simpl.
      generalize (fun_of_alg h (algenv_deenv_alg e2) d2); intros; simpl; clear e2.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      unfold lift, rmap_concat, oomap_concat; simpl.
      rewrite rmap_map_rec1 in *; simpl.
      rewrite omap_concat_map_rec in *; simpl.
      rewrite app_nil_r in *.
      rewrite rmap_remove1 in *; simpl.
      unfold pat_context_data in *.
      induction l; try reflexivity; simpl.
      rewrite IHe1; simpl; clear IHe1.
      generalize (fun_of_alg h (algenv_deenv_alg e1) a); intros.
      destruct o; try reflexivity.
      destruct d; try reflexivity.
      unfold lift_oncoll in *; simpl in *.
      rewrite rmap_map_rec1 in *; simpl in *.
      rewrite omap_concat_map_rec2 in *; simpl in *.
      unfold lift in *; simpl in *.
      revert IHl.
      generalize (
                 oflat_map
         (fun a0 : data =>
          match
            match fun_of_alg h (alg_of_algenv e1) a0 with
            | Some (dcoll l1) =>
                match
                  rmap (fun x : data => Some (drec (("PDATA2"%string, x) :: nil))) l1
                with
                | Some a' => Some (dcoll a')
                | None => None
                end
            | _ => None
            end
          with
          | Some (dcoll y) => omap_concat a0 y
          | _ => None
          end) (map (fun x : data => drec (("PBIND"%string, d1) :: ("PCONST"%string, c):: ("PDATA"%string, x) :: nil)) l)

        ); generalize (
     oflat_map
       (fun a0 : data =>
        match fun_of_alg h (algenv_deenv_alg e1) a0 with
        | Some (dcoll y) => omap_concat a0 y
        | _ => None
        end) l
             ); intros.
      destruct o; destruct o0; try reflexivity; try congruence; simpl; try rewrite rmap_map_unnest2; simpl in *.
      * generalize rmap_map_unnest2; intros HH.
        unfold olift2 in HH.
        rewrite HH; clear HH.
        revert IHl.
        unfold olift2 in *; simpl in *.
        generalize (     rmap
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
      * generalize rmap_map_unnest2; intros HH.
        unfold olift2 in HH.
        rewrite HH; clear HH.
        revert IHl.
        unfold olift2 in *; simpl in *.
        generalize (     rmap
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
      generalize (fun_of_alg h (algenv_deenv_alg e2) d2); intros; simpl; clear e2.
      destruct o; try reflexivity; simpl.
      destruct d; try reflexivity; simpl.
      unfold lift, rmap_concat, oomap_concat; simpl.
      rewrite rmap_map_rec1 in *; simpl.
      rewrite omap_concat_map_rec in *; simpl.
      rewrite app_nil_r in *.
      rewrite rmap_remove1 in *; simpl.
      unfold pat_context_data in *.
      induction l; try reflexivity; simpl.
      rewrite IHe1; simpl; clear IHe1.
      generalize (fun_of_alg h (algenv_deenv_alg e1) a); intros.
      destruct o; try reflexivity.
      destruct d; try reflexivity.
      unfold lift_oncoll in *; simpl in *.
      revert IHl.
      generalize (lift_filter
         (fun x' : data =>
          match fun_of_alg h (alg_of_algenv e1) x' with
          | Some (dbool b0) => Some b0
          | _ => None
          end) (map (fun x : data => drec (("PBIND"%string, d1) :: ("PCONST"%string, c):: ("PDATA"%string, x) :: nil)) l)
                 ); intros.
      destruct o; try reflexivity; try congruence; simpl.
      * destruct b; try reflexivity.
        rewrite rmap_one1.
        revert IHl.
        generalize (rmap
         (fun x : data =>
          match x with
          | drec r => edot r "PDATA"
          | _ => None
          end) l0);
        generalize (lift_filter
       (fun x' : data =>
        match fun_of_alg h (algenv_deenv_alg e1) x' with
        | Some (dbool b) => Some b
        | _ => None
        end) l
                                 ); intros.
        destruct o; destruct o0; try reflexivity; try congruence; simpl.
        revert IHl.
        generalize (rmap
         (fun x : data =>
          match x with
          | drec r => edot r "PDATA"
          | _ => None
          end) l0);
        generalize (lift_filter
       (fun x' : data =>
        match fun_of_alg h (algenv_deenv_alg e1) x' with
        | Some (dbool b) => Some b
        | _ => None
        end) l
                                 ); intros.
        destruct o; destruct o0; try reflexivity; congruence.
      * revert IHl.
        generalize (lift_filter
       (fun x' : data =>
        match fun_of_alg h (algenv_deenv_alg e1) x' with
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
      generalize (fun_of_alg h (algenv_deenv_alg e2) d2); intros; simpl.
      destruct o; try reflexivity; simpl;
      unfold pat_context_data in *;
      rewrite IHe1; reflexivity.
    - inversion H; clear H.
      specialize (IHe1 H0); clear H0.
      specialize (IHe2 H1); clear H1.
      rewrite IHe2; simpl; clear IHe2.
      generalize (fun_of_alg h (algenv_deenv_alg e2) d2); intros; simpl.
      destruct o; try reflexivity; simpl.
      unfold pat_context_data in *;
      rewrite IHe1; reflexivity.
  Qed.

  (* TODO: try to define ANEitherConcat. *)
  (* TODO: this (and the Proper) should move *)
  Fixpoint algenv_of_alg (a:alg) : algenv :=
    match a with
      | AID => ANID
      | AConst d => ANConst d
      | ABinop b e1 e2 => ANBinop b (algenv_of_alg e1) (algenv_of_alg e2)
      | AUnop u e1 => ANUnop u (algenv_of_alg e1)
      | AMap e1 e2 => ANMap (algenv_of_alg e1) (algenv_of_alg e2)
      | AMapConcat e1 e2 => ANMapConcat (algenv_of_alg e1) (algenv_of_alg e2)
      | AProduct e1 e2 => ANProduct (algenv_of_alg e1) (algenv_of_alg e2)
      | ASelect e1 e2 => ANSelect (algenv_of_alg e1) (algenv_of_alg e2)
      | ADefault e1 e2 => ANDefault (algenv_of_alg e1) (algenv_of_alg e2)
      | AEither opl opr => ANEither (algenv_of_alg opl) (algenv_of_alg opr)
      | AEitherConcat op1 op2 => ANEitherConcat (algenv_of_alg op1) (algenv_of_alg op2)
      | AApp e1 e2 => ANApp (algenv_of_alg e1) (algenv_of_alg e2)
    end.

  Lemma fun_of_algenv_of_alg h c e d env :
    fun_of_alg h e d = fun_of_algenv h c (algenv_of_alg e) env d.
  Proof.
    revert d env.
    induction e; simpl; trivial; intros;
    try rewrite <- IHe;
    try rewrite <- IHe1; try rewrite <- IHe2; trivial;
    repeat (first [
                apply olift_ext
              | apply lift_oncoll_ext
              | apply lift_dcoll_inversion
              | apply rmap_ext
              | apply rmap_concat_ext
              | apply lift_filter_ext]; intros); trivial.
    - rewrite <- IHe1; trivial.
    - match_destr.
  Qed.
  
  Lemma algenv_of_alg_is_nra x : algenv_is_nra (algenv_of_alg x).
  Proof.
    induction x; simpl; auto.
  Qed.

  Lemma algenv_deenv_alg_of_alg x : algenv_deenv_alg (algenv_of_alg x) = x.
  Proof.
    induction x; simpl; try congruence.
  Qed.
    
End RAlgEnvIgnore.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
