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

Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import String.
Require Import List.
Require Import Arith.
Require Import CommonRuntime.
Require Import cNNRC.
Require Import cNNRCNorm.
Require Import cNNRCEq.
Require Import NNRC.

Section NNRCEq.
  Context {fruntime:foreign_runtime}.

  (** Equivalence between expressions in the Named Nested Relational Calculus *)

  (** Semantics of NNRC *)
  Definition nnrc_eq (e1 e2:nnrc) : Prop :=
    forall (h:brand_relation_t),
    forall (cenv:bindings),
    forall (env:bindings),
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      @nnrc_eval _ h cenv env e1 = @nnrc_eval _ h cenv env e2.

  Global Instance nnrc_equiv : Equivalence nnrc_eq.
  Proof.
    constructor.
    - unfold Reflexive, nnrc_eq.
      intros; reflexivity.
    - unfold Symmetric, nnrc_eq.
      intros; rewrite (H h cenv env) by trivial; reflexivity.
    - unfold Transitive, nnrc_eq.
      intros; rewrite (H h cenv env) by trivial;
      rewrite (H0 h cenv env) by trivial; reflexivity.
  Qed.

  (* all the nnrc constructors are proper wrt. equivalence *)

  (* NNRCGetConstant *)
  Global Instance proper_NNRCGetConstant : Proper (eq ==> nnrc_eq) NNRCGetConstant.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NNRCVar *)
  Global Instance proper_NNRCVar : Proper (eq ==> nnrc_eq) NNRCVar.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NNRCConst *)
  Global Instance proper_NNRCConst : Proper (eq ==> nnrc_eq) NNRCConst.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NNRCBinop *)
  
  Global Instance proper_NNRCBinop : Proper (binary_op_eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NNRCBinop.
  Proof.
    generalize proper_cNNRCBinop; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_eq, nnrc_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.

  (* NNRCUnnop *)

  Global Instance proper_NNRCUnnop : Proper (unary_op_eq ==> nnrc_eq ==> nnrc_eq) NNRCUnop.
  Proof.
    generalize proper_cNNRCUnop; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_eq, nnrc_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.
    
  (* NNRCLet *)
  
  Global Instance proper_NNRCLet : Proper (eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NNRCLet.
  Proof.
    generalize proper_cNNRCLet; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_eq, nnrc_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.

  (* NNRCFor *)

  Global Instance proper_NNRCFor : Proper (eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NNRCFor.
  Proof.
    generalize proper_cNNRCFor; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_eq, nnrc_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.

  (* NNRCIf *)
  
  Global Instance proper_NNRCIf : Proper (nnrc_eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NNRCIf.
  Proof.
    generalize proper_cNNRCIf; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_eq, nnrc_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.

  (* NNRCEither *)
  Global Instance proper_NNRCEither : Proper (nnrc_eq ==> eq ==> nnrc_eq ==> eq ==> nnrc_eq ==> nnrc_eq) NNRCEither.
  Proof.
    generalize proper_cNNRCEither; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_eq, nnrc_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.

  (* NNRCGroupBy *)
  Global Instance proper_NNRCGroupBy : Proper (eq ==> eq ==> nnrc_eq ==> nnrc_eq) NNRCGroupBy.
  Proof.
    unfold Proper, respectful; intros.
    unfold nnrc_eq in *.
    unfold nnrc_eval in *.
    simpl (nnrc_to_nnrc_base (NNRCGroupBy x x0 x1)).
    simpl (nnrc_to_nnrc_base (NNRCGroupBy y y0 y1)).
    subst.
    unfold nnrc_group_by.
    intros.
    simpl.
    rewrite H1.
    reflexivity.
    assumption.
    assumption.
  Qed.

End NNRCEq.

Notation "X ≡ᶜ Y" := (nnrc_eq X Y) (at level 90) : nnrc_scope.                             (* ≡ = \equiv *)

