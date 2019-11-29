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
Require Import Utils.
Require Import CommonRuntime.
Require Import cNNRC.
Require Import cNNRCNorm.

Section cNNRCEq.
  Context {fruntime:foreign_runtime}.

  (** Equivalence between expressions in the Named Nested Relational Calculus *)

  (** Semantics of NNRC *)
  Definition nnrc_core_eq (e1 e2:nnrc) : Prop :=
    forall (h:brand_relation_t),
    forall (cenv:bindings),
    forall (env:bindings),
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      nnrc_core_eval h cenv env e1 = nnrc_core_eval h cenv env e2.

  Global Instance nnrc_core_equiv : Equivalence nnrc_core_eq.
  Proof.
    constructor.
    - unfold Reflexive, nnrc_core_eq.
      intros; reflexivity.
    - unfold Symmetric, nnrc_core_eq.
      intros; rewrite (H h cenv env) by trivial; reflexivity.
    - unfold Transitive, nnrc_core_eq.
      intros; rewrite (H h cenv env) by trivial;
      rewrite (H0 h cenv env) by trivial; reflexivity.
  Qed.

  (** All the nnrc constructors are proper wrt. equivalence. *)

  (* NNRCGetConstant *)
  
  Global Instance proper_cNNRCGetConstant : Proper (eq ==> nnrc_core_eq) NNRCGetConstant.
  Proof.
    unfold Proper, respectful, nnrc_core_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NNRCVar *)
  Global Instance proper_cNNRCVar : Proper (eq ==> nnrc_core_eq) NNRCVar.
  Proof.
    unfold Proper, respectful, nnrc_core_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NNRCConst *)
  
  Global Instance proper_cNNRCConst : Proper (eq ==> nnrc_core_eq) NNRCConst.
  Proof.
    unfold Proper, respectful, nnrc_core_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NNRCBinop *)
  
  Global Instance proper_cNNRCBinop : Proper (binary_op_eq ==> nnrc_core_eq ==> nnrc_core_eq ==> nnrc_core_eq) NNRCBinop.
  Proof.
    unfold Proper, respectful, nnrc_core_eq.
    intros; simpl; rewrite H0 by trivial; rewrite H1 by trivial; clear H0 H1.
    case_eq (nnrc_core_eval h cenv env y0);
      case_eq (nnrc_core_eval h cenv env y1); intros; simpl; trivial.
    rewrite (H h); eauto.
  Qed.

  (* NNRCUnop *)
  
  Global Instance proper_cNNRCUnop : Proper (unary_op_eq ==> nnrc_core_eq ==> nnrc_core_eq) NNRCUnop.
  Proof.
    unfold Proper, respectful, nnrc_core_eq.
    intros; simpl; rewrite H0 by trivial; clear H0.
    case_eq (nnrc_core_eval h cenv env y0); simpl; trivial; intros.
    rewrite (H h); eauto.
  Qed.
    
  (* NNRCLet *)
  
  Global Instance proper_cNNRCLet : Proper (eq ==> nnrc_core_eq ==> nnrc_core_eq ==> nnrc_core_eq) NNRCLet.
  Proof.
    unfold Proper, respectful, nnrc_core_eq.
    intros; simpl. rewrite H0 by trivial; clear H0.
    case_eq (nnrc_core_eval h cenv env y0); simpl; trivial; intros.
    rewrite H; clear H.
    rewrite H1; eauto.
    constructor; eauto.
  Qed.

  (* NNRCFor *)

    Hint Resolve data_normalized_dcoll_in.

  Global Instance proper_cNNRCFor : Proper (eq ==> nnrc_core_eq ==> nnrc_core_eq ==> nnrc_core_eq) NNRCFor.
  Proof.
    unfold Proper, respectful, nnrc_core_eq.
    intros; simpl. rewrite H0 by trivial; clear H0. subst.
    case_eq (nnrc_core_eval h cenv env y0); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    f_equal.
    apply lift_map_ext; intros.
    apply H1; simpl; eauto.
  Qed.

  (* NNRCIf *)
  
  Global Instance proper_cNNRCIf : Proper (nnrc_core_eq ==> nnrc_core_eq ==> nnrc_core_eq ==> nnrc_core_eq) NNRCIf.
  Proof.
    unfold Proper, respectful, nnrc_core_eq.
    intros; simpl. rewrite H by trivial; clear H.
    case_eq (nnrc_core_eval h cenv env y); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    destruct b; eauto.
  Qed.

  (* NNRCEither *)
  Global Instance proper_cNNRCEither : Proper (nnrc_core_eq ==> eq ==> nnrc_core_eq ==> eq ==> nnrc_core_eq ==> nnrc_core_eq) NNRCEither.
  Proof.
    unfold Proper, respectful, nnrc_core_eq.
    intros; simpl. subst.
    rewrite H by trivial.
    match_case; intros ? eqq1. match_destr.
    - assert (dn:data_normalized h (dleft d)) by eauto.
      inversion dn; subst.
      apply H1; simpl; eauto.
    - assert (dn:data_normalized h (dright d)) by eauto.
      inversion dn; subst.
      apply H3; simpl; eauto.
  Qed.

  (* NNRCGroupBy *)
  (* Fails for core *)
  
  Global Instance proper_cNNRCGroupBy : Proper (eq ==> eq ==> nnrc_core_eq ==> nnrc_core_eq) NNRCGroupBy.
  Proof.
    unfold Proper, respectful, nnrc_core_eq.
    intros; reflexivity.
  Qed.

End cNNRCEq.

Notation "X ≡ᶜᶜ Y" := (nnrc_core_eq X Y) (at level 90) : nnrc_scope.                             (* ≡ = \equiv *)

