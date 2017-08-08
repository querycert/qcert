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

Section cNNRCEq.
  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import BasicRuntime.
  Require Import cNNRC.
  Require Import cNNRCNorm.

  Context {fruntime:foreign_runtime}.

  (** Equivalence between expressions in the Named Nested Relational Calculus *)

  (** Semantics of NNRC *)
  Definition nnrc_eq (e1 e2:nnrc) : Prop :=
    forall (h:brand_relation_t),
    forall (cenv:bindings),
    forall (env:bindings),
      Forall (data_normalized h) (map snd cenv) ->
      Forall (data_normalized h) (map snd env) ->
      nnrc_core_eval h cenv env e1 = nnrc_core_eval h cenv env e2.

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
  
  Global Instance get_constant_proper : Proper (eq ==> nnrc_eq) NNRCGetConstant.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NNRCVar *)
  Global Instance var_proper : Proper (eq ==> nnrc_eq) NNRCVar.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NNRCConst *)
  
  Global Instance const_proper : Proper (eq ==> nnrc_eq) NNRCConst.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NNRCBinop *)
  
  Global Instance binop_proper : Proper (binop_eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NNRCBinop.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; simpl; rewrite H0 by trivial; rewrite H1 by trivial; clear H0 H1.
    case_eq (nnrc_core_eval h cenv env y0);
      case_eq (nnrc_core_eval h cenv env y1); intros; simpl; trivial.
    rewrite (H h); eauto.
  Qed.

  (* NNRCUnnop *)
  
  Global Instance unop_proper : Proper (unaryop_eq ==> nnrc_eq ==> nnrc_eq) NNRCUnop.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; simpl; rewrite H0 by trivial; clear H0.
    case_eq (nnrc_core_eval h cenv env y0); simpl; trivial; intros.
    rewrite (H h); eauto.
  Qed.
    
  (* NNRCLet *)
  
  Global Instance let_proper : Proper (eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NNRCLet.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; simpl. rewrite H0 by trivial; clear H0.
    case_eq (nnrc_core_eval h cenv env y0); simpl; trivial; intros.
    rewrite H; clear H.
    rewrite H1; eauto.
    constructor; eauto.
  Qed.

  (* NNRCFor *)

    Hint Resolve data_normalized_dcoll_in.

  Global Instance for_proper : Proper (eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NNRCFor.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; simpl. rewrite H0 by trivial; clear H0. subst.
    case_eq (nnrc_core_eval h cenv env y0); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    f_equal.
    apply rmap_ext; intros.
    apply H1; simpl; eauto.
  Qed.

  (* NNRCIf *)
  
  Global Instance if_proper : Proper (nnrc_eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NNRCIf.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; simpl. rewrite H by trivial; clear H.
    case_eq (nnrc_core_eval h cenv env y); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    destruct b; eauto.
  Qed.

  (* NNRCEither *)
  Global Instance either_proper : Proper (nnrc_eq ==> eq ==> nnrc_eq ==> eq ==> nnrc_eq ==> nnrc_eq) NNRCEither.
  Proof.
    unfold Proper, respectful, nnrc_eq.
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
  
  Global Instance group_by_proper : Proper (eq ==> eq ==> nnrc_eq ==> nnrc_eq) NNRCGroupBy.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; reflexivity.
  Qed.

End cNNRCEq.

Notation "X ≡ᶜᶜ Y" := (nnrc_eq X Y) (at level 90) : nnrc_scope.                             (* ≡ = \equiv *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
