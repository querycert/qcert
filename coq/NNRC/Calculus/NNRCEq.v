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

Section NNRCEq.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.
  Require Import String.
  Require Import List.
  Require Import Arith.
  
  Require Import Utils BasicRuntime.
  Require Import NNRC.

  Context {fruntime:foreign_runtime}.

  (** Equivalence between expressions in the Named Nested Relational Calculus *)

  (** Semantics of NNRC *)
  Definition nnrc_eq (e1 e2:nrc) : Prop :=
    forall (h:brand_relation_t),
    forall (env:bindings),
      Forall (data_normalized h) (map snd env) ->
      nrc_eval h env e1 = nrc_eval h env e2.

  Global Instance nnrc_equiv : Equivalence nnrc_eq.
  Proof.
    constructor.
    - unfold Reflexive, nnrc_eq.
      intros; reflexivity.
    - unfold Symmetric, nnrc_eq.
      intros; rewrite (H h env) by trivial; reflexivity.
    - unfold Transitive, nnrc_eq.
      intros; rewrite (H h env) by trivial;
      rewrite (H0 h env) by trivial; reflexivity.
  Qed.

  (* all the nnrc constructors are proper wrt. equivalence *)

  (* NRCVar *)
  Global Instance var_proper : Proper (eq ==> nnrc_eq) NRCVar.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NRCConst *)
  
  Global Instance const_proper : Proper (eq ==> nnrc_eq) NRCConst.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NRCBinop *)
  
  Global Instance binop_proper : Proper (binop_eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NRCBinop.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; simpl; rewrite H0 by trivial; rewrite H1 by trivial; clear H0 H1.
    case_eq (nrc_eval h env y0); case_eq (nrc_eval h env y1); intros; simpl; trivial.
    rewrite (H h); eauto.
  Qed.

  (* NRCUnnop *)
  
  Global Instance unop_proper : Proper (unaryop_eq ==> nnrc_eq ==> nnrc_eq) NRCUnop.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; simpl; rewrite H0 by trivial; clear H0.
    case_eq (nrc_eval h env y0); simpl; trivial; intros.
    rewrite (H h); eauto.
  Qed.
    
  (* NRCLet *)
  
  Global Instance let_proper : Proper (eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NRCLet.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; simpl. rewrite H0 by trivial; clear H0.
    case_eq (nrc_eval h env y0); simpl; trivial; intros.
    rewrite H; clear H.
    rewrite H1; eauto.
    constructor; eauto.
  Qed.
    
  (* NRCFor *)

    Hint Resolve data_normalized_dcoll_in.

  Global Instance for_proper : Proper (eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NRCFor.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; simpl. rewrite H0 by trivial; clear H0. subst.
    case_eq (nrc_eval h env y0); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    f_equal.
    apply rmap_ext; intros.
    apply H1; simpl; eauto.
  Qed.

  (* NRCIf *)
  
  Global Instance if_proper : Proper (nnrc_eq ==> nnrc_eq ==> nnrc_eq ==> nnrc_eq) NRCIf.
  Proof.
    unfold Proper, respectful, nnrc_eq.
    intros; simpl. rewrite H by trivial; clear H.
    case_eq (nrc_eval h env y); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    destruct b; eauto.
  Qed.

  (* NRCEither *)
  Global Instance either_proper : Proper (nnrc_eq ==> eq ==> nnrc_eq ==> eq ==> nnrc_eq ==> nnrc_eq) NRCEither.
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

End NNRCEq.

Notation "X ≡ᶜ Y" := (nnrc_eq X Y) (at level 90) : nrc_scope.                             (* ≡ = \equiv *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
