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

Section NNRCExtEq.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.
  Require Import String.
  Require Import List.
  Require Import Arith.
  
  Require Import Utils BasicRuntime.
  Require Import NNRC NNRCNorm NNRCEq.
  Require Import NNRCExt.

  Context {fruntime:foreign_runtime}.

  (** Equivalence between expressions in the Named Nested Relational Calculus *)

  (** Semantics of NNRC *)
  Definition nnrc_ext_eq (e1 e2:nnrc) : Prop :=
    forall (h:brand_relation_t),
    forall (env:bindings),
      Forall (data_normalized h) (map snd env) ->
      @nnrc_ext_eval _ h env e1 = @nnrc_ext_eval _ h env e2.

  Global Instance nnrc_ext_equiv : Equivalence nnrc_ext_eq.
  Proof.
    constructor.
    - unfold Reflexive, nnrc_ext_eq.
      intros; reflexivity.
    - unfold Symmetric, nnrc_ext_eq.
      intros; rewrite (H h env) by trivial; reflexivity.
    - unfold Transitive, nnrc_ext_eq.
      intros; rewrite (H h env) by trivial;
      rewrite (H0 h env) by trivial; reflexivity.
  Qed.

  (* all the nnrc constructors are proper wrt. equivalence *)

  (* NRCVar *)
  Global Instance var_ext_proper : Proper (eq ==> nnrc_ext_eq) NNRCVar.
  Proof.
    unfold Proper, respectful, nnrc_ext_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NNRCConst *)
  
  Global Instance const_ext_proper : Proper (eq ==> nnrc_ext_eq) NNRCConst.
  Proof.
    unfold Proper, respectful, nnrc_ext_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NNRCBinop *)
  
  Global Instance binop_ext_proper : Proper (binop_eq ==> nnrc_ext_eq ==> nnrc_ext_eq ==> nnrc_ext_eq) NNRCBinop.
  Proof.
    generalize binop_proper; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_ext_eq, nnrc_ext_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.

  (* NNRCUnnop *)
  
  Global Instance unop_ext_proper : Proper (unaryop_eq ==> nnrc_ext_eq ==> nnrc_ext_eq) NNRCUnop.
  Proof.
    generalize unop_proper; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_ext_eq, nnrc_ext_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.
    
  (* NNRCLet *)
  
  Global Instance let_ext_proper : Proper (eq ==> nnrc_ext_eq ==> nnrc_ext_eq ==> nnrc_ext_eq) NNRCLet.
  Proof.
    generalize let_proper; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_ext_eq, nnrc_ext_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.
    
  (* NNRCFor *)

  Global Instance for_ext_proper : Proper (eq ==> nnrc_ext_eq ==> nnrc_ext_eq ==> nnrc_ext_eq) NNRCFor.
  Proof.
    generalize for_proper; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_ext_eq, nnrc_ext_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.

  (* NNRCIf *)
  
  Global Instance if_ext_proper : Proper (nnrc_ext_eq ==> nnrc_ext_eq ==> nnrc_ext_eq ==> nnrc_ext_eq) NNRCIf.
  Proof.
    generalize if_proper; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_ext_eq, nnrc_ext_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.

  (* NNRCEither *)
  Global Instance either_ext_proper : Proper (nnrc_ext_eq ==> eq ==> nnrc_ext_eq ==> eq ==> nnrc_ext_eq ==> nnrc_ext_eq) NNRCEither.
  Proof.
    generalize either_proper; intros Hnnrc_core_prop.
    unfold Proper, respectful, nnrc_ext_eq, nnrc_ext_eval; intros.
    apply Hnnrc_core_prop; auto.
  Qed.

  (* NNRCGroupBy *)
  (* Fails for core *)

  Global Instance group_by_ext_proper : Proper (eq ==> eq ==> nnrc_ext_eq ==> nnrc_ext_eq) NNRCGroupBy.
  Proof.
    unfold Proper, respectful; intros.
    unfold nnrc_ext_eq in *.
    unfold nnrc_ext_eval in *.
    simpl (nnrc_ext_to_nnrc (NNRCGroupBy x x0 x1)).
    simpl (nnrc_ext_to_nnrc (NNRCGroupBy y y0 y1)).
    subst.
    unfold nnrc_group_by.
    intros.
    simpl.
    rewrite H1.
    reflexivity.
    assumption.
  Qed.

End NNRCExtEq.

Notation "X ≡ᶜ Y" := (nnrc_ext_eq X Y) (at level 90) : nnrc_scope.                             (* ≡ = \equiv *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
