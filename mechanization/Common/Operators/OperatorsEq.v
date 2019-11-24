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

(*************************
 * Operators equivalence *
 *************************)

Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import List.
Require Import String.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignData.
Require Import ForeignDataToJSON.
Require Import Data.
Require Import DataNorm.
Require Import Iterators.
Require Import OperatorsUtils.
Require Import BinaryOperatorsSem.
Require Import UnaryOperatorsSem.
Require Import ForeignOperators.

Section OperatorsEq.
  Context {fdata:foreign_data}.
  Context {fuop:foreign_unary_op}.
  Context {fbop:foreign_binary_op}.
  Context {ftojson:foreign_to_JSON}.

  (* Equivalence relation between operators.
     Two plans are equivalent iff they return the same value for every input.
   *)

  Definition unary_op_eq (uop1 uop2:unary_op) : Prop :=
    forall (h:list (string*string)),
    forall (x:data),
      data_normalized h x ->
      (unary_op_eval h uop1) x = (unary_op_eval h uop2) x.

  Global Instance unary_op_equiv : Equivalence unary_op_eq.
  Proof.
    constructor.
    - unfold Reflexive, unary_op_eq.
      intros; reflexivity.
    - unfold Symmetric, unary_op_eq.
      intros; rewrite H by trivial; reflexivity.
    - unfold Transitive, unary_op_eq.
      intros; rewrite H, H0 by trivial; reflexivity.
  Qed.

  Definition binary_op_eq (bop1 bop2:binary_op) : Prop :=
    forall (h:list (string*string)),
    forall (x:data),
      data_normalized h x ->
      forall (y:data),
        data_normalized h x ->
        (binary_op_eval h bop1) x y = (binary_op_eval h bop2) x y.

  Global Instance binary_op_equiv : Equivalence binary_op_eq.
  Proof.
    constructor.
    - unfold Reflexive, binary_op_eq.
      intros; reflexivity.
    - unfold Symmetric, binary_op_eq.
      intros; rewrite (H h) by trivial; reflexivity.
    - unfold Transitive, binary_op_eq.
      intros; rewrite (H h), (H0 h) by trivial; reflexivity.
  Qed.

End OperatorsEq.
