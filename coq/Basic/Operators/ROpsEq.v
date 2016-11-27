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

Section ROpsEq.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.
  Require Import List.
  Require Import String.

  Require Import Utils.
  Require Import BrandRelation.
  Require Import RData RDataNorm RRelation.
  Require Import RUtilOps RBinaryOpsSem RUnaryOpsSem.
  Require Import ForeignData.
  Require Import ForeignOps.

  Context {fdata:foreign_data}.
  Context {fuop:foreign_unary_op}.
  Context {fbop:foreign_binary_op}.

  (* Equivalence relation between operators.
     Two plans are equivalent iff they return the same value for every input.
   *)

  Definition unaryop_eq (uop1 uop2:unaryOp) : Prop :=
    forall (h:list (string*string)),
    forall (x:data),
      data_normalized h x ->
      (fun_of_unaryop h uop1) x = (fun_of_unaryop h uop2) x.

  Global Instance unaryop_equiv : Equivalence unaryop_eq.
  Proof.
    constructor.
    - unfold Reflexive, unaryop_eq.
      intros; reflexivity.
    - unfold Symmetric, unaryop_eq.
      intros; rewrite H by trivial; reflexivity.
    - unfold Transitive, unaryop_eq.
      intros; rewrite H, H0 by trivial; reflexivity.
  Qed.

  Definition binop_eq (bop1 bop2:binOp) : Prop :=
    forall (h:list (string*string)),
    forall (x:data),
      data_normalized h x ->
      forall (y:data),
        data_normalized h x ->
        (fun_of_binop h bop1) x y = (fun_of_binop h bop2) x y.

  Global Instance binop_equiv : Equivalence binop_eq.
  Proof.
    constructor.
    - unfold Reflexive, binop_eq.
      intros; reflexivity.
    - unfold Symmetric, binop_eq.
      intros; rewrite (H h) by trivial; reflexivity.
    - unfold Transitive, binop_eq.
      intros; rewrite (H h), (H0 h) by trivial; reflexivity.
  Qed.

End ROpsEq.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
