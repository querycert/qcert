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

(*******************************
 * Operators typed equivalence *
 *******************************)

Section TOpsEq.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.

  Require Import List.
  Require Import String.

  Require Import Utils Types BasicRuntime.
  Require Import ForeignDataTyping ForeignOpsTyping.
  Require Import TData TOps.

  (* Two well-typed operators are type equivalent iff they return the
     same value for every well-typed input.
   *)
    Context {fdata:foreign_data}.
    Context {fuop:foreign_unary_op}.
    Context {fbop:foreign_binary_op}.
    Context {ftype:foreign_type}.
    Context {fdtyping:foreign_data_typing}.
    Context {m:brand_model}.
    Context {fuoptyping:foreign_unary_op_typing}.
    Context {fboptyping:foreign_binary_op_typing}.

  Definition typed_unaryOp τin τout := {u:unaryOp|unaryOp_type u τin τout}.

  Definition tunaryop_eq {τin τout} (uop1 uop2:typed_unaryOp τin τout) : Prop :=
    forall (x:data), data_type x τin -> (fun_of_unaryop brand_relation_brands (`uop1)) x = (fun_of_unaryop brand_relation_brands (`uop2)) x.
  
  Global Instance tunaryop_equiv {τin τout} : Equivalence (@tunaryop_eq τin τout).
  Proof.
    constructor.
    - unfold Reflexive, tunaryop_eq.
      intros; reflexivity.
    - unfold Symmetric, tunaryop_eq.
      intros; rewrite (H x0); [reflexivity|assumption].
    - unfold Transitive, tunaryop_eq.
      intros; rewrite (H x0); try assumption; rewrite (H0 x0); [reflexivity|assumption].
  Qed.

  Definition tunaryOp_rewrites_to {τ₁ τ₂} (u1 u2:unaryOp) :=
    unaryOp_type u1 τ₁ τ₂ ->
    unaryOp_type u2 τ₁ τ₂ ->
    (forall (x:data), data_type x τ₁ -> (fun_of_unaryop brand_relation_brands u1) x = (fun_of_unaryop brand_relation_brands u2) x).
  
  Definition typed_binOp τ₁ τ₂ τout := {b:binOp|binOp_type b τ₁ τ₂ τout}.

  Definition tbinop_eq {τ₁ τ₂ τout} (bop1 bop2:typed_binOp τ₁ τ₂ τout) : Prop :=
    forall (x1 x2:data),
      data_type x1 τ₁ -> data_type x2 τ₂ -> 
      (fun_of_binop brand_relation_brands (`bop1)) x1 x2 = (fun_of_binop brand_relation_brands (`bop2)) x1 x2.

  Global Instance tbinop_equiv {τ₁ τ₂ τout} : Equivalence (@tbinop_eq τ₁ τ₂ τout).
  Proof.
    constructor.
    - unfold Reflexive, tbinop_eq.
      intros; reflexivity.
    - unfold Symmetric, tbinop_eq.
      intros; rewrite (H x1 x2); try assumption; reflexivity.
    - unfold Transitive, tbinop_eq.
      intros; rewrite (H x1 x2); try assumption; rewrite (H0 x1 x2); try assumption; reflexivity.
  Qed.

  Definition tbinaryOp_rewrites_to {τ₁ τ₂ τ₃} (b1 b2:binOp) :=
    binOp_type b1 τ₁ τ₂ τ₃ ->
    binOp_type b2 τ₁ τ₂ τ₃ /\
    (forall (x1 x2:data), data_type x1 τ₁ -> data_type x2 τ₂ ->
                          (fun_of_binop brand_relation_brands b1) x1 x2 = (fun_of_binop brand_relation_brands b2) x1 x2).

End TOpsEq.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
