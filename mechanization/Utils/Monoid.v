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

Require Import RelationClasses.
Require Import Morphisms.
Require Import Equivalence.
Require Import Setoid.
Require Import EquivDec.

(** Definition of monoids over collections, loosely based on ideas
    from "Optimizing object queries using an effective
    calculus. Leonidas Fegaras and David Maier. In ACM Transactions on
    Database Systems (TODS) 25.4 (2000): 457-516."

    Some of the type classes structure follow from: "A Gentle
    Introduction to Type Classes and Relations in Coq. Pierre Castéran
    and Matthieu Sozeau" *)

(** #<b>Warning: This module is not used.</b> *)

Section Monoid.

  Local Open Scope equiv_scope.

  Definition associative {A} eqA `{equivA : Equivalence A eqA} (op : A->A->A)
    := forall x₁ x₂ x₃, op (op x₁ x₂) x₃ === op x₁ (op x₂ x₃).

  Definition commutative {A} eqA `{equivA : Equivalence A eqA} (op : binary_operation A)
    := forall x₁ x₂, op x₁ x₂ === op x₂ x₁.

  Definition idempotent {A} eqA `{equivA : Equivalence A eqA} (op : binary_operation A)
    := forall x, op x x === x.

  Definition anti_idempotent {A} eqA `{equivA : Equivalence A eqA} (op : binary_operation A)
    := forall x, not (op x x === x).

  Definition zero_left {A} eqA `{equivA : Equivalence A eqA} (op : binary_operation A) (z : A)
    := forall x, op z x === x.
  
  Definition zero_right {A} eqA `{equivA : Equivalence A eqA} (op : binary_operation A) (z : A)
    := forall x, op x z === x.
  
  Class Monoid (A:Type) (eqA:A->A->Prop) {equivB:Equivalence eqA}
    := {
        merge: A -> A -> A;
        z: A;

        merge_morphism :> Proper (eqA ==> eqA ==> eqA) merge ;
        z_morphism :> Proper (eqA) z;

        merge_assoc: associative eqA merge;
        z_left: zero_left eqA merge z;
        z_right: zero_right eqA merge z
      }.

  Infix "⊕" := merge (at level 70). (* ⊕ = \oplus *)
  Infix "ζ" := z (at level 70).  (* ζ = \zeta *)

  (** A collection monoid. *)

  Class CollMonoid {A U:Type}
        (eqA:A->A->Prop)
        `{monoid:Monoid A eqA}
    := {
        unit: U -> A;
        }.

  (** A commutative monoid. *)

  Class CMonoid {A:Type}
        (eqA:A->A->Prop)
        `{monoid:Monoid A eqA}
    := {
        c_merge_comm: commutative eqA merge
        }.

  (** An idempotent monoid. *)

  Class IMonoid {A:Type}
        (eqA:A->A->Prop)
        `{monoid:Monoid A eqA}
    := {
        i_merge_idem: idempotent eqA merge
        }.

  (** An anti-idempotent monoid. *)

  Class AIMonoid {A:Type}
        (eqA:A->A->Prop)
        `{monoid:Monoid A eqA}
    := {
        ai_merge_anti_idem: anti_idempotent eqA merge
        }.

  (** A commutative & idempotent monoid. *)

  Class CIMonoid {A:Type}
        (eqA:A->A->Prop)
        `{monoid:Monoid A eqA}
    := {
        ci_merge_comm: commutative eqA merge;
        ci_merge_idem: idempotent eqA merge
      }.
  
  (** A commutative & anti-idempotent monoid. *)

  Class CAIMonoid {A:Type}
        (eqA:A->A->Prop)
        `{monoid:Monoid A eqA}
    := {
        cai_merge_comm: commutative eqA merge;
        cai_merge_idem: anti_idempotent eqA merge
      }.

  (* Monoid homomorphisms *)
  (* TBD *)
  
End Monoid.

Infix "⊕" := merge (at level 70). (* ⊕ = \oplus *)
Infix "ζ" := z (at level 70).  (* ζ = \zeta *)

