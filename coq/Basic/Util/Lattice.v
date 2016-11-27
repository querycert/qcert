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
Require Import EquivDec.

Section Lattice.

  (** Definition of a lattice, loosely based on ideas from 
   "A reflection-based proof tactic for lattices in Coq" and 
   http://www.pps.univ-paris-diderot.fr/~sozeau/repos/coq/order/
   *)
  Definition part_le {A} {eqA} {R} `{part:PartialOrder A eqA R} : _ := R.
  Infix "≤" := part_le (at level 70, no associativity).

  Definition associative {A} eqA `{equivA : Equivalence A eqA} (op : A->A-> A)
    := forall x₁ x₂ x₃, equiv (op (op x₁ x₂) x₃) (op x₁ (op x₂ x₃)).

  Definition commutative {A} eqA `{equivA : Equivalence A eqA} (op : A->A->A)
    := forall x₁ x₂, equiv (op x₁ x₂) (op x₂ x₁).

  Definition idempotent {A} eqA `{equivA : Equivalence A eqA} (op : A->A->A)
    := forall x, equiv (op x x) x.

  Definition absorptive {A} eqA `{equivA : Equivalence A eqA}
             (op1 op2 : A->A->A)
    := forall x y, op1 x (op2 x y) === x.
  
  Class Lattice (A:Type) (eqA:A->A->Prop) {equivA:Equivalence eqA}
    := {
        meet : A -> A -> A;
        join : A -> A -> A;

        meet_morphism :> Proper (eqA ==> eqA ==> eqA) meet ;
        join_morphism :> Proper (eqA ==> eqA ==> eqA) join ;
        
        meet_commutative : commutative eqA meet;
        meet_associative    : associative eqA meet;
        meet_idempotent   : idempotent eqA meet;

        join_commutative : commutative eqA join;
        join_associative    : associative eqA join;
        join_idempotent   : idempotent eqA join;

        meet_absorptive : absorptive eqA meet join;
        join_absorptive   : absorptive eqA join meet
      }.

  Infix "⊓" := meet (at level 70). (* ⊓ = \sqcap *)
  Infix "⊔" := join (at level 70). (* ⊔ = \sqcup *)

  (** A lattice that is consistent with a specified partial order. *)

  Class OLattice {A:Type}
        (eqA:A->A->Prop)
        (ordA:A->A->Prop)
        {equivA:Equivalence eqA}
        {lattice:Lattice A eqA}
        {pre:PreOrder ordA}
        {po:PartialOrder eqA ordA}
    := {
        consistent_meet: forall a b, a ≤ b <-> a ⊓ b === a
        }.

  Section props.
    Context {A eqA ordA} `{olattice:OLattice A eqA ordA}.

    Lemma consistent_join 
    : forall a b, a ≤ b <-> a ⊔ b === b.
  Proof.
    intros.
    rewrite consistent_meet.
    split; intros eqq.
    - rewrite <- eqq.
      rewrite join_commutative, meet_commutative.
      rewrite (join_absorptive b a).
      reflexivity.
    - rewrite <- eqq.
      rewrite (meet_absorptive a b).
      reflexivity.
  Qed.

  Lemma meet_leq_l a b: (a ⊓ b) ≤ a.
  Proof.
    rewrite consistent_meet.
    rewrite meet_commutative.
    rewrite <- meet_associative, meet_idempotent.
    reflexivity.
  Qed.

  Lemma  meet_leq_r a b: (a ⊓ b) ≤ b.
  Proof.    
    rewrite meet_commutative.
    apply meet_leq_l.
  Qed.

  Theorem meet_most {a b c} : a ≤ b -> a ≤ c -> a ≤ (b ⊓ c).
  Proof.
    intros sub1 sub2.
    rewrite consistent_meet in sub1,sub2.
    rewrite <- sub1, <- sub2.
    rewrite meet_associative.
    rewrite (meet_commutative c b).
    apply meet_leq_r.
  Qed.

  Lemma join_leq_l a b: a ≤ (a ⊔ b).
  Proof.
    rewrite consistent_join.
    rewrite <- join_associative, join_idempotent.
    reflexivity.
  Qed.

  Lemma join_leq_r a b: b ≤ (a ⊔ b).
  Proof.    
    rewrite join_commutative.
    apply join_leq_l.
  Qed.

  Theorem join_least {a b c} : a ≤ c -> b ≤ c -> (a ⊔ b) ≤ c.
  Proof.
    intros sub1 sub2.
    rewrite consistent_join in sub1,sub2.
    rewrite consistent_join.
    rewrite join_associative.
    rewrite sub2, sub1.
    reflexivity.
  Qed.

    Global Instance meet_leq_proper :
    Proper (part_le ==> part_le ==> part_le) meet.
  Proof.
    unfold Proper, respectful.
    intros a1 a2 aleq b1 b2 bleq.
    rewrite consistent_meet in aleq, bleq |- *.
    rewrite meet_associative.
    rewrite (meet_commutative a2 b2).
    rewrite <- (meet_associative b1 b2 a2).
    rewrite bleq.
    rewrite (meet_commutative b1 a2).
    rewrite <- meet_associative.
    rewrite aleq.
    reflexivity.
  Qed.

  Global Instance join_leq_proper :
    Proper (part_le ==> part_le ==> part_le) join.
  Proof.
    unfold Proper, respectful.
    intros a1 a2 aleq b1 b2 bleq.
    rewrite consistent_join in aleq, bleq |- *.
    rewrite join_associative.
    rewrite (join_commutative a2 b2).
    rewrite <- (join_associative b1 b2 a2).
    rewrite bleq.
    rewrite (join_commutative b2 a2).
    rewrite <- join_associative.
    rewrite aleq.
    reflexivity.
  Qed.


  (* If the equivalence relation is decidable, 
     then we can decide the leq relation using either meet or join 
 *)
  Lemma leq_dec_meet `{dec:EqDec A eqA} a b : {a ≤ b} + {~ a ≤ b}.
  Proof.
    generalize (consistent_meet a b).
    destruct (meet a b == a); unfold equiv, complement in *; intuition.
  Defined.

  Lemma leq_dec_join `{dec:EqDec A eqA} a b : {a ≤ b} + {~ a ≤ b}.
  Proof.
    generalize (consistent_join a b).
    destruct (join a b == b); unfold equiv, complement in *; intuition.
  Defined.

  End props.
  
End Lattice.

Infix "≤" := part_le (at level 70, no associativity).
Infix "⊓" := meet (at level 70). (* ⊓ = \sqcap *)
Infix "⊔" := join (at level 70). (* ⊔ = \sqcup *)


(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
