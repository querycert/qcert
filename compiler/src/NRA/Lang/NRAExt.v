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

(** This module is not in use, but is kept around as a referent to
some of the additional operators commonly found in the nested
relational algebra. *)

Require Import String.
Require Import List.
Require Import Compare_dec.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.
Require Import NRA.

Section NRAExt.
  (* Algebra *)

  (* By convention, "static" parameters come first, followed by
     dependent operators. This allows for instanciation on those
     parameters *)

  Context {fruntime:foreign_runtime}.

  (* Joins *)

  Definition join op1 op2 op3 := (NRASelect op1 (NRAProduct op2 op3)).

  Definition semi_join op1 op2 op3 :=
    NRASelect (NRAUnop OpNeg (NRABinop OpEqual
                                       (NRASelect op1 (NRAProduct ((NRAUnop OpBag) NRAID) op3))
                                       (NRAConst (dcoll nil)))) op2.
  Definition anti_join op1 op2 op3 :=
    NRASelect (NRABinop OpEqual
                        (NRASelect op1 (NRAProduct ((NRAUnop OpBag) NRAID) op3))
                        (NRAConst (dcoll nil))) op2.

  (* Maps *)

  Definition map_add_rec (s:string) op1 op2 :=
    NRAMap ((NRABinop OpRecConcat) NRAID ((NRAUnop (OpRec s)) op1)) op2.
  Definition map_to_rec (s:string) op :=
    NRAMap ((NRAUnop (OpRec s)) NRAID) op.

  (* Projects *)
  Fixpoint rproject (fields:list string) (op:nra) 
    := match fields with
         | nil => NRAConst (drec nil)
         | s::xs => NRABinop OpRecConcat
                             ((NRAUnop (OpRec s)) ((NRAUnop (OpDot s)) op))
                             (rproject xs op)
       end.

  Definition project (fields:list string) (op:nra)  :=
    NRAMap (rproject fields NRAID) op.

  Definition project_remove s op :=
    NRAMap ((NRAUnop (OpRecRemove s)) NRAID) op.

 (* Renaming *)
  (* renames field s1 to s2 *)
  Definition map_rename_rec (s1 s2:string) op :=
    NRAMap ((NRABinop OpRecConcat) ((NRAUnop (OpRec s2)) ((NRAUnop (OpDot s1)) NRAID))
                                   ((NRAUnop (OpRecRemove s1)) NRAID)) op.

  (* Grouping *)

  (* Tricky -- you need to do two passes, and compare elements with
     the same set of attribute names which means you need to
     encapsulate each branch with distinct record names... This is not
     so great. *)

  (*
    group1 g s1 [{s1->1,r_1}, {s1->2,r_2}, {s1->1,r_3}] 
  = [{s1->1,g->[{s1->1,r_1}, {s1->1,r_3}]}, {s1->2, g->[{s1->2,r_2}]}]
  *)

  Import ListNotations.
  Definition group1 (g:string) (s1:string) op :=
    NRAMap
      ((NRABinop OpRecConcat) ((NRAUnop (OpDot "1")) ((NRAUnop (OpDot "2")) NRAID))
                              ((NRAUnop (OpRec g))
                                 (NRAMap ((NRAUnop (OpDot "3")) NRAID)
                                         (NRASelect
                                            (NRABinop OpEqual ((NRAUnop (OpDot s1)) ((NRAUnop (OpDot "1")) NRAID)) ((NRAUnop (OpDot s1)) ((NRAUnop (OpDot "3")) NRAID)))
                                            (NRAProduct ((NRAUnop OpBag) ((NRAUnop (OpDot "2")) NRAID))
                                                        ((NRAUnop (OpDot "4")) NRAID))))))
      (NRAMapProduct
         ((NRAUnop OpBag) ((NRAUnop (OpRec "4")) (NRAMap ((NRAUnop (OpRec "3")) NRAID) op)))
         (map_to_rec "2" (map_to_rec "1" ((NRAUnop OpDistinct) (project (s1::nil) op))))).

  (* Unnest *)

  Definition unnest_one s op :=
    NRAMap ((NRAUnop (OpRecRemove s)) NRAID) (NRAMapProduct ((NRAUnop (OpDot s)) NRAID) op).

  Definition unnest_two s1 s2 op :=
    NRAMap ((NRAUnop (OpRecRemove s1)) NRAID)
           (NRAMapProduct (NRAMap ((NRAUnop (OpRec s2)) NRAID)
                                  ((NRAUnop (OpDot s1)) NRAID)) op).


  (* NRA for Optim *)
  (* A representation for the NRA with additional operators, usually
     helpful when considering optimization *)
  
  Inductive nraext : Set :=
  (* Those correspond to operators in the underlying NRA *)
  | xNRAID : nraext
  | xNRAConst : data -> nraext
  | xNRABinop : binary_op -> nraext -> nraext -> nraext
  | xNRAUnop : unary_op -> nraext -> nraext
  | xNRAMap : nraext -> nraext -> nraext
  | xNRAMapProduct : nraext -> nraext -> nraext
  | xNRAProduct : nraext -> nraext -> nraext
  | xNRASelect : nraext -> nraext -> nraext
  | xNRADefault : nraext -> nraext -> nraext
  | xNRAEither : nraext -> nraext -> nraext
  | xNRAEitherConcat : nraext -> nraext -> nraext
  | xNRAApp : nraext -> nraext -> nraext
  | xNRAGetConstant : string -> nraext
  (* Those are additional operators *)
  | xNRAJoin : nraext -> nraext -> nraext -> nraext
  | xNRASemiJoin : nraext -> nraext -> nraext -> nraext
  | xNRAAntiJoin : nraext -> nraext -> nraext -> nraext
  | xNRAMapToRec : string -> nraext -> nraext
  | xNRAMapAddRec : string -> nraext -> nraext -> nraext
  | xNRARProject : list string -> nraext -> nraext
  | xNRAProject : list string -> nraext -> nraext
  | xNRAProjectRemove : string -> nraext -> nraext
  | xNRAMapRename : string -> string -> nraext -> nraext
  | xNRAUnnestOne : string -> nraext -> nraext
  | xNRAUnnestTwo : string -> string -> nraext -> nraext
  | xNRAGroupBy : string -> string -> nraext -> nraext
  .

  Global Instance nraext_eqdec : EqDec nraext eq.
  Proof.
    change (forall x y : nraext,  {x = y} + {x <> y}).
    decide equality;
      try solve [apply binary_op_eqdec | apply unary_op_eqdec | apply data_eqdec | apply string_eqdec | apply list_eqdec; apply string_eqdec].
  Qed.

  Fixpoint nra_of_nraext (e:nraext) : nra :=
    match e with
      | xNRAID => NRAID
      | xNRAConst d => NRAConst d
      | xNRABinop b e1 e2 => NRABinop b (nra_of_nraext e1) (nra_of_nraext e2)
      | xNRAUnop u e1 => NRAUnop u (nra_of_nraext e1)
      | xNRAMap e1 e2 => NRAMap (nra_of_nraext e1) (nra_of_nraext e2)
      | xNRAMapProduct e1 e2 => NRAMapProduct (nra_of_nraext e1) (nra_of_nraext e2)
      | xNRAProduct e1 e2 => NRAProduct (nra_of_nraext e1) (nra_of_nraext e2)
      | xNRASelect e1 e2 => NRASelect (nra_of_nraext e1) (nra_of_nraext e2)
      | xNRADefault e1 e2 => NRADefault (nra_of_nraext e1) (nra_of_nraext e2)
      | xNRAEither opl opr => NRAEither (nra_of_nraext opl) (nra_of_nraext opr)
      | xNRAEitherConcat op1 op2 => NRAEitherConcat (nra_of_nraext op1) (nra_of_nraext op2)
      | xNRAApp e1 e2 => NRAApp (nra_of_nraext e1) (nra_of_nraext e2)
      | xNRAGetConstant s => NRAGetConstant s
      | xNRAJoin e1 e2 e3 => join (nra_of_nraext e1) (nra_of_nraext e2) (nra_of_nraext e3)
      | xNRASemiJoin e1 e2 e3 => semi_join (nra_of_nraext e1) (nra_of_nraext e2) (nra_of_nraext e3)
      | xNRAAntiJoin e1 e2 e3 => anti_join (nra_of_nraext e1) (nra_of_nraext e2) (nra_of_nraext e3)
      | xNRAMapToRec s e1 => map_to_rec s (nra_of_nraext e1)
      | xNRAMapAddRec s e1 e2 => map_add_rec s (nra_of_nraext e1) (nra_of_nraext e2)
      | xNRARProject ls e1 => rproject ls (nra_of_nraext e1)
      | xNRAProject ls e1 => project ls (nra_of_nraext e1)
      | xNRAProjectRemove s e1 => project_remove s (nra_of_nraext e1)
      | xNRAMapRename s1 s2 e1 => map_rename_rec s1 s2 (nra_of_nraext e1)
      | xNRAUnnestOne s1 e1 => unnest_one s1 (nra_of_nraext e1)
      | xNRAUnnestTwo s1 s2 e1 => unnest_two s1 s2 (nra_of_nraext e1)
      | xNRAGroupBy s1 s2 e1 => group1 s1 s2 (nra_of_nraext e1)
    end.

  Fixpoint nraext_of_nra (a:nra) : nraext :=
    match a with
    | NRAGetConstant s => xNRAGetConstant s
    | NRAID => xNRAID
    | NRAConst d => xNRAConst d
    | NRABinop b e1 e2 => xNRABinop b (nraext_of_nra e1) (nraext_of_nra e2)
    | NRAUnop u e1 => xNRAUnop u (nraext_of_nra e1)
    | NRAMap e1 e2 => xNRAMap (nraext_of_nra e1) (nraext_of_nra e2)
    | NRAMapProduct e1 e2 => xNRAMapProduct (nraext_of_nra e1) (nraext_of_nra e2)
    | NRAProduct e1 e2 => xNRAProduct (nraext_of_nra e1) (nraext_of_nra e2)
    | NRASelect e1 e2 => xNRASelect (nraext_of_nra e1) (nraext_of_nra e2)
    | NRADefault e1 e2 => xNRADefault (nraext_of_nra e1) (nraext_of_nra e2)
    | NRAEither opl opr => xNRAEither (nraext_of_nra opl) (nraext_of_nra opr)
    | NRAEitherConcat op1 op2 => xNRAEitherConcat (nraext_of_nra op1) (nraext_of_nra op2)
    | NRAApp e1 e2 => xNRAApp (nraext_of_nra e1) (nraext_of_nra e2)
    end.

  Lemma nraext_roundtrip (a:nra) :
    (nra_of_nraext (nraext_of_nra a)) = a.
  Proof.
    induction a; simpl; try reflexivity; try (rewrite IHa1; rewrite IHa2; try rewrite IHa3; reflexivity).
    rewrite IHa; reflexivity.
  Qed.
    
  Context (h:list(string*string)).
  
  Definition nraext_eval c (e:nraext) (x:data) : option data :=
    nra_eval h c (nra_of_nraext e) x.

  (** Nraebraic plan application *)

End NRAExt.

(* As much as possible, notations are aligned with those of [CM93]
   S. Cluet and G. Moerkotte. Nested queries in object bases. In
   Proc. Int.  Workshop on Database Programming Languages , pages
   226-242, 1993.

   See also chapter 7.2 in:
   http://pi3.informatik.uni-mannheim.de/~moer/querycompiler.pdf
 *)

(* begin hide *)
Delimit Scope nraext_scope with nraext.

Notation "h ⊢ EOp @ₓ x ⊣ c" := (nraext_eval h c EOp x) (at level 10): nraext_scope.

Notation "'ID'" := (xNRAID)  (at level 50) : nraext_scope.                                           (* ◇ = \Diamond *)
Notation "CGET⟨ s ⟩" := (xNRAGetConstant s) (at level 50) : nraext_core_scope.

Notation "‵‵ c" := (xNRAConst (dconst c))  (at level 0) : nraext_scope.                           (* ‵ = \backprime *)
Notation "‵ c" := (xNRAConst c)  (at level 0) : nraext_scope.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (xNRAConst (dcoll nil))  (at level 0) : nraext_scope.                         (* ‵ = \backprime *)
Notation "‵[||]" := (xNRAConst (drec nil)) (at level 50) : nraext_scope.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (xNRABinop OpAnd r1 r2) (right associativity, at level 65): nraext_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (xNRABinop OpOr r1 r2) (right associativity, at level 70): nraext_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (xNRABinop OpEqual r1 r2) (right associativity, at level 70): nraext_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (xNRABinop OpLt r1 r2) (no associativity, at level 70): nraext_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (xNRABinop OpBagUnion r1 r2) (right associativity, at level 70): nraext_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (xNRABinop OpBagDiff r1 r2) (right associativity, at level 70): nraext_scope.  (* − = \minus *)
Notation "r1 ♯min r2" := (xNRABinop OpBagMin r1 r2) (right associativity, at level 70): nraext_scope. (* ♯ = \sharp *)
Notation "r1 ♯max r2" := (xNRABinop OpBagMax r1 r2) (right associativity, at level 70): nraext_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((xNRABinop OpRecConcat) p r) (at level 70) : nraext_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((xNRABinop OpRecMerge) p r) (at level 70) : nraext_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (xNRAUnop OpNeg r1) (right associativity, at level 70): nraext_scope.        (* ¬ = \neg *)
Notation "ε( r1 )" := (xNRAUnop OpDistinct r1) (right associativity, at level 70): nraext_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (xNRAUnop OpCount r1) (right associativity, at level 70): nraext_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (xNRAUnop OpFlatten d) (at level 50) : nraext_scope.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((xNRAUnop OpBag) d)  (at level 50) : nraext_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((xNRAUnop (OpRec s)) r) (at level 50) : nraext_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((xNRAUnop (OpRecRemove s1)) r) (at level 50) : nraext_scope.          (* ¬ = \neg and π = \pi *)
Notation "p · r" := ((xNRAUnop (OpDot r)) p) (left associativity, at level 40): nraext_scope.      (* · = \cdot *)

Notation "χ⟨ p ⟩( r )" := (xNRAMap p r) (at level 70) : nraext_scope.                              (* χ = \chi *)
Notation "⋈ᵈ⟨ e2 ⟩( e1 )" := (xNRAMapProduct e2 e1) (at level 70) : nraext_scope.                   (* ⟨ ... ⟩ = \rangle ...  \langle *)
Notation "r1 × r2" := (xNRAProduct r1 r2) (right associativity, at level 70): nraext_scope.       (* × = \times *)
Notation "σ⟨ p ⟩( r )" := (xNRASelect p r) (at level 70) : nraext_scope.                           (* σ = \sigma *)
Notation "r1 ∥ r2" := (xNRADefault r1 r2) (right associativity, at level 70): nraext_scope.       (* ∥ = \parallel *)
Notation "r1 ◯ r2" := (xNRAApp r1 r2) (right associativity, at level 60): nraext_scope.           (* ◯ = \bigcirc *)

(* Operators only in the extended nraebra *)
Notation "⋈⟨ p ⟩( r1 , r2 )" := (xNRAJoin p r1 r2) (at level 70) : nraext_scope.                     (* ⋈ = \Join *)
Notation "⋉⟨ p ⟩( r1 , r2 )" := (xNRASemiJoin p r1 r2) (at level 70) : nraext_scope.                (* ⋉ = \ltimes *)
Notation "▷⟨ p ⟩( r1 , r2 )" := (xNRAAntiJoin p r1 r2) (at level 70) : nraext_scope.                (* ▷ = \rhd *)

Notation "p ⌈ a ⌋" := (xNRAMapToRec a p) (at level 70) : nraext_scope.
Notation "χ⌈ a ⌋⟨ p1 ⟩( p2 )" := (xNRAMapAddRec a p1 p2) (at level 70) : nraext_scope.

(*
Notation "π[  ]( r )" := (xNRARProject nil r) (at level 70) : nraext_scope.
Notation "π[ x ]( r )" := (xNRARProject (cons x nil) r) (at level 70) : nraext_scope.
Notation "π[ x , .. , y ]( r )" := (xNRARProject (cons x .. (cons y nil) ..) r) (at level 70) : nraext_scope.
*)
Notation "Π[ ]( r )" := (xNRAProject nil r) (at level 70) : nraext_scope.
Notation "Π[ x ]( r )" := (xNRAProject (cons x nil) r) (at level 70) : nraext_scope.
Notation "Π[ x , .. , y ]( r )" := (xNRAProject (cons x .. (cons y nil) ..) r) (at level 70) : nraext_scope.

Notation "¬Π[ s1 ]( r )" := (xNRAProjectRemove s1 r) (at level 70) : nraext_scope.

Notation "ρ[ s1 ↦ s2 ]( r )" := (xNRAMapRename s1 s2 r) (at level 70) : nraext_scope.

Notation "μ[ s1 ]( r )" := (xNRAUnnestOne s1 r) (at level 70) : nraext_scope.
Notation "μ[ s1 ][ s2 ]( r )" := (xNRAUnnestTwo s1 s2 r) (at level 70) : nraext_scope.

Notation "Γ[ g ][ s1 ]( r )" := (xNRAGroupBy g s1 r) (at level 70) : nraext_scope.

(* end hide *)

Local Open Scope string_scope.
Tactic Notation "nraext_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "xNRAID"
  | Case_aux c "xNRAConst"
  | Case_aux c "xNRABinop"
  | Case_aux c "xNRAUnop"
  | Case_aux c "xNRAMap"
  | Case_aux c "xNRAMapProduct"
  | Case_aux c "xNRAProduct"
  | Case_aux c "xNRASelect"
  | Case_aux c "xNRADefault"
  | Case_aux c "xNRAEither"
  | Case_aux c "xNRAEitherConcat"
  | Case_aux c "xNRAApp"
  | Case_aux c "xNRAGetConstant"
  | Case_aux c "xNRAJoin"
  | Case_aux c "xNRASemiJoin"
  | Case_aux c "xNRAAntiJoin"
  | Case_aux c "xNRAMapToRec"
  | Case_aux c "xNRARProject"
  | Case_aux c "xNRAProject"
  | Case_aux c "xNRAProjectRemove"
  | Case_aux c "xNRAMapRename"
  | Case_aux c "xNRAUnnestOne"
  | Case_aux c "xNRAUnnestTwo"
  | Case_aux c "xNRAGroupBy" ].

