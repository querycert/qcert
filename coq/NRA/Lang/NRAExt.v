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

Section NRAExt.
  Require Import String List Compare_dec.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.
  Require Import NRA.

  (* Algebra *)

  (* By convention, "static" parameters come first, followed by
     dependent operators. This allows for instanciation on those
     parameters *)

  Context {fruntime:foreign_runtime}.

  (* Joins *)

  Definition join op1 op2 op3 := (ASelect op1 (AProduct op2 op3)).

  Definition semi_join op1 op2 op3 :=
    ASelect (AUnop ANeg (ABinop AEq (ASelect op1 (AProduct ((AUnop AColl) AID) op3)) (AConst (dcoll nil)))) op2.

  Definition anti_join op1 op2 op3 :=
    ASelect (ABinop AEq (ASelect op1 (AProduct ((AUnop AColl) AID) op3)) (AConst (dcoll nil))) op2.

  (* Maps *)

  Definition map_add_rec (s:string) op1 op2 := AMap ((ABinop AConcat) AID ((AUnop (ARec s)) op1)) op2.
  Definition map_to_rec (s:string) op := AMap ((AUnop (ARec s)) AID) op.

  (* Projects *)
  Fixpoint rproject (fields:list string) (op:nra) 
    := match fields with
         | nil => AConst (drec nil)
         | s::xs => ABinop AConcat
                           ((AUnop (ARec s)) ((AUnop (ADot s)) op))
                           (rproject xs op)
       end.

  Definition project (fields:list string) (op:nra) 
    := AMap (rproject fields AID) op.

  Definition project_remove s op :=
    AMap ((AUnop (ARecRemove s)) AID) op.

 (* Renaming *)
  (* renames field s1 to s2 *)
  Definition map_rename_rec (s1 s2:string) op :=
    AMap ((ABinop AConcat) ((AUnop (ARec s2)) ((AUnop (ADot s1)) AID))
                  ((AUnop (ARecRemove s1)) AID)) op.

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
    AMap
      ((ABinop AConcat) ((AUnop (ADot "1")) ((AUnop (ADot "2")) AID))
               ((AUnop (ARec g))
                     (AMap ((AUnop (ADot "3")) AID)
                           (ASelect
                              (ABinop AEq ((AUnop (ADot s1)) ((AUnop (ADot "1")) AID)) ((AUnop (ADot s1)) ((AUnop (ADot "3")) AID)))
                              (AProduct ((AUnop AColl) ((AUnop (ADot "2")) AID))
                                        ((AUnop (ADot "4")) AID))))))
      (AMapConcat
         ((AUnop AColl) ((AUnop (ARec "4")) (AMap ((AUnop (ARec "3")) AID) op)))
         (map_to_rec "2" (map_to_rec "1" ((AUnop ADistinct) (project (s1::nil) op))))).

  (* Unnest *)

  Definition unnest_one s op :=
    AMap ((AUnop (ARecRemove s)) AID) (AMapConcat ((AUnop (ADot s)) AID) op).

  Definition unnest_two s1 s2 op :=
    AMap ((AUnop (ARecRemove s1)) AID) (AMapConcat (AMap ((AUnop (ARec s2)) AID) ((AUnop (ADot s1)) AID)) op).


  (* NRA for Optim *)
  (* A representation for the NRA with additional operators, usually
     helpful when considering optimization *)
  
  Inductive nraext : Set :=
  (* Those correspond to operators in the underlying NRA *)
  | AXID : nraext
  | AXConst : data -> nraext
  | AXBinop : binOp -> nraext -> nraext -> nraext
  | AXUnop : unaryOp -> nraext -> nraext
  | AXMap : nraext -> nraext -> nraext
  | AXMapConcat : nraext -> nraext -> nraext
  | AXProduct : nraext -> nraext -> nraext
  | AXSelect : nraext -> nraext -> nraext
  | AXDefault : nraext -> nraext -> nraext
  | AXEither : nraext -> nraext -> nraext
  | AXEitherConcat : nraext -> nraext -> nraext
  | AXApp : nraext -> nraext -> nraext
  (* Those are additional operators *)
  | AXJoin : nraext -> nraext -> nraext -> nraext
  | AXSemiJoin : nraext -> nraext -> nraext -> nraext
  | AXAntiJoin : nraext -> nraext -> nraext -> nraext
  | AXMapToRec : string -> nraext -> nraext
  | AXMapAddRec : string -> nraext -> nraext -> nraext
  | AXRProject : list string -> nraext -> nraext
  | AXProject : list string -> nraext -> nraext
  | AXProjectRemove : string -> nraext -> nraext
  | AXMapRename : string -> string -> nraext -> nraext
  | AXUnnestOne : string -> nraext -> nraext
  | AXUnnestTwo : string -> string -> nraext -> nraext
  | AXGroupBy : string -> string -> nraext -> nraext
  .

  Global Instance nraext_eqdec : EqDec nraext eq.
  Proof.
    change (forall x y : nraext,  {x = y} + {x <> y}).
    decide equality;
      try solve [apply binOp_eqdec | apply unaryOp_eqdec | apply data_eqdec | apply string_eqdec | apply list_eqdec; apply string_eqdec].
  Qed.

  Fixpoint nra_of_nraext (e:nraext) : nra :=
    match e with
      | AXID => AID
      | AXConst d => AConst d
      | AXBinop b e1 e2 => ABinop b (nra_of_nraext e1) (nra_of_nraext e2)
      | AXUnop u e1 => AUnop u (nra_of_nraext e1)
      | AXMap e1 e2 => AMap (nra_of_nraext e1) (nra_of_nraext e2)
      | AXMapConcat e1 e2 => AMapConcat (nra_of_nraext e1) (nra_of_nraext e2)
      | AXProduct e1 e2 => AProduct (nra_of_nraext e1) (nra_of_nraext e2)
      | AXSelect e1 e2 => ASelect (nra_of_nraext e1) (nra_of_nraext e2)
      | AXDefault e1 e2 => ADefault (nra_of_nraext e1) (nra_of_nraext e2)
      | AXEither opl opr => AEither (nra_of_nraext opl) (nra_of_nraext opr)
      | AXEitherConcat op1 op2 => AEitherConcat (nra_of_nraext op1) (nra_of_nraext op2)
      | AXApp e1 e2 => AApp (nra_of_nraext e1) (nra_of_nraext e2)
      | AXJoin e1 e2 e3 => join (nra_of_nraext e1) (nra_of_nraext e2) (nra_of_nraext e3)
      | AXSemiJoin e1 e2 e3 => semi_join (nra_of_nraext e1) (nra_of_nraext e2) (nra_of_nraext e3)
      | AXAntiJoin e1 e2 e3 => anti_join (nra_of_nraext e1) (nra_of_nraext e2) (nra_of_nraext e3)
      | AXMapToRec s e1 => map_to_rec s (nra_of_nraext e1)
      | AXMapAddRec s e1 e2 => map_add_rec s (nra_of_nraext e1) (nra_of_nraext e2)
      | AXRProject ls e1 => rproject ls (nra_of_nraext e1)
      | AXProject ls e1 => project ls (nra_of_nraext e1)
      | AXProjectRemove s e1 => project_remove s (nra_of_nraext e1)
      | AXMapRename s1 s2 e1 => map_rename_rec s1 s2 (nra_of_nraext e1)
      | AXUnnestOne s1 e1 => unnest_one s1 (nra_of_nraext e1)
      | AXUnnestTwo s1 s2 e1 => unnest_two s1 s2 (nra_of_nraext e1)
      | AXGroupBy s1 s2 e1 => group1 s1 s2 (nra_of_nraext e1)
    end.

  Fixpoint nraext_of_nra (a:nra) : nraext :=
    match a with
      | AID => AXID
      | AConst d => AXConst d
      | ABinop b e1 e2 => AXBinop b (nraext_of_nra e1) (nraext_of_nra e2)
      | AUnop u e1 => AXUnop u (nraext_of_nra e1)
      | AMap e1 e2 => AXMap (nraext_of_nra e1) (nraext_of_nra e2)
      | AMapConcat e1 e2 => AXMapConcat (nraext_of_nra e1) (nraext_of_nra e2)
      | AProduct e1 e2 => AXProduct (nraext_of_nra e1) (nraext_of_nra e2)
      | ASelect e1 e2 => AXSelect (nraext_of_nra e1) (nraext_of_nra e2)
      | ADefault e1 e2 => AXDefault (nraext_of_nra e1) (nraext_of_nra e2)
      | AEither opl opr => AXEither (nraext_of_nra opl) (nraext_of_nra opr)
      | AEitherConcat op1 op2 => AXEitherConcat (nraext_of_nra op1) (nraext_of_nra op2)
      | AApp e1 e2 => AXApp (nraext_of_nra e1) (nraext_of_nra e2)
    end.

  Lemma nraext_roundtrip (a:nra) :
    (nra_of_nraext (nraext_of_nra a)) = a.
  Proof.
    induction a; simpl; try reflexivity; try (rewrite IHa1; rewrite IHa2; try rewrite IHa3; reflexivity).
    rewrite IHa; reflexivity.
  Qed.
    
  Context (h:list(string*string)).
  
  Definition nraext_eval (e:nraext) (x:data) : option data :=
    nra_eval h (nra_of_nraext e) x.

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

Notation "h ⊢ EOp @ₓ x" := (nraext_eval h EOp x) (at level 10): nraext_scope.

Notation "'ID'" := (AXID)  (at level 50) : nraext_scope.                                           (* ◇ = \Diamond *)

Notation "‵‵ c" := (AXConst (dconst c))  (at level 0) : nraext_scope.                           (* ‵ = \backprime *)
Notation "‵ c" := (AXConst c)  (at level 0) : nraext_scope.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (AXConst (dcoll nil))  (at level 0) : nraext_scope.                         (* ‵ = \backprime *)
Notation "‵[||]" := (AXConst (drec nil)) (at level 50) : nraext_scope.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (AXBinop AAnd r1 r2) (right associativity, at level 65): nraext_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (AXBinop AOr r1 r2) (right associativity, at level 70): nraext_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (AXBinop AEq r1 r2) (right associativity, at level 70): nraext_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (AXBinop ALt r1 r2) (no associativity, at level 70): nraext_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (AXBinop AUnion r1 r2) (right associativity, at level 70): nraext_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (AXBinop AMinus r1 r2) (right associativity, at level 70): nraext_scope.  (* − = \minus *)
Notation "r1 ♯min r2" := (AXBinop AMin r1 r2) (right associativity, at level 70): nraext_scope. (* ♯ = \sharp *)
Notation "r1 ♯max r2" := (AXBinop AMax r1 r2) (right associativity, at level 70): nraext_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((AXBinop AConcat) p r) (at level 70) : nraext_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((AXBinop AMergeConcat) p r) (at level 70) : nraext_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (AXUnop ANeg r1) (right associativity, at level 70): nraext_scope.        (* ¬ = \neg *)
Notation "ε( r1 )" := (AXUnop ADistinct r1) (right associativity, at level 70): nraext_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (AXUnop ACount r1) (right associativity, at level 70): nraext_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (AXUnop AFlatten d) (at level 50) : nraext_scope.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((AXUnop AColl) d)  (at level 50) : nraext_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((AXUnop (ARec s)) r) (at level 50) : nraext_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((AXUnop (ARecRemove s1)) r) (at level 50) : nraext_scope.          (* ¬ = \neg and π = \pi *)
Notation "p · r" := ((AXUnop (ADot r)) p) (left associativity, at level 40): nraext_scope.      (* · = \cdot *)

Notation "χ⟨ p ⟩( r )" := (AXMap p r) (at level 70) : nraext_scope.                              (* χ = \chi *)
Notation "⋈ᵈ⟨ e2 ⟩( e1 )" := (AXMapConcat e2 e1) (at level 70) : nraext_scope.                   (* ⟨ ... ⟩ = \rangle ...  \langle *)
Notation "r1 × r2" := (AXProduct r1 r2) (right associativity, at level 70): nraext_scope.       (* × = \times *)
Notation "σ⟨ p ⟩( r )" := (AXSelect p r) (at level 70) : nraext_scope.                           (* σ = \sigma *)
Notation "r1 ∥ r2" := (AXDefault r1 r2) (right associativity, at level 70): nraext_scope.       (* ∥ = \parallel *)
Notation "r1 ◯ r2" := (AXApp r1 r2) (right associativity, at level 60): nraext_scope.           (* ◯ = \bigcirc *)

(* Operators only in the extended nraebra *)
Notation "⋈⟨ p ⟩( r1 , r2 )" := (AXJoin p r1 r2) (at level 70) : nraext_scope.                     (* ⋈ = \Join *)
Notation "⋉⟨ p ⟩( r1 , r2 )" := (AXSemiJoin p r1 r2) (at level 70) : nraext_scope.                (* ⋉ = \ltimes *)
Notation "▷⟨ p ⟩( r1 , r2 )" := (AXAntiJoin p r1 r2) (at level 70) : nraext_scope.                (* ▷ = \rhd *)

Notation "p ⌈ a ⌋" := (AXMapToRec a p) (at level 70) : nraext_scope.
Notation "χ⌈ a ⌋⟨ p1 ⟩( p2 )" := (AXMapAddRec a p1 p2) (at level 70) : nraext_scope.

(*
Notation "π[  ]( r )" := (AXRProject nil r) (at level 70) : nraext_scope.
Notation "π[ x ]( r )" := (AXRProject (cons x nil) r) (at level 70) : nraext_scope.
Notation "π[ x , .. , y ]( r )" := (AXRProject (cons x .. (cons y nil) ..) r) (at level 70) : nraext_scope.
*)
Notation "Π[ ]( r )" := (AXProject nil r) (at level 70) : nraext_scope.
Notation "Π[ x ]( r )" := (AXProject (cons x nil) r) (at level 70) : nraext_scope.
Notation "Π[ x , .. , y ]( r )" := (AXProject (cons x .. (cons y nil) ..) r) (at level 70) : nraext_scope.

Notation "¬Π[ s1 ]( r )" := (AXProjectRemove s1 r) (at level 70) : nraext_scope.

Notation "ρ[ s1 ↦ s2 ]( r )" := (AXMapRename s1 s2 r) (at level 70) : nraext_scope.

Notation "μ[ s1 ]( r )" := (AXUnnestOne s1 r) (at level 70) : nraext_scope.
Notation "μ[ s1 ][ s2 ]( r )" := (AXUnnestTwo s1 s2 r) (at level 70) : nraext_scope.

Notation "Γ[ g ][ s1 ]( r )" := (AXGroupBy g s1 r) (at level 70) : nraext_scope.

(* end hide *)

Local Open Scope string_scope.
Tactic Notation "nraext_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "AXID"
  | Case_aux c "AXConst"
  | Case_aux c "AXBinop"
  | Case_aux c "AXUnop"
  | Case_aux c "AXMap"
  | Case_aux c "AXMapConcat"
  | Case_aux c "AXProduct"
  | Case_aux c "AXSelect"
  | Case_aux c "AXDefault"
  | Case_aux c "AXEither"
  | Case_aux c "AXEitherConcat"
  | Case_aux c "AXApp"
  | Case_aux c "AXJoin"
  | Case_aux c "AXSemiJoin"
  | Case_aux c "AXAntiJoin"
  | Case_aux c "AXMapToRec"
  | Case_aux c "AXRProject"
  | Case_aux c "AXProject"
  | Case_aux c "AXProjectRemove"
  | Case_aux c "AXMapRename"
  | Case_aux c "AXUnnestOne"
  | Case_aux c "AXUnnestTwo"
  | Case_aux c "AXGroupBy" ].

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
