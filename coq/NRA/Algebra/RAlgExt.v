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

Section RAlgExt.
  Require Import String List Compare_dec.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.
  Require Import RAlg.

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
  Fixpoint rproject (fields:list string) (op:alg) 
    := match fields with
         | nil => AConst (drec nil)
         | s::xs => ABinop AConcat
                           ((AUnop (ARec s)) ((AUnop (ADot s)) op))
                           (rproject xs op)
       end.

  Definition project (fields:list string) (op:alg) 
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
  
  Inductive algext : Set :=
  (* Those correspond to operators in the underlying NRA *)
  | AXID : algext
  | AXConst : data -> algext
  | AXBinop : binOp -> algext -> algext -> algext
  | AXUnop : unaryOp -> algext -> algext
  | AXMap : algext -> algext -> algext
  | AXMapConcat : algext -> algext -> algext
  | AXProduct : algext -> algext -> algext
  | AXSelect : algext -> algext -> algext
  | AXDefault : algext -> algext -> algext
  | AXEither : algext -> algext -> algext
  | AXEitherConcat : algext -> algext -> algext
  | AXApp : algext -> algext -> algext
  (* Those are additional operators *)
  | AXJoin : algext -> algext -> algext -> algext
  | AXSemiJoin : algext -> algext -> algext -> algext
  | AXAntiJoin : algext -> algext -> algext -> algext
  | AXMapToRec : string -> algext -> algext
  | AXMapAddRec : string -> algext -> algext -> algext
  | AXRProject : list string -> algext -> algext
  | AXProject : list string -> algext -> algext
  | AXProjectRemove : string -> algext -> algext
  | AXMapRename : string -> string -> algext -> algext
  | AXUnnestOne : string -> algext -> algext
  | AXUnnestTwo : string -> string -> algext -> algext
  | AXGroupBy : string -> string -> algext -> algext
  .

  Global Instance algext_eqdec : EqDec algext eq.
  Proof.
    change (forall x y : algext,  {x = y} + {x <> y}).
    decide equality;
      try solve [apply binOp_eqdec | apply unaryOp_eqdec | apply data_eqdec | apply string_eqdec | apply list_eqdec; apply string_eqdec].
  Qed.

  Fixpoint alg_of_algext (e:algext) : alg :=
    match e with
      | AXID => AID
      | AXConst d => AConst d
      | AXBinop b e1 e2 => ABinop b (alg_of_algext e1) (alg_of_algext e2)
      | AXUnop u e1 => AUnop u (alg_of_algext e1)
      | AXMap e1 e2 => AMap (alg_of_algext e1) (alg_of_algext e2)
      | AXMapConcat e1 e2 => AMapConcat (alg_of_algext e1) (alg_of_algext e2)
      | AXProduct e1 e2 => AProduct (alg_of_algext e1) (alg_of_algext e2)
      | AXSelect e1 e2 => ASelect (alg_of_algext e1) (alg_of_algext e2)
      | AXDefault e1 e2 => ADefault (alg_of_algext e1) (alg_of_algext e2)
      | AXEither opl opr => AEither (alg_of_algext opl) (alg_of_algext opr)
      | AXEitherConcat op1 op2 => AEitherConcat (alg_of_algext op1) (alg_of_algext op2)
      | AXApp e1 e2 => AApp (alg_of_algext e1) (alg_of_algext e2)
      | AXJoin e1 e2 e3 => join (alg_of_algext e1) (alg_of_algext e2) (alg_of_algext e3)
      | AXSemiJoin e1 e2 e3 => semi_join (alg_of_algext e1) (alg_of_algext e2) (alg_of_algext e3)
      | AXAntiJoin e1 e2 e3 => anti_join (alg_of_algext e1) (alg_of_algext e2) (alg_of_algext e3)
      | AXMapToRec s e1 => map_to_rec s (alg_of_algext e1)
      | AXMapAddRec s e1 e2 => map_add_rec s (alg_of_algext e1) (alg_of_algext e2)
      | AXRProject ls e1 => rproject ls (alg_of_algext e1)
      | AXProject ls e1 => project ls (alg_of_algext e1)
      | AXProjectRemove s e1 => project_remove s (alg_of_algext e1)
      | AXMapRename s1 s2 e1 => map_rename_rec s1 s2 (alg_of_algext e1)
      | AXUnnestOne s1 e1 => unnest_one s1 (alg_of_algext e1)
      | AXUnnestTwo s1 s2 e1 => unnest_two s1 s2 (alg_of_algext e1)
      | AXGroupBy s1 s2 e1 => group1 s1 s2 (alg_of_algext e1)
    end.

  Fixpoint algext_of_alg (a:alg) : algext :=
    match a with
      | AID => AXID
      | AConst d => AXConst d
      | ABinop b e1 e2 => AXBinop b (algext_of_alg e1) (algext_of_alg e2)
      | AUnop u e1 => AXUnop u (algext_of_alg e1)
      | AMap e1 e2 => AXMap (algext_of_alg e1) (algext_of_alg e2)
      | AMapConcat e1 e2 => AXMapConcat (algext_of_alg e1) (algext_of_alg e2)
      | AProduct e1 e2 => AXProduct (algext_of_alg e1) (algext_of_alg e2)
      | ASelect e1 e2 => AXSelect (algext_of_alg e1) (algext_of_alg e2)
      | ADefault e1 e2 => AXDefault (algext_of_alg e1) (algext_of_alg e2)
      | AEither opl opr => AXEither (algext_of_alg opl) (algext_of_alg opr)
      | AEitherConcat op1 op2 => AXEitherConcat (algext_of_alg op1) (algext_of_alg op2)
      | AApp e1 e2 => AXApp (algext_of_alg e1) (algext_of_alg e2)
    end.

  Lemma algext_roundtrip (a:alg) :
    (alg_of_algext (algext_of_alg a)) = a.
  Proof.
    induction a; simpl; try reflexivity; try (rewrite IHa1; rewrite IHa2; try rewrite IHa3; reflexivity).
    rewrite IHa; reflexivity.
  Qed.
    
  Context (h:list(string*string)).
  
  Definition fun_of_algext (e:algext) (x:data) : option data :=
    fun_of_alg h (alg_of_algext e) x.

  (** Algebraic plan application *)

End RAlgExt.

(* As much as possible, notations are aligned with those of [CM93]
   S. Cluet and G. Moerkotte. Nested queries in object bases. In
   Proc. Int.  Workshop on Database Programming Languages , pages
   226-242, 1993.

   See also chapter 7.2 in:
   http://pi3.informatik.uni-mannheim.de/~moer/querycompiler.pdf
 *)

(* begin hide *)
Delimit Scope algext_scope with algext.

Notation "h ⊢ EOp @ₓ x" := (fun_of_algext h EOp x) (at level 10): algext_scope.

Notation "'ID'" := (AXID)  (at level 50) : algext_scope.                                           (* ◇ = \Diamond *)

Notation "‵‵ c" := (AXConst (dconst c))  (at level 0) : algext_scope.                           (* ‵ = \backprime *)
Notation "‵ c" := (AXConst c)  (at level 0) : algext_scope.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (AXConst (dcoll nil))  (at level 0) : algext_scope.                         (* ‵ = \backprime *)
Notation "‵[||]" := (AXConst (drec nil)) (at level 50) : algext_scope.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (AXBinop AAnd r1 r2) (right associativity, at level 65): algext_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (AXBinop AOr r1 r2) (right associativity, at level 70): algext_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (AXBinop AEq r1 r2) (right associativity, at level 70): algext_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (AXBinop ALt r1 r2) (no associativity, at level 70): algext_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (AXBinop AUnion r1 r2) (right associativity, at level 70): algext_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (AXBinop AMinus r1 r2) (right associativity, at level 70): algext_scope.  (* − = \minus *)
Notation "r1 ♯min r2" := (AXBinop AMin r1 r2) (right associativity, at level 70): algext_scope. (* ♯ = \sharp *)
Notation "r1 ♯max r2" := (AXBinop AMax r1 r2) (right associativity, at level 70): algext_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((AXBinop AConcat) p r) (at level 70) : algext_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((AXBinop AMergeConcat) p r) (at level 70) : algext_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (AXUnop ANeg r1) (right associativity, at level 70): algext_scope.        (* ¬ = \neg *)
Notation "ε( r1 )" := (AXUnop ADistinct r1) (right associativity, at level 70): algext_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (AXUnop ACount r1) (right associativity, at level 70): algext_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (AXUnop AFlatten d) (at level 50) : algext_scope.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((AXUnop AColl) d)  (at level 50) : algext_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((AXUnop (ARec s)) r) (at level 50) : algext_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((AXUnop (ARecRemove s1)) r) (at level 50) : algext_scope.          (* ¬ = \neg and π = \pi *)
Notation "p · r" := ((AXUnop (ADot r)) p) (left associativity, at level 40): algext_scope.      (* · = \cdot *)

Notation "χ⟨ p ⟩( r )" := (AXMap p r) (at level 70) : algext_scope.                              (* χ = \chi *)
Notation "⋈ᵈ⟨ e2 ⟩( e1 )" := (AXMapConcat e2 e1) (at level 70) : algext_scope.                   (* ⟨ ... ⟩ = \rangle ...  \langle *)
Notation "r1 × r2" := (AXProduct r1 r2) (right associativity, at level 70): algext_scope.       (* × = \times *)
Notation "σ⟨ p ⟩( r )" := (AXSelect p r) (at level 70) : algext_scope.                           (* σ = \sigma *)
Notation "r1 ∥ r2" := (AXDefault r1 r2) (right associativity, at level 70): algext_scope.       (* ∥ = \parallel *)
Notation "r1 ◯ r2" := (AXApp r1 r2) (right associativity, at level 60): algext_scope.           (* ◯ = \bigcirc *)

(* Operators only in the extended algebra *)
Notation "⋈⟨ p ⟩( r1 , r2 )" := (AXJoin p r1 r2) (at level 70) : algext_scope.                     (* ⋈ = \Join *)
Notation "⋉⟨ p ⟩( r1 , r2 )" := (AXSemiJoin p r1 r2) (at level 70) : algext_scope.                (* ⋉ = \ltimes *)
Notation "▷⟨ p ⟩( r1 , r2 )" := (AXAntiJoin p r1 r2) (at level 70) : algext_scope.                (* ▷ = \rhd *)

Notation "p ⌈ a ⌋" := (AXMapToRec a p) (at level 70) : algext_scope.
Notation "χ⌈ a ⌋⟨ p1 ⟩( p2 )" := (AXMapAddRec a p1 p2) (at level 70) : algext_scope.

(*
Notation "π[  ]( r )" := (AXRProject nil r) (at level 70) : algext_scope.
Notation "π[ x ]( r )" := (AXRProject (cons x nil) r) (at level 70) : algext_scope.
Notation "π[ x , .. , y ]( r )" := (AXRProject (cons x .. (cons y nil) ..) r) (at level 70) : algext_scope.
*)
Notation "Π[ ]( r )" := (AXProject nil r) (at level 70) : algext_scope.
Notation "Π[ x ]( r )" := (AXProject (cons x nil) r) (at level 70) : algext_scope.
Notation "Π[ x , .. , y ]( r )" := (AXProject (cons x .. (cons y nil) ..) r) (at level 70) : algext_scope.

Notation "¬Π[ s1 ]( r )" := (AXProjectRemove s1 r) (at level 70) : algext_scope.

Notation "ρ[ s1 ↦ s2 ]( r )" := (AXMapRename s1 s2 r) (at level 70) : algext_scope.

Notation "μ[ s1 ]( r )" := (AXUnnestOne s1 r) (at level 70) : algext_scope.
Notation "μ[ s1 ][ s2 ]( r )" := (AXUnnestTwo s1 s2 r) (at level 70) : algext_scope.

Notation "Γ[ g ][ s1 ]( r )" := (AXGroupBy g s1 r) (at level 70) : algext_scope.

(* end hide *)

Local Open Scope string_scope.
Tactic Notation "algext_cases" tactic(first) ident(c) :=
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
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
