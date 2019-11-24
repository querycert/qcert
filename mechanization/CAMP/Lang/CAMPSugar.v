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

Require Import String.
Require Import List.
Require Import EquivDec.
Require Import ZArith.
Require Import Utils.
Require Import CommonRuntime.  
Require Export CAMP.

Section CAMPSugar.
  (* This file defines derived patterns, notations, and concepts *)
  Context {fruntime:foreign_runtime}.

  (* Some success/failure macros *)
    
  (* Convention: "just success" is modeled as Some {} *)
  (* Java equivalent: CampAcceptMacro *)
  Definition paccept := pconst (drec nil).

  Definition pfail : camp := passert (pconst (dconst false)).
  Definition makeSingleton (p:camp) : camp := punop OpBag p.

  (* Some operators macros *)
    
  Definition pand (p1 p2:camp):= pletEnv (passert p1) p2.
    
  (* Java equivalent: CampToStringMacro *)
  Definition toString p := punop OpToString p.

  Definition psome := pleft.
  Definition pnone := pright.
  Definition pnull := (pconst dnone).
  
  (* Used in the expansion of Java macro CampUnbrandDotMacro *)
  Definition punbrand' p := punop OpUnbrand p.
  (* Used in the expansion of Java macro CampUnbrandDotMacro *)
  Definition punbrand := punbrand' pit.

  Definition pcast' b p:= pletIt (punop (OpCast b) p) psome.
  (* Java equivalent: CampCastMacro *)
  Definition pcast b := pcast' b pit.

  Definition psingleton' p := pletIt (punop OpSingleton p) psome.
  Definition psingleton := psingleton' pit.

  (* Some var/env macros *)
    
  (* Java equivalent: CampBindingsMacro *)
  Definition pWithBindings : camp -> camp := pletIt penv.
  (* Java equivalent: CampVarwithMacro *)
  Definition pvarwith f : camp -> camp := punop (OpRec f).
  (* Inlined in several Java macro definitions *)
  Definition pvar f : camp := pvarwith f pit.
  (* Used in the expansion of Java macro CampUnbrandDotMacro *)
  Definition pdot f : camp -> camp := pletIt (punop (OpDot f) pit).
  (* Java equivalent: CampUnbrandDotMacro *)
  Definition pbdot s p : camp := (pletIt punbrand (pdot s p)).
  Definition pbsomedot s p : camp := (pletIt (pbdot s p) psome).
  Definition varOf (varName:string) (p:camp) := pletEnv (pvar varName) p.
  (* Java equivalent: CampLookupMacro *)
  Definition lookup c := (pWithBindings (pdot c pit)).

  Definition withVar (name:string) (p:camp) : camp := pletIt (lookup name) p.
  Definition withBrandedVar (name:string) (p:camp) : camp :=
    pletIt (punbrand' (lookup name)) p.

  (* Java equivalent: CampIsMacro *)
  Definition pIS var p := pletIt p (pvar var).
    
  Example empty_binding := @nil (string*data).

  Definition stringConcat a b := pbinop OpStringConcat (toString a) (toString b).
    
  (* Some notations *)

  Fixpoint pFoldRec (camps:list (string*camp)) (init:data) : camp
    := match camps with
       | nil => pconst init
       | (s,p)::ls => pletIt (pletEnv
                                (pdot s (pvar "current"))
                                (pletIt (pFoldRec ls init) (pvar "previous")))
                             p
       end.

  Fixpoint pMapRec (camps:list (string*camp)) : camp 
    := match camps with
       | nil => pconst (drec nil)
       | (s,p)::ls => pletEnv (pdot s p) (pMapRec ls)
       end.

  Definition pMapRecFromFold (camps:list (string*camp)) : camp 
    := pFoldRec 
         (map (fun xy => ((fst xy), pdot "current" (snd xy))) camps)
         (drec nil).

  (** A reduction operator for patterns.
        This is particularly useful with binary operators and sequencing constructs.
        For example, 
           camp_reduce (pbinop AAnd) [p1; p2; p3]
        and 
           camp_reduce pletIt [p1; p2; p3]
   *)

  Fixpoint camp_reduce (f:camp->camp->camp) (l:list camp) : camp
    := match l with
       | nil => passert (pconst (dconst false))
       | p1::l' => match l' with
                   | nil => p1
                   | p2::l'' => f p1 (camp_reduce f l')
                   end
       end.

  Definition camp_binop_reduce (b:binary_op) (l:list camp) : camp :=
    camp_reduce (fun p1 p2 => (pbinop b p1 p2)) l.

  (* Defines what it means for two patterns to be equivalent *)
  Definition camp_equiv p₁ p₂ := forall h c b d, camp_eval h c p₁ b d = camp_eval h c p₂ b d.

  Theorem withAccept_id p : camp_equiv (pletIt pit p) p.
  Proof.
    unfold camp_equiv; reflexivity.
  Qed.

  Lemma preduce_id b (l:list camp):
    camp_equiv (camp_reduce (pbinop b) l) (camp_binop_reduce b l).
  Proof.
    unfold camp_equiv.
    intros.
    reflexivity.
  Qed.
    
  (* Used in Rules *)
  
  (* objects are branded records: brand ClassName (rec [ attributes... ])  *)
  (* Java equivalent: CampTypedObjectMacro *)
  Definition typedObject (type:brands) (p:camp) :=
    pletIt (pcast type) p.

  (* Java equivalent: CampNamedObjectMacro *)
  Definition namedObject (varName:string) (type:brands) (p:camp) :=
    pletIt (pcast type)
           (pletEnv (pvar varName)
                    p).

  Definition class (type:brands) (contents:data)
    := dbrand type contents.

  (* Java equivalent: CampVariablesMacro *)
  Definition returnVariables (sl:list string) : camp
    := punop (OpRecProject (insertion_sort ODT_lt_dec sl)) penv.

  (** Useful definitions *)
  (* Java equivalent: CampNowMacro *)
  Definition pnow := pgetConstant ("NOW").

  Definition WW p := pletIt (pgetConstant ("WORLD")) p.

  (* NB: This version does not use "fresh" as in the paper.  
   * See mapall_let in Translation/NNRCtoCAMP.v for a version
   * that uses a fresh variable to avoid recomputing (pmap p) 
   *)
  Notation "p1 ≐ p2" := (passert (pbinop OpEqual p1 p2)) (right associativity, at level 70, only parsing).     (* ≐ = \doteq *)
  Notation "‵ c" := (pconst (dconst c)) (at level 0). (* ‵ = \backprime *)

  Definition mapall p :=
    pletEnv (punop OpCount pit ≐ punop OpCount (pmap p))
            (pmap p).

  (* p does not hold for any element in the list *)
  (* Java equivalent: CampBasicFunctionRule.mapsnone *)
  Definition mapsnone p := (punop OpCount (pmap p) ≐ ‵(0%Z)).

  (* p holds for exactly one element in the list *)
  Definition mapsone p := (punop OpCount (pmap p) ≐ ‵(1%Z)).

  (* Java equivalent: CampBasicFunctionRule.notholds *)
  Definition notholds p := WW (mapsnone p).

End CAMPSugar.
  
Delimit Scope camp_scope with camp.

Notation "p1 |p-eq| p2" := (pbinop OpEqual p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-union| p2" := (pbinop OpBagUnion p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-concat| p2" := (pbinop OpRecConcat p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-mergeconcat| p2" := (pbinop OpRecMerge p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-and| p2" := (pbinop OpAnd p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-or| p2" := (pbinop OpOr p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-lt| p2" := (pbinop OpLt p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-le| p2" := (pbinop OpLe p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-bagdiff| p2" := (pbinop OpBagDiff p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-bagmin| p2" := (pbinop OpBagMin p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-bagmax| p2" := (pbinop OpBagMax p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-contains| p2" := (pbinop OpContains p1 p2) (right associativity, at level 70): camp_scope.
Notation "p1 |p-stringconcat| p2" := (pbinop OpStringConcat p1 p2) (right associativity, at level 70): camp_scope.
Notation "a '+s+' b" := (stringConcat a b) (right associativity, at level 60) : camp_scope.

Notation "|p-min-num|( p )" := (punop OpNatMin p) (right associativity, at level 70): camp_scope.
Notation "|p-max-num|( p )" := (punop OpNatMin p) (right associativity, at level 70): camp_scope.

Notation "p1 ≐ p2" := (passert (pbinop OpEqual p1 p2)) (right associativity, at level 70, only parsing): camp_scope.     (* ≐ = \doteq *)
Notation "p1 ∧ p2" := (pand p1 p2) (right associativity, at level 65): camp_scope. (* ∧ = \wedge *)
Notation "…" := pit.
Notation "s ↓ p" := (pdot s p) (right associativity, at level 30): camp_scope. (* ↓ = \downarrow *)
(* Java equivalent: CampBindingsMacro *)
Notation "'BINDINGS'" := (pWithBindings pit) : camp_scope.
(* Java equivalent: CampReturnMacro *)
Notation "a 'RETURN' b" := (pletEnv a b) (right associativity, at level 30, only parsing) : camp_scope.

Notation "! x" := (punbrand' x) (at level 0) : camp_scope.
Notation "t 'COLON' p" := (varOf t p) (at level 70) : camp_scope.
(* Java equivalent: CampIsMacro *)
Notation "var 'IS' p" := (pIS var p) (at level 71, only parsing) : camp_scope.

(* non-unicode alternative notations *)
Notation "‵ c" := (pconst (dconst c)) (at level 0). (* ‵ = \backprime *)
Notation "#` c" := (pconst (dconst c)) (only parsing, at level 0) : camp_scope.
Notation "s #-> p" := (pdot s p) (only parsing, right associativity, at level 30): camp_scope.
Notation "s !#-> p" := (pbdot s p) (only parsing, right associativity, at level 30): camp_scope.
Notation "#_" := pit (only parsing): camp_scope.
Notation "p1 #= p2" := (passert (pbinop OpEqual p1 p2)) (only parsing, right associativity, at level 70): camp_scope.

