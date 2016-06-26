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

(* This file defines derived patterns, notations, and concepts *)
Section PatternSugar.

  Require Import String.
  Require Import List.
  Require Import EquivDec.

  Require Import BasicRuntime.  
  Require Export Pattern.

  Context {fruntime:foreign_runtime}.

  (* Some success/failure macros *)
    
  (* Convention: "just success" is modeled as Some {} *)
  (* Java equivalent: CampAcceptMacro *)
  Definition paccept := pconst (drec nil).

  Definition pfail : pat := passert (pconst (dconst false)).
  Definition makeSingleton (p:pat) : pat := punop AColl p.

  (* Some operators macros *)
    
  Definition pand (p1 p2:pat):= pletEnv (passert p1) p2.
    
  (* Java equivalent: CampToStringMacro *)
  Definition toString p := punop AToString p.

  Definition psome := pleft.
  Definition pnone := pright.
  Definition pnull := (pconst dnone).
  
  (* Used in the expansion of Java macro CampUnbrandDotMacro *)
  Definition punbrand' p := punop AUnbrand p.
  (* Used in the expansion of Java macro CampUnbrandDotMacro *)
  Definition punbrand := punbrand' pit.

  Definition pcast' b p:= pletIt (punop (ACast b) p) psome.
  (* Java equivalent: CampCastMacro *)
  Definition pcast b := pcast' b pit.

  Definition psingleton' p := pletIt (punop ASingleton p) psome.
  Definition psingleton := psingleton' pit.

  (* Some var/env macros *)
    
  (* Java equivalent: CampBindingsMacro *)
  Definition pWithBindings : pat -> pat := pletIt penv.
  (* Java equivalent: CampVarwithMacro *)
  Definition pvarwith f : pat -> pat := punop (ARec f).
  (* Inlined in several Java macro definitions *)
  Definition pvar f : pat := pvarwith f pit.
  (* Used in the expansion of Java macro CampUnbrandDotMacro *)
  Definition pdot f : pat -> pat := pletIt (punop (ADot f) pit).
  (* Java equivalent: CampUnbrandDotMacro *)
  Definition pbdot s p : pat := (pletIt punbrand (pdot s p)).
  Definition pbsomedot s p : pat := (pletIt (pbdot s p) psome).
  Definition varOf (varName:string) (p:pat) := pletEnv (pvar varName) p.
  (* Java equivalent: CampLookupMacro *)
  Definition lookup c := (pWithBindings (pdot c pit)).

  Definition withVar (name:string) (p:pat) : pat := pletIt (lookup name) p.
  Definition withBrandedVar (name:string) (p:pat) : pat :=
    pletIt (punbrand' (lookup name)) p.

  (* Java equivalent: CampIsMacro *)
  Definition pIS var p := pletIt p (pvar var).
    
  Example empty_binding := @nil (string*data).

  Definition stringConcat a b := pbinop ASConcat (toString a) (toString b).
    
  (* Some notations *)

  Fixpoint pFoldRec (pats:list (string*pat)) (init:data) : pat
    := match pats with
       | nil => pconst init
       | (s,p)::ls => pletIt (pletEnv
                                (pdot s (pvar "current"))
                                (pletIt (pFoldRec ls init) (pvar "previous")))
                             p
       end.

  Fixpoint pMapRec (pats:list (string*pat)) : pat 
    := match pats with
       | nil => pconst (drec nil)
       | (s,p)::ls => pletEnv (pdot s p) (pMapRec ls)
       end.

  Definition pMapRecFromFold (pats:list (string*pat)) : pat 
    := pFoldRec 
         (map (fun xy => ((fst xy), pdot "current" (snd xy))) pats)
         (drec nil).

  (** A reduction operator for patterns.
        This is particularly useful with binary operators and sequencing constructs.
        For example, 
           pat_reduce (pbinop AAnd) [p1; p2; p3]
        and 
           pat_reduce pletIt [p1; p2; p3]
   *)

  Fixpoint pat_reduce (f:pat->pat->pat) (l:list pat) : pat
    := match l with
       | nil => passert (pconst (dconst false))
       | p1::l' => match l' with
                   | nil => p1
                   | p2::l'' => f p1 (pat_reduce f l')
                   end
       end.

  Definition pat_binop_reduce (b:binOp) (l:list pat) : pat :=
    pat_reduce (fun p1 p2 => (pbinop b p1 p2)) l.

  (* Defines what it means for two patterns to be equivalent *)
  Definition pat_equiv p₁ p₂ := forall h c b d, interp h c p₁ b d = interp h c p₂ b d.

  Theorem withAccept_id p : pat_equiv (pletIt pit p) p.
  Proof.
    unfold pat_equiv; reflexivity.
  Qed.

  Lemma preduce_id b (l:list pat):
    pat_equiv (pat_reduce (pbinop b) l) (pat_binop_reduce b l).
  Proof.
    unfold pat_equiv.
    intros.
    reflexivity.
  Qed.
    
  (* Used in Rules *)
  
  (* objects are branded records: brand ClassName (rec [ attributes... ])  *)
  (* Java equivalent: CampTypedObjectMacro *)
  Definition typedObject (type:brands) (p:pat) :=
    pletIt (pcast type) p.

  (* Java equivalent: CampNamedObjectMacro *)
  Definition namedObject (varName:string) (type:brands) (p:pat) :=
    pletIt (pcast type)
           (pletEnv (pvar varName)
                    p).

  Definition class (type:brands) (contents:data)
    := dbrand type contents.

  (* Java equivalent: CampVariablesMacro *)
  Definition returnVariables (sl:list string) : pat
    := punop (ARecProject sl) penv.

  (** Useful definitions *)
  (* Java equivalent: CampNowMacro *)
  Definition pnow := pgetconstant ("NOW").

  Definition WW p := pletIt (pgetconstant ("WORLD")) p.

  (* NB: This version does not use "fresh" as in the paper.  
   * See mapall_let in Translation/NNRCtoPattern.v for a version
   * that uses a fresh variable to avoid recomputing (pmap p) 
   *)
  Notation "p1 ≐ p2" := (passert (pbinop AEq p1 p2)) (right associativity, at level 70, only parsing).     (* ≐ = \doteq *)
  Notation "‵ c" := (pconst (dconst c)) (at level 0). (* ‵ = \backprime *)

  Definition mapall p :=
    pletEnv (punop ACount pit ≐ punop ACount (pmap p))
            (pmap p).

  Require Import ZArith.
  
  (* p does not hold for any element in the list *)
  (* Java equivalent: CampBasicFunctionRule.mapsnone *)
  Definition mapsnone p := (punop ACount (pmap p) ≐ ‵(0%Z)).

  (* p holds for exactly one element in the list *)
  Definition mapsone p := (punop ACount (pmap p) ≐ ‵(1%Z)).

  (* Java equivalent: CampBasicFunctionRule.notholds *)
  Definition notholds p := WW (mapsnone p).

End PatternSugar.
  
Delimit Scope rule_scope with rule.

Notation "p1 |p-eq| p2" := (pbinop AEq p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-union| p2" := (pbinop AUnion p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-concat| p2" := (pbinop AConcat p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-mergeconcat| p2" := (pbinop AMergeConcat p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-and| p2" := (pbinop AAnd p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-or| p2" := (pbinop AOr p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-lt| p2" := (pbinop ALt p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-le| p2" := (pbinop ALe p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-minus| p2" := (pbinop AMinus p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-min| p2" := (pbinop AMin p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-max| p2" := (pbinop AMax p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-contains| p2" := (pbinop AContains p1 p2) (right associativity, at level 70): rule_scope.
Notation "p1 |p-sconcat| p2" := (pbinop ASConcat p1 p2) (right associativity, at level 70): rule_scope.
Notation "a '+s+' b" := (stringConcat a b) (right associativity, at level 60) : rule_scope.

Notation "|p-min-num|( p )" := (punop ANumMin p) (right associativity, at level 70): rule_scope.
Notation "|p-max-num|( p )" := (punop ANumMin p) (right associativity, at level 70): rule_scope.

Notation "p1 ≐ p2" := (passert (pbinop AEq p1 p2)) (right associativity, at level 70, only parsing): rule_scope.     (* ≐ = \doteq *)
Notation "p1 ∧ p2" := (pand p1 p2) (right associativity, at level 65): rule_scope. (* ∧ = \wedge *)
Notation "…" := pit.
Notation "s ↓ p" := (pdot s p) (right associativity, at level 30): rule_scope. (* ↓ = \downarrow *)
(* Java equivalent: CampBindingsMacro *)
Notation "'BINDINGS'" := (pWithBindings pit) : rule_scope.
(* Java equivalent: CampReturnMacro *)
Notation "a 'RETURN' b" := (pletEnv a b) (right associativity, at level 30, only parsing) : rule_scope.

Notation "! x" := (punbrand' x) (at level 0) : rule_scope.
Notation "t 'COLON' p" := (varOf t p) (at level 70) : rule_scope.
(* Java equivalent: CampIsMacro *)
Notation "var 'IS' p" := (pIS var p) (at level 71, only parsing) : rule_scope.

(* non-unicode alternative notations *)
Notation "‵ c" := (pconst (dconst c)) (at level 0). (* ‵ = \backprime *)
Notation "#` c" := (pconst (dconst c)) (only parsing, at level 0) : rule_scope.
Notation "s #-> p" := (pdot s p) (only parsing, right associativity, at level 30): rule_scope.
Notation "s !#-> p" := (pbdot s p) (only parsing, right associativity, at level 30): rule_scope.
Notation "#_" := pit (only parsing): rule_scope.
Notation "p1 #= p2" := (passert (pbinop AEq p1 p2)) (only parsing, right associativity, at level 70): rule_scope.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
