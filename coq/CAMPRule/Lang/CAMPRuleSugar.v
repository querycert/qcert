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
Require Import Utils.
Require Import CommonRuntime.
Require Export CAMPSugar.
Require Export CAMPRule.
  
Section CAMPRuleSugar.
  (* This file defines derived patterns, notations, and concepts *)
  Local Open Scope camp_scope.
  Local Open Scope string.

  Context {fruntime:foreign_runtime}.

  Fixpoint flattenn (n:nat) (p:camp)
    := match n with
       | 0 => p
       | S m =>flattenn m (punop OpFlatten p)
       end.
  
  (* Java equivalent: CampAggregateMacro *)
  Definition aggregate (rules:camp_rule->camp_rule) (op:unary_op) (secondMap:camp) (nflat:nat): camp
    :=  pletIt
          (camp_rule_to_camp (rules (rule_return penv)))
          (punop op (flattenn nflat (pmap (pletEnv pit secondMap)))).

  Definition aggregate_group_by (rules:camp_rule->camp_rule) (opg:camp) (op:unary_op) (secondMap:camp) : camp
    :=  pletIt
          (camp_rule_to_camp (rules (rule_return penv)))
          (punop op (pmap (pletEnv pit secondMap))).

  (* Java equivalent: CampFetchRefMacro *)
  Definition fetchRef (entity:brands) (keyatt:string) (tempvar:string) (keyval:camp) : camp -> camp
    := pletIt
         (pletEnv (pvarwith tempvar keyval)
                  (WW
                     (pletIt
                        (pmap
                           (pletIt (pcast entity) (pand ((pletIt punbrand (keyatt ↓ …) |p-eq| (lookup tempvar))) pit)))
                        psingleton))).

  (* Java equivalent: CampInstanceOfMacro *)
  Definition instanceOf n t p := namedObject n t (p RETURN BINDINGS).
  (* Java equivalent: CampMatchesMacro *)
  Definition matches t p := typedObject t (p RETURN BINDINGS).
End CAMPRuleSugar.

Delimit Scope camp_scope with camp_rule.

(* Java equivalent: CampInstanceOfMacro *)
Notation "n 'INSTANCEOF' t 'WHERE' p" := ((instanceOf n t p)%camp_rule) (at level 70) : camp_scope.
Notation "p 'TEMPVAR' t 'FETCH' e 'KEY' a 'DO' pcont" := ((fetchRef e a t p pcont)%camp_rule) (at level 70) : camp_scope.
(* Java equivalent: CampMatchesMacro *)
Notation "'MATCHES' t 'WHERE' p" := ((matches t p)%camp_rule) (at level 70) : camp_scope.
Notation "'VARIABLES' sl" := (returnVariables sl) (at level 70) : camp_scope.

Notation " 'AGGREGATE' m1 'DO' op 'OVER' m2 'FLATTEN' f" := (aggregate m1 op m2 f) (at level 70) : camp_scope.
Notation " 'AGGREGATEG' m1 'GROUPBY' opg 'DO' op 'OVER' m2" := (aggregate_group_by m1 opg op m2) (at level 70) : camp_scope.
Notation "p1 'ANDMAPSNONES' p2" :=  ((p1 ∧ notholds p2 RETURN BINDINGS)%camp_rule) (left associativity, at level 83) : camp_scope.

Notation "a ;; b" := (a b) (at level 99, right associativity, only parsing) : camp_scope.

(* Can be use inside an aggregate (function composition instead of application *)
Notation "a ;;; b" := (fun x => a (b x)) (at level 99, right associativity, only parsing) : camp_scope.  

