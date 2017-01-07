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
Section RuleSugar.

  (* begin hide *)
  Require Import String.
  Require Import List.

  Require Import BasicRuntime.
  Require Export CAMPSugar Rule.
  
  Local Open Scope rule.
  Local Open Scope string.
  (* end hide *)

  Context {fruntime:foreign_runtime}.

  Fixpoint flattenn (n:nat) (p:pat)
    := match n with
       | 0 => p
       | S m =>flattenn m (punop AFlatten p)
       end.
  
  (* Java equivalent: CampAggregateMacro *)
  Definition aggregate (rules:rule->rule) (op:unaryOp) (secondMap:pat) (nflat:nat): pat
    :=  pletIt
          (rule_to_pattern (rules (rule_return penv)))
          (punop op (flattenn nflat (pmap (pletEnv pit secondMap)))).

  Definition aggregate_group_by (rules:rule->rule) (opg:pat) (op:unaryOp) (secondMap:pat) : pat
    :=  pletIt
          (rule_to_pattern (rules (rule_return penv)))
          (punop op (pmap (pletEnv pit secondMap))).

  (* Java equivalent: CampFetchRefMacro *)
  Definition fetchRef (entity:brands) (keyatt:string) (tempvar:string) (keyval:pat) : pat -> pat
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
End RuleSugar.

Delimit Scope rule_scope with rule.

(* Java equivalent: CampInstanceOfMacro *)
Notation "n 'INSTANCEOF' t 'WHERE' p" := ((instanceOf n t p)%rule) (at level 70) : rule_scope.
Notation "p 'TEMPVAR' t 'FETCH' e 'KEY' a 'DO' pcont" := ((fetchRef e a t p pcont)%rule) (at level 70) : rule_scope.
(* Java equivalent: CampMatchesMacro *)
Notation "'MATCHES' t 'WHERE' p" := ((matches t p)%rule) (at level 70) : rule_scope.
Notation "'VARIABLES' sl" := (returnVariables sl) (at level 70) : rule_scope.

Notation " 'AGGREGATE' m1 'DO' op 'OVER' m2 'FLATTEN' f" := (aggregate m1 op m2 f) (at level 70) : rule_scope.
Notation " 'AGGREGATEG' m1 'GROUPBY' opg 'DO' op 'OVER' m2" := (aggregate_group_by m1 opg op m2) (at level 70) : rule_scope.
Notation "p1 'ANDMAPSNONES' p2" :=  ((p1 ∧ notholds p2 RETURN BINDINGS)%rule) (left associativity, at level 83) : rule_scope.

Notation "a ;; b" := (a b) (at level 99, right associativity, only parsing) : rule_scope.

(* Can be use inside an aggregate (function composition instead of application *)
Notation "a ;;; b" := (fun x => a (b x)) (at level 99, right associativity, only parsing) : rule_scope.  

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
