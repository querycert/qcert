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
Section CAMPRule.

  (* begin hide *)
  Require Import String.
  Require Import List.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.
  Require Export CAMPSugar.
  
  Local Open Scope camp_scope.
  Local Open Scope string.
  (* end hide *)

  Context {fruntime:foreign_runtime}.

  (** rules and their semantics *)
  Inductive camp_rule :=
  (** a normal rule, matched against each working memory element in turn *)
  | rule_when : camp -> camp_rule -> camp_rule
  (** a rule that should run against the entire working memory (as a collection of elements) *)
  | rule_global : camp -> camp_rule -> camp_rule
  (** A rule that must not match any working memory element *)
  | rule_not : camp -> camp_rule -> camp_rule
  (** This is the last part of a rule, and it allow the 
        rule to return a value for each successful match-set. pit can be used as the identity *)
  | rule_return : camp -> camp_rule
  (** This allows a rule to simply match a camp pattern *)
  | rule_match : camp -> camp_rule.  

  (* Java equivalent: CampRule.convertToPattern *)
  Fixpoint camp_rule_to_camp (rule:camp_rule) : camp
    := match rule with
         | rule_when p ps =>
           punop AFlatten
                 (WW
                    (pmap
                       (pletEnv
                          p
                          (camp_rule_to_camp ps))))
         | rule_global p ps =>
           punop AFlatten
                 (makeSingleton
                    (pletEnv
                       (WW p)
                       (camp_rule_to_camp ps)))
         | rule_not p ps =>
           punop AFlatten
                 (makeSingleton
                    (pletEnv
                       (notholds p RETURN BINDINGS)
                       (camp_rule_to_camp ps)))
         | rule_return p =>
           makeSingleton p
         | rule_match p =>
           p
       end.

  Definition eval_camp_rule_debug (h:list(string*string)) (print_env:bool) (r:camp_rule) (world:list data)
    : presult_debug data
    := interp_debug h (mkWorld world) print_env nil (camp_rule_to_camp r) nil dunit.

  Definition eval_camp_rule_res_to_string
             (h:list(string*string)) (print_env:bool) (r:camp_rule) (world:list data)
    : string
    := let pp := (camp_rule_to_camp r) in
       print_presult_debug pp
                           (interp_debug h
                                         (mkWorld world)
                                         print_env nil pp nil dunit).

  (** Semantics of CAMP rules, returning a presult *)
  Definition eval_camp_rule_res (h:list(string*string)) (r:camp_rule) (world:list data)
    : presult data
    := interp h (mkWorld world) (camp_rule_to_camp r) nil dunit.

  Definition eval_camp_rule (h:list(string*string)) (r:camp_rule) (world:list data)
    : option (list data)
    := match eval_camp_rule_res h r world with
       | Success l => Some (l::nil)
       | RecoverableError => Some nil
       | TerminalError => None
       end.

  Section Top.
    Context (h:brand_relation_t).

    Definition camp_rule_eval_top (q:camp_rule) (cenv:bindings) :=
      match interp h (rec_sort cenv) (camp_rule_to_camp q) nil dunit with
      | Success l => Some (dcoll (l::nil))
      | RecoverableError => Some (dcoll nil)
      | TerminalError => None
      end.
  End Top.

End CAMPRule.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
