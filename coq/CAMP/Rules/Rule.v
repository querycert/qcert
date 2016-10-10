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
Section Rule.

  (* begin hide *)
  Require Import String.
  Require Import List.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.
  Require Export PatternSugar.
  
  Local Open Scope rule.
  Local Open Scope string.
  (* end hide *)

  Context {fruntime:foreign_runtime}.

  (** rules and their semantics *)
  Inductive rule :=
  (** a normal rule, matched against each working memory element in turn *)
  | rule_when : pat -> rule -> rule
  (** a rule that should run against the entire working memory (as a collection of elements) *)
  | rule_global : pat -> rule -> rule
  (** A rule that must not match any working memory element *)
  | rule_not : pat -> rule -> rule
  (** This is the last part of a rule, and it allow the 
        rule to return a value for each successful match-set. pit can be used as the identity *)
  | rule_return : pat -> rule.  

  (* Java equivalent: CampRule.convertToPattern *)
  Fixpoint rule_to_pattern (rule:rule) : pat
    := match rule with
         | rule_when p ps =>
           punop AFlatten
                 (WW
                    (pmap
                       (pletEnv
                          p
                          (rule_to_pattern ps))))
         | rule_global p ps =>
           punop AFlatten
                 (makeSingleton
                    (pletEnv
                       (WW p)
                       (rule_to_pattern ps)))
         | rule_not p ps =>
           punop AFlatten
                 (makeSingleton
                    (pletEnv
                       (notholds p RETURN BINDINGS)
                       (rule_to_pattern ps)))
         | rule_return p =>
           makeSingleton p
       end.

  Definition eval_rule_debug (h:list(string*string)) (print_env:bool) (r:rule) (world:list data)
    : presult_debug data
    := interp_debug h (mkWorld world) print_env nil (rule_to_pattern r) nil dunit.

  Definition eval_rule_res_to_string
             (h:list(string*string)) (print_env:bool) (r:rule) (world:list data)
    : string
    := let pp := (rule_to_pattern r) in
       print_presult_debug pp
                           (interp_debug h
                                         (mkWorld world)
                                         print_env nil pp nil dunit).

  (** Semantics of CAMP rules, returning a presult *)
  Definition eval_rule_res (h:list(string*string)) (r:rule) (world:list data)
    : presult data
    := interp h (mkWorld world) (rule_to_pattern r) nil dunit.

  Definition eval_rule (h:list(string*string)) (r:rule) (world:list data)
    : option (list data)
    := match eval_rule_res h r world with
       | Success l => Some (l::nil)
       | RecoverableError => Some nil
       | TerminalError => None
       end.

End Rule.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
