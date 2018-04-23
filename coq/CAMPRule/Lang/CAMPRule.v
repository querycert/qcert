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


(** CAMPRule is a small language built on top of CAMP (Calculus for
  Aggregating Matching Patterns). It help to bridge the gap between
  the CAMP core calculus and real-world production rule languages such
  as JRules.
 *)

(** The language is built as a set of macros on top of CAMP. It is
    described in Section 3 of the article "A Pattern Calculus for Rule
    Languages: Expressiveness, Compilation, and Mechanization" by Avraham
    Shinnar, Jérôme Siméon, and Martin Hirzel (ECOOP'2015).
 *)


Require Import String.
Require Import List.
Require Import EquivDec.
Require Import Utils.
Require Import CommonRuntime.
Require Export CAMPRuntime.

Section CAMPRule.
  (* This file defines derived patterns, notations, and concepts *)
  Local Open Scope camp_scope.
  Local Open Scope string.

  Context {fruntime:foreign_runtime}.

  (** * Abstract Syntax Tree *)

  Inductive camp_rule :=
  | rule_when : camp -> camp_rule -> camp_rule (**r Match against each element of the working memory. *)
  | rule_global : camp -> camp_rule -> camp_rule (**r Match against the working memory as a collection *)
  | rule_not : camp -> camp_rule -> camp_rule (**r A rule that must not match any working memory element. *)
  | rule_return : camp -> camp_rule (**r Rule to return a value for each successful match-set. *)
  | rule_match : camp -> camp_rule. (**r This allows a rule to simply match a camp pattern. *)

  (** * Translate CAMPRule into the CAMP kernel *)

  (* Java equivalent: CampRule.convertToPattern *)
  Fixpoint camp_rule_to_camp (rule:camp_rule) : camp
    := match rule with
         | rule_when p ps =>
           punop OpFlatten
                 (WW
                    (pmap
                       (pletEnv
                          p
                          (camp_rule_to_camp ps))))
         | rule_global p ps =>
           punop OpFlatten
                 (makeSingleton
                    (pletEnv
                       (WW p)
                       (camp_rule_to_camp ps)))
         | rule_not p ps =>
           punop OpFlatten
                 (makeSingleton
                    (pletEnv
                       (notholds p RETURN BINDINGS)
                       (camp_rule_to_camp ps)))
         | rule_return p =>
           makeSingleton p
         | rule_match p =>
           p
       end.

  (** * Evaluation *)

  Definition eval_camp_rule_debug (h:list(string*string)) (print_env:bool) (r:camp_rule) (world:list data)
    : presult_debug data
    := camp_eval_debug h (mkWorld world) print_env nil (camp_rule_to_camp r) nil dunit.

  Definition eval_camp_rule_res_to_string
             (h:list(string*string)) (print_env:bool) (r:camp_rule) (world:list data)
    : string
    := let pp := (camp_rule_to_camp r) in
       print_presult_debug pp toString_camp_with_path
                           (camp_eval_debug h
                                         (mkWorld world)
                                         print_env nil pp nil dunit).

  (** Semantics of CAMP rules, returning a presult *)
  Definition eval_camp_rule_res (h:list(string*string)) (r:camp_rule) (world:list data)
    : presult data
    := camp_eval h (mkWorld world) (camp_rule_to_camp r) nil dunit.

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
      presult_to_result (camp_eval h (rec_sort cenv) (camp_rule_to_camp q) nil dunit).

    Definition camp_rule_eval_top_debug (debug:bool) (q:camp_rule) (cenv:bindings) :=
      let pp := camp_rule_to_camp q in
      print_presult_debug pp toString_camp_with_path
                          (camp_eval_debug h
                                           (rec_sort cenv)
                                           debug nil pp nil dunit).
  End Top.

End CAMPRule.

