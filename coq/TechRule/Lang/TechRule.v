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

(** TechRule stands for ODM technical rules. This is merely a
place-holder since the source language is effectively parsed in
Java. *)

(** Summary:
- Language: TechRule (Technical Rules)
- translating to TechRule:
- translating from TechRule: CAMPRule *)

Require Import Utils.
Require Import CommonRuntime.
Require Export CAMPRuleRuntime.

Section TechRule.
  Context {fruntime:foreign_runtime}.

  Axiom tech_rule : Set.
  Axiom tech_rule_to_camp_rule : tech_rule -> camp_rule.

End TechRule.

