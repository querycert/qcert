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
Require Import CommonRuntime.
Require Import TechRuleRuntime.
Require Import CAMPRuleRuntime.
  
Section TechRuletoCAMPRule.
  Section Top.
    Context {fr:foreign_runtime}.

    (** Note: Translation from Tech Rules to CAMP Rule is done in Java *)
    Definition tech_rule_to_camp_rule_top (q:tech_rule) : camp_rule :=
      tech_rule_to_camp_rule q.
  End Top.
    
End TechRuletoCAMPRule.

