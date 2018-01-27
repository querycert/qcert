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

Require Import CompilerRuntime.
Require String.
Require QOperators QData QCAMP.
Require CAMPRuleRuntime.

Module QCAMPRule(runtime:CompilerRuntime).

  Module Data := QData.QData runtime.
  Module Ops := QOperators.QOperators runtime.
  Module CAMP := QCAMP.QCAMP runtime.

  Definition camp_rule : Set 
    := CAMPRule.camp_rule.
  Definition t : Set 
    := camp_rule.
  
  Definition rule_when : CAMP.camp -> camp_rule -> camp_rule 
    := CAMPRule.rule_when.
  Definition rule_global : CAMP.camp -> camp_rule -> camp_rule 
    := CAMPRule.rule_global.
  Definition rule_not : CAMP.camp -> camp_rule -> camp_rule 
    := CAMPRule.rule_not.
  Definition rule_return : CAMP.camp -> camp_rule 
    := CAMPRule.rule_return.
  Definition rule_match : CAMP.camp -> camp_rule 
    := CAMPRule.rule_match.

  Definition aggregate : (camp_rule -> camp_rule) -> Ops.Unary.op -> CAMP.camp -> nat -> CAMP.camp
    := CAMPRuleSugar.aggregate.

  Definition instanceOf : String.string -> BrandRelation.brands -> CAMP.camp -> CAMP.camp
    := CAMPRuleSugar.instanceOf.

  Definition matches : BrandRelation.brands -> CAMP.camp -> CAMP.camp
    := CAMPRuleSugar.matches.

  Definition fetchRef : BrandRelation.brands -> String.string -> String.string -> CAMP.camp -> CAMP.camp -> CAMP.camp
    := CAMPRuleSugar.fetchRef.

End QCAMPRule.

