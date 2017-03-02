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
Require RuleRuntime.

Module QRule(runtime:CompilerRuntime).

  Module Data := QData.QData runtime.
  Module Ops := QOperators.QOperators runtime.
  Module CAMP := QCAMP.QCAMP runtime.

  Definition rule : Set 
    := Rule.rule.
  Definition t : Set 
    := rule.
  
  Definition rule_when : CAMP.expr -> rule -> rule 
    := Rule.rule_when.
  Definition rule_global : CAMP.expr -> rule -> rule 
    := Rule.rule_global.
  Definition rule_not : CAMP.expr -> rule -> rule 
    := Rule.rule_not.
  Definition rule_return : CAMP.expr -> rule 
    := Rule.rule_return.

  Definition aggregate : (rule -> rule) -> Ops.Unary.op -> CAMP.expr -> nat -> CAMP.expr
    := RuleSugar.aggregate.

  Definition instanceOf : String.string -> BrandRelation.brands -> CAMP.expr -> CAMP.expr
    := RuleSugar.instanceOf.

  Definition matches : BrandRelation.brands -> CAMP.expr -> CAMP.expr
    := RuleSugar.matches.

  Definition fetchRef : BrandRelation.brands -> String.string -> String.string -> CAMP.expr -> CAMP.expr -> CAMP.expr
    := RuleSugar.fetchRef.

End QRule.
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
