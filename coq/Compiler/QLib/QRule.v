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
Module QRule(runtime:CompilerRuntime).
  Require String.
  Require QOperators QData QPattern.
  Require Rule RuleSugar.

  Module Data := QData.QData runtime.
  Module Ops := QOperators.QOperators runtime.
  Module Pattern := QPattern.QPattern runtime.

  Definition rule : Set 
    := Rule.rule.
  Definition t : Set 
    := rule.
  
  Definition rule_when : Pattern.expr -> rule -> rule 
    := Rule.rule_when.
  Definition rule_global : Pattern.expr -> rule -> rule 
    := Rule.rule_global.
  Definition rule_not : Pattern.expr -> rule -> rule 
    := Rule.rule_not.
  Definition rule_return : Pattern.expr -> rule 
    := Rule.rule_return.

  Definition aggregate : (rule -> rule) -> Ops.Unary.op -> Pattern.expr -> nat -> Pattern.expr
    := RuleSugar.aggregate.

End QRule.
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
