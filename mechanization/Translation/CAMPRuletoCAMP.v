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
Require Import CAMPRuleRuntime.
Require Import CAMPRuntime.
  
Section CAMPRuletoCAMP.
  Section Top.
    Context {fr:foreign_runtime}.
    (** Note: Translation from CAMP Rules to CAMP is really macro-expansion *)
    Definition camp_rule_to_camp_top (q:camp_rule) : camp := camp_rule_to_camp q.

    Context (h:brand_relation_t).

    Theorem camp_rule_to_camp_top_correct :
      forall q:camp_rule, forall global_env:bindings,
          camp_rule_eval_top h q global_env =
          camp_eval_top h (camp_rule_to_camp_top q) global_env.
    Proof.
      intros.
      unfold camp_rule_eval_top.
      unfold camp_eval_top.
      reflexivity.
    Qed.
  End Top.
    
End CAMPRuletoCAMP.

