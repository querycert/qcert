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
Require Import EquivDec.
Require Import Utils.
Require Import CommonSystem.
Require Export CAMPRule.
Require Import TCAMP.

Section TCAMPRule.
  (* This file defines derived patterns, notations, and concepts *)
  Local Open Scope camp_scope.
  Local Open Scope string.

  (* Some typing wrappers *)

  Context {m:basic_model}.

  Definition mkTWorld (τworld:rtype) : tbindings
    := ("WORLD",Coll τworld)::nil.
  
  Definition camp_rule_type (τworld τout:rtype) (r:camp_rule) : Prop :=
    camp_type (mkTWorld τworld) nil (camp_rule_to_camp r) Unit τout.

  Lemma typed_rule_correct {τworld τout} (r:camp_rule):
    camp_rule_type τworld τout r ->
    forall (world:list data),
      bindings_type (mkWorld world) (mkTWorld τworld) ->
      (exists d, eval_camp_rule brand_relation_brands  r world = Some (d::nil) /\ (data_type d τout))
      \/ (eval_camp_rule brand_relation_brands r world = Some nil).
  Proof.
    intros.
    unfold eval_camp_rule.
    unfold camp_rule_type in H.
    generalize (@typed_camp_success_or_recoverable
                  m (mkWorld world)
                  (mkTWorld τworld) nil
                  Unit
                  τout
                  (camp_rule_to_camp r)
                  nil
                  dunit); intros.
    cut_to H1.
    - unfold eval_camp_rule_res.
      destruct H1.
      + destruct H1 as [x [eqq1 ?]].
        rewrite eqq1.
        left; eauto.
      + right. rewrite H1; trivial.
    - trivial.
    - econstructor.
    - trivial.
    - econstructor.
  Qed.

End TCAMPRule.

