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

Section RuletoNRAEnv.

  Require Import String.
  Require Import List.

  Require Import Utils BasicRuntime.
  Require Import NRAEnvRuntime.
  Require Import PatterntoNRA PatterntoNRAEnv.
  Require Import Rule RuletoNRA.

  Local Open Scope string_scope.
  Local Open Scope list_scope.

  Context {fruntime:foreign_runtime}.

  (* Rule parts *)

  Definition algenv_of_rule (r:rule) : algenv :=
    algenv_of_pat (rule_to_pattern r).

  Lemma rule_envtrans_correct h c rps bind d :
    lift_failure (interp h c (rule_to_pattern rps) bind d) =
    fun_of_algenv h c (algenv_of_rule rps) (drec bind) d.
  Proof.
    unfold algenv_of_rule.
    generalize (rule_to_pattern rps); intros.
    apply pat_envtrans_correct.
  Qed.

  Lemma rule_parts_envtrans_correct_r h c rps bind d :
      interp h c (rule_to_pattern rps) bind d =
      lift_pat_failure (fun_of_algenv h
                                      c 
                            (algenv_of_rule rps)
                            (drec bind) d).
  Proof.
    rewrite <- (rule_envtrans_correct _ ).
    generalize (rule_to_pattern rps); intros; simpl.
    destruct (interp h c p bind d); simpl; eauto.
  Qed.

  (* Rules *)
  Lemma rule_trans_correct_r (h:list (string*string)) (r:rule) (world:list data) :
    eval_rule h r world =
    lift_rule_failure (fun_of_algenv h (mkWorld world) (algenv_of_rule r) (drec nil) dunit).
  Proof.
    simpl; unfold eval_rule.
    generalize rule_envtrans_correct; intros.
    rewrite <- (H _); clear H.
    unfold eval_rule_res.
    match_destr.
  Qed.

  (* Aggregates *)

  Require Import RuleSugar.
  
  Definition algenv_of_aggregate (rules:rule->rule) (op:unaryOp) (secondMap:pat) (flatn:nat) : algenv :=
    algenv_of_pat (aggregate rules op secondMap flatn).

  Lemma aggregate_envtrans_correct h c rules op secondMap bind d (flatn:nat) :
    lift_failure (interp h c (aggregate rules op secondMap flatn) bind d) =
    fun_of_algenv h c (algenv_of_aggregate rules op secondMap flatn) (drec bind) d.
  Proof.
    unfold algenv_of_aggregate.
    apply pat_envtrans_correct.
  Qed.

  Lemma aggregate_envtrans_correct_r h c rules op secondMap bind d  (flatn:nat) :
    interp h c (aggregate rules op secondMap flatn) bind d =
    lift_pat_failure (fun_of_algenv h c (algenv_of_aggregate rules op secondMap flatn) (drec bind) d).
  Proof.
    rewrite <- (aggregate_envtrans_correct _).
    generalize (AGGREGATE rules DO op OVER secondMap FLATTEN flatn)%rule; intros.
    destruct (interp h c p bind d); simpl; eauto.
  Qed.

  (* Top-level translation call *)

  Definition translate_rule_to_algenv (r:rule) : algenv :=
    (* Produces the initial plan *)
    ANAppEnv (algenv_of_rule r) (ANConst (drec nil)).

End RuletoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
