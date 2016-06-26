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

Section RuletoNRA.

  Require Import String.
  Require Import List.

  Require Import Utils BasicRuntime.
  Require Import NRARuntime.
  Require Import Rule.
  Require Import PatterntoNRA.
  
  Local Open Scope string_scope.
  Local Open Scope list_scope.

  Context {fruntime:foreign_runtime}.

  (* Rule parts *)

  Definition alg_of_rule (r:rule) : alg :=
    alg_of_pat (rule_to_pattern r).

  Lemma rule_trans_correct {h:list(string*string)} c rps bind d :
    lift_failure (interp h c (rule_to_pattern rps) bind d) =
    fun_of_alg h (alg_of_rule rps) (pat_context_data (drec (rec_sort c)) (drec bind) d).
  Proof.
    unfold alg_of_rule.
    generalize (rule_to_pattern rps); intros.
    apply pat_trans_correct.
  Qed.

  Lemma rule_parts_trans_correct_r {h:list(string*string)} c rps bind d :
      interp h c (rule_to_pattern rps) bind d =
      lift_pat_failure (fun_of_alg h
                            (alg_of_rule rps)
                            (pat_context_data (drec (rec_sort c)) (drec bind) d)).
  Proof.
    rewrite <- rule_trans_correct.
    generalize (rule_to_pattern rps); intros; simpl.
    destruct (interp h c p bind d); eauto.
  Qed.

  (* Rules *)

  Definition lift_rule_failure (d : option data) :=
    match d with
      | Some (dcoll nil) => Some nil
      | Some (dcoll (l::nil)) => Some (l::nil)
      | _ => None
    end.

  Definition rule_trans (r:rule) : alg :=
    AUnop AFlatten
          (AMap (alg_of_rule r)
                (AUnop AColl (pat_context AID (AConst (drec nil))
                                          (AConst dunit)))).
  
  Lemma rule_trans_correct_r {h:list(string*string)} (r:rule) (world:list data) :
    eval_rule h r world =
    lift_rule_failure (fun_of_alg h (rule_trans r) (drec (mkWorld world))).
  Proof.
    simpl; unfold eval_rule.
    generalize (@rule_trans_correct h (mkWorld world)); intros.
    unfold pat_context_data in *.
    rewrite <- H; clear H.
    unfold eval_rule_res.
    unfold mkWorld.
    match_destr.
  Qed.

  (* Aggregates *)

  Require Import RuleSugar.
  
  Definition alg_of_aggregate (rules:rule->rule) (op:unaryOp) (secondMap:pat) (nflat:nat): alg :=
    alg_of_pat (aggregate rules op secondMap nflat).

  Lemma aggregate_trans_correct {h:list(string*string)} c rules op secondMap bind d nflat :
    lift_failure (interp h c (aggregate rules op secondMap nflat) bind d) =
    fun_of_alg h (alg_of_aggregate rules op secondMap nflat) (pat_context_data (drec (rec_sort c)) (drec bind) d).
  Proof.
    unfold alg_of_aggregate.
    apply pat_trans_correct.
  Qed.

  Lemma aggregate_trans_correct_r {h:list(string*string)} c rules op secondMap bind d nflat:
    interp h c (aggregate rules op secondMap nflat) bind d =
    lift_pat_failure (fun_of_alg h (alg_of_aggregate rules op secondMap nflat) (pat_context_data (drec (rec_sort c)) (drec bind) d)).
  Proof.
    rewrite <- aggregate_trans_correct.
    generalize (AGGREGATE rules DO op OVER secondMap FLATTEN nflat)%rule; intros.
    destruct (interp h c p bind d); eauto.
  Qed.    

End RuletoNRA.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
