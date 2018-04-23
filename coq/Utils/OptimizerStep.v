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

(* This includes some rewrites/simplification rules for the Nested relational calculus *)

Require Import String.
Require Import List.
Require Import Setoid.
Require Import Equivalence.
Require Import EquivDec.
Require Import CoqLibAdd.
Require Import ListAdd.

Section OptimizerStep.

  Record OptimizerStep (lang:Set) : Set :=
    mkOptimizerStep {
        optim_step_name : String.string
        ; optim_step_description : String.string
        ; optim_step_lemma : String.string
        ; optim_step_step (input:lang): lang
      }.
  
  Global Arguments mkOptimizerStep {lang} optim_step_name optim_step_description optim_step_lemma optim_step_step.
  Global Arguments optim_step_name {lang} o.
  Global Arguments optim_step_description {lang} o.
  Global Arguments optim_step_lemma {lang} o.
  Global Arguments optim_step_step {lang} o input.
  
  Record OptimizerStepModel {lang:Set} (R:relation lang) :=
    mkOptimizerStepModel {
        optim_step_model_step : OptimizerStep lang
        ; optim_step_model_step_correct (input:lang): R input (optim_step_step optim_step_model_step input)
      }.
  
  Global Arguments mkOptimizerStepModel {lang} {R} optim_step_model_step optim_step_model_step_correct.

  (* Properties about optimization lists *)

  (* an optimization model list has proofs for all optimizations in the optimization list *)
  Definition optim_model_list_complete {lang:Set} {R:relation lang}
             (optim_list:list (OptimizerStep lang))
             (optim_correct_list :list (OptimizerStepModel R))
    := forall x,
      In x optim_list ->
      exists y,
        In y optim_correct_list
        /\ optim_step_model_step _ y = x.

  Definition optim_list_correct {lang:Set} (R:relation lang)
             (optim_list:list (OptimizerStep lang))
    := Forall (fun o => forall input, R input (optim_step_step o input)) optim_list.

  Lemma optim_list_correct_from_model {lang:Set} {R:relation lang}
        {optim_list:list (OptimizerStep lang)}
        {optim_correct_list :list (OptimizerStepModel R)} :
    optim_model_list_complete optim_list optim_correct_list ->
    optim_list_correct R optim_list.
  Proof.
    unfold optim_model_list_complete, optim_list_correct.
    rewrite Forall_forall.
    intros pf ? inn.
    destruct (pf _ inn) as [cor [_ ?]].
    subst.
    apply optim_step_model_step_correct.
  Qed.
    
  (* The optim_correct_list_complete_prover tactic defined below can be used
      to prove optim_model_list_complete statements over constant lists *)

  (* The list of names in an optimization list does not have duplicates *)
  Definition optim_list_distinct {lang:Set} 
             (optim_list:list (OptimizerStep lang))
    := NoDup (map optim_step_name optim_list).

  Lemma optim_list_distinct_dec {lang:Set} 
        (optim_list:list (OptimizerStep lang))
    : {optim_list_distinct optim_list} + {~ optim_list_distinct optim_list}.
  Proof.
    apply NoDup_dec.
  Defined.

  Definition optim_list_distinct_holds {lang:Set} 
             (optim_list:list (OptimizerStep lang))
    := holds (optim_list_distinct_dec optim_list).

  Lemma optim_list_distinct_prover {lang:Set} 
        (optim_list:list (OptimizerStep lang))
        (pf:optim_list_distinct_holds optim_list) :
    optim_list_distinct optim_list.
  Proof.
    generalize (optim_list_distinct_dec optim_list).
    unfold optim_list_distinct_holds, holds, is_true in *.
    match_destr_in pf.
  Qed.

  (* Looking up an optimization by name *)
  Fixpoint optim_lookup {lang:Set} 
           (optim_list:list (OptimizerStep lang)) (name:string)
    : option (OptimizerStep lang)
    := match optim_list with
       | nil => None
       | opt::rest =>
         if optim_step_name opt == name
         then Some opt
         else optim_lookup rest name
       end.

  Lemma optim_lookup_name_correct {lang:Set} 
           (optim_list:list (OptimizerStep lang)) (name:string) (o:OptimizerStep lang)
    : optim_lookup optim_list name = Some o -> optim_step_name o = name.
  Proof.
    induction optim_list; simpl; intros eqq.
    - invcs eqq.
    - match_destr_in eqq.
      + invcs eqq; trivial.
      + auto.
  Qed.

  Lemma optim_lookup_some_in {lang:Set} 
           (optim_list:list (OptimizerStep lang)) (name:string) (o:OptimizerStep lang)
    : optim_lookup optim_list name = Some o -> In o optim_list.
  Proof.
    induction optim_list; simpl; intros eqq.
    - invcs eqq.
    - match_destr_in eqq.
      + invcs eqq; auto.
      + auto.
  Qed.

    Lemma optim_lookup_none_nin {lang:Set} 
           (optim_list:list (OptimizerStep lang)) (name:string)
      : optim_lookup optim_list name = None ->
        forall o, In o optim_list -> optim_step_name o <> name.
  Proof.
    induction optim_list; simpl; intros eqq.
    - intuition.
    - match_destr_in eqq.
      intros o [eqq2 | inn].
      + subst; intuition.
      + auto.
  Qed.

  Definition optim_lookup_as_list {lang:Set} 
           (optim_list:list (OptimizerStep lang)) (name:string)
    : list (OptimizerStep lang)
    := match optim_lookup optim_list name with
       | None => nil
       | Some res => res::nil
       end.

    (* Given a list of optimizations and candidate optimization names, 
     partition the list into 
     known optimization names and
     unknown optimization names *)
  Definition valid_optims {lang:Set} 
           (optim_list:list (OptimizerStep lang)) (names:list string) :
    list string * list string
    := partition
         (fun x => if optim_lookup optim_list x then true else false)
         names .
  
  (* Just skip invalid specifications *)
  Definition project_optims {lang:Set} 
           (optim_list:list (OptimizerStep lang)) (names:list string)
    := flat_map (optim_lookup_as_list optim_list) names.

  Lemma project_optims_incl {lang:Set} 
        (optim_list:list (OptimizerStep lang)) (names:list string) :
    incl (project_optims optim_list names) optim_list.
  Proof.
    unfold project_optims.
    red; intros o inn.
    apply in_flat_map in inn.
    destruct inn as [name [inn inl]].
    unfold optim_lookup_as_list in inl.
    match_case_in inl; [intros ? eqq | intros eqq]
    ; rewrite eqq in inl; simpl in *; intuition.
    subst.
    apply optim_lookup_some_in in eqq; trivial.
  Qed.
        
  Lemma project_optims_model_list_complete {lang:Set} {R:relation lang}
        {optim_list:list (OptimizerStep lang)}
        {optim_correct_list:list (OptimizerStepModel R)}
        (pf:optim_model_list_complete optim_list optim_correct_list)
        (names:list string)
    : optim_model_list_complete
        (project_optims optim_list names)
        optim_correct_list.
  Proof.
    red; intros o inn.
    apply project_optims_incl in inn.
    auto.
  Qed.

    Lemma project_optims_list_correct {lang:Set} {R:relation lang}
        {optim_list:list (OptimizerStep lang)}
        (pf:optim_list_correct R optim_list)
        (names:list string)
    : optim_list_correct R
        (project_optims optim_list names).
    Proof.
      unfold optim_list_correct in *.
      rewrite Forall_forall in *.
      intros ? inn.
      apply project_optims_incl in inn.
      auto.
    Qed.
  
End OptimizerStep.

Ltac optim_correct_list_complete_try_pf_match pf step
  := match eval simpl in (optim_step_model_step _ pf) with
     | step => idtac
     end.

Ltac optim_correct_list_complete_pf_finder step l
  := match l with
     | (?pf = _) \/ ?rest =>
       (optim_correct_list_complete_try_pf_match pf step; instantiate (1:=pf); (split; tauto; simpl; trivial))
       || (optim_correct_list_complete_pf_finder step rest)
     | (?pf = _) =>  (optim_correct_list_complete_try_pf_match pf step; instantiate (1:=pf); (split; tauto; simpl; trivial))
     end.

Ltac optim_correct_list_complete_step steps
  := match type of steps with
     | ?step \/ ?rest => 
       destruct steps as [? | steps]
       ; [eexists
          ; match step with
              ?name = _ => 
              match goal with
                [|- ?l /\ ?pf ] =>
                optim_correct_list_complete_pf_finder name l
              end
            end | idtac]
     | False => inversion steps
     end.


(* This tactic can be used to prove lemmas about  optim_model_list_complete *)
Ltac optim_correct_list_complete_prover :=
  unfold optim_model_list_complete; simpl; intros ? steps
  ; repeat optim_correct_list_complete_step steps.

