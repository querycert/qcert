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
Require Import Setoid.
Require Import Equivalence.
Require Import CoqLibAdd.
Require Import OptimizerStep.

Section OptimizerLogger.
  
  Class optimizer_logger (Name:Set) (D:Set) 
    := mk_optimizer_logger {
           optimizer_logger_token_type:Set
           ; logStartPass (name:Name) (input:D) : optimizer_logger_token_type
           ; logStep (t:optimizer_logger_token_type) (name:Name) (input output:D) :
               optimizer_logger_token_type
           ; logEndPass (t:optimizer_logger_token_type) (output:D):
               optimizer_logger_token_type
         }.

  (* This it to try and ``trick'' the system so that 
     the evaluation is extracted and run for its effects
   *)
  Definition hide_use {A B} (x:A) (y:B) := y.
  Lemma hide_use_eq {A B} (x:A) (y:B) : hide_use x y = y.
  Proof.
    reflexivity.
  Qed.
  Opaque hide_use.
  
  Instance silent_optimizer_logger (Name:Set) (D:Set) : optimizer_logger Name D
    :=
      {
        optimizer_logger_token_type := bool
        ; logStartPass name input := true
        ; logStep t name input output := t
        ; logEndPass t output := t
      } .

  Definition run_optimizer_step {lang:Set} 
             {logger:optimizer_logger string lang}
             (step:OptimizerStep lang)
             (input:optimizer_logger_token_type*lang)
    : optimizer_logger_token_type*lang
    := let res := (optim_step_step step) (snd input) in
       let log := logStep (fst input) (optim_step_name step) (snd input) res in
       (log, res).

  Lemma run_optimizer_step_result
        {lang:Set} 
        {logger:optimizer_logger string lang}
        (step:OptimizerStep lang)
        (input:optimizer_logger_token_type*lang) :
    snd (run_optimizer_step step input) = (optim_step_step step) (snd input).
  Proof.
    unfold run_optimizer_step.
    simpl; reflexivity.
  Qed.

  Definition run_optimizer_steps
             {lang:Set} 
             {logger:optimizer_logger string lang}
             (passName:string)
             (steps:list (OptimizerStep lang))
             (input:lang) : lang
    := let tok := logStartPass passName input in
       let '(tok2, res) := fold_right run_optimizer_step (tok,input) steps in
       let tok := logEndPass tok2 res in
       hide_use tok res.

  Lemma run_optimizer_steps_fold_correct
        {lang:Set}
        {R:relation lang}
        {pre:PreOrder R}
        {logger:optimizer_logger string lang}
        (steps:list (OptimizerStep lang))
        (tok:optimizer_logger_token_type)
        (input:lang) :
    optim_list_correct R steps ->
    R input (snd (fold_right run_optimizer_step (tok,input) steps)).
  Proof.
    revert input tok.
    (* reverse induction *)
    induction steps using rev_ind; simpl; intros input tok pf.
    - reflexivity.
    - rewrite fold_right_app.
      simpl.
      apply Forall_app_inv in pf.
      destruct pf as [pf1 pf2].
      invcs pf2.
      etransitivity; eauto.
  Qed.
  
  Lemma run_optimizer_steps_correct
        {lang:Set}
        {R:relation lang}
        {pre:PreOrder R}
        {logger:optimizer_logger string lang}
        (passName:string)
        (steps:list (OptimizerStep lang))
        (input:lang) :
    optim_list_correct R steps ->
    R input (run_optimizer_steps passName steps input).
  Proof.
    unfold run_optimizer_steps.
    simpl.
    intros pf.
    generalize (run_optimizer_steps_fold_correct steps (logStartPass passName input) input pf).
    match_destr.
  Qed.

  Definition run_phase {lang:Set}
             {logger:optimizer_logger string lang}
             (mapdeep:(lang->lang)->lang->lang)
             (cost:lang->nat)
             (lang_optim_list:list (OptimizerStep lang))
             (phaseName:string)
             (optims:list string)
             (iterationsBetweenCostCheck:nat)
    : lang -> lang :=
    iter_cost
      (iter
         (mapdeep
            (run_optimizer_steps phaseName
                                 (project_optims lang_optim_list optims)))
         iterationsBetweenCostCheck) cost.

  Lemma run_phase_correctness {lang:Set} {R:relation lang} {pre:PreOrder R}
        {logger:optimizer_logger string lang}
        {mapdeep:(lang->lang)->lang->lang}
        (mapdeep_correct:
           forall f, (forall a, R a (f a)) -> forall a, R a (mapdeep f a))
        (cost:lang->nat)
        {lang_optim_list:list (OptimizerStep lang)}
        (lang_optim_list_correct:optim_list_correct R lang_optim_list)
        (phaseName:string)
        (optims:list string)
        (iterationsBetweenCostCheck:nat) p :
    R p (run_phase mapdeep cost lang_optim_list
                   phaseName optims iterationsBetweenCostCheck p).
  Proof.
    unfold run_phase.
    apply iter_cost_trans; trivial; intros.
    apply iter_trans; trivial; intros.
    apply mapdeep_correct; intros.
    apply run_optimizer_steps_correct.
    apply project_optims_list_correct.
    apply lang_optim_list_correct.
  Qed.

  Section multiphase.
    Definition optim_phase_config : Set :=
      (string * list string * nat).
    Definition optim_phases_config : Set :=
      list optim_phase_config.
    
    Fixpoint run_phases {lang:Set}
             {logger:optimizer_logger string lang}
             (mapdeep:(lang->lang)->lang->lang)
             (cost:lang->nat)
             (lang_optim_list:list (OptimizerStep lang))
             (opc: optim_phases_config)
             (q:lang)
      : lang :=
      match opc with
      | nil => q
      | (phaseName,optims,iterationsBetweenCostCheck) :: opc' =>
        let q :=
            run_phase mapdeep cost lang_optim_list phaseName optims iterationsBetweenCostCheck q
        in
        run_phases mapdeep cost lang_optim_list opc' q
      end.
    
    Lemma run_phases_correctness {lang:Set} {R:relation lang} {pre:PreOrder R}
          {logger:optimizer_logger string lang}
          {mapdeep:(lang->lang)->lang->lang}
          (mapdeep_correct:
             forall f, (forall a, R a (f a)) -> forall a, R a (mapdeep f a))
          (cost:lang->nat)
          {lang_optim_list:list (OptimizerStep lang)}
          (lang_optim_list_correct:optim_list_correct R lang_optim_list)
          (opc: optim_phases_config) p :
      R p (run_phases mapdeep cost lang_optim_list
                      opc p).
    Proof.
      revert p.
      induction opc; simpl; [reflexivity|]; intros.
      destruct a; simpl.
      destruct p0; simpl.
      specialize (IHopc (run_phase mapdeep cost lang_optim_list s l n p)).
      generalize (run_phase_correctness mapdeep_correct cost lang_optim_list_correct s l n p).
      intros; destruct pre; eauto.
    Qed.
  End multiphase.

  Definition run_phase3 {E S T:Set}
             {logger_e:optimizer_logger string E}
             {logger_s:optimizer_logger string S}
             {logger_t:optimizer_logger string T}
             (mapdeep:
                (E -> E)->
                (S -> S) ->
                (T -> T) ->
                T -> T)
             (cost:T->nat)
             (optim_list_e:list (OptimizerStep E))
             (optim_list_s:list (OptimizerStep S))
             (optim_list_t:list (OptimizerStep T))
             (phaseName:string)
             (optims_e:list string)
             (optims_s:list string)
             (optims_t:list string)
             (iterationsBetweenCostCheck:nat)
    : T -> T :=
    iter_cost
      (iter
         (mapdeep
            (run_optimizer_steps phaseName
                                 (project_optims optim_list_e optims_e))
            (run_optimizer_steps phaseName
                                 (project_optims optim_list_s optims_s))
            (run_optimizer_steps phaseName
                                 (project_optims optim_list_t optims_t)))
         iterationsBetweenCostCheck) cost.


  Lemma run_phase3_correctness
        {E S T:Set}
        {R_e:relation E} {R_s:relation S} {R_t:relation T}
        {pre_e:PreOrder R_e} {pre_s:PreOrder R_s} {pre_t:PreOrder R_t}
        {logger_e:optimizer_logger string E}
        {logger_s:optimizer_logger string S}
        {logger_t:optimizer_logger string T}
        {mapdeep:
           (E -> E)->
           (S -> S) ->
           (T -> T) ->
           T -> T}
        (mapdeep_correct:
           forall f_e f_s f_t, (forall e, R_e e (f_e e)) ->
                               (forall s, R_s s (f_s s)) ->
                               (forall t, R_t t (f_t t)) ->
                               forall t, R_t t (mapdeep f_e f_s f_t t))
        (cost:T->nat)
        {optim_list_e:list (OptimizerStep E)}
        {optim_list_s:list (OptimizerStep S)}
        {optim_list_t:list (OptimizerStep T)}
        (optim_list_e_correct:optim_list_correct R_e optim_list_e)
        (optim_list_s_correct:optim_list_correct R_s optim_list_s)
        (optim_list_t_correct:optim_list_correct R_t optim_list_t)
        (phaseName:string)
        (optims_e:list string)
        (optims_s:list string)
        (optims_t:list string)
        (iterationsBetweenCostCheck:nat) p :
    R_t p (run_phase3 mapdeep cost
                      optim_list_e
                      optim_list_s
                      optim_list_t
                      phaseName
                      optims_e
                      optims_s
                      optims_t
                      iterationsBetweenCostCheck p).
  Proof.
    unfold run_phase3.
    apply iter_cost_trans; trivial; intros.
    apply iter_trans; trivial; intros.
    apply mapdeep_correct; intros
    ; apply run_optimizer_steps_correct
    ; apply project_optims_list_correct
    ; eauto.
  Qed.

  Section multiphase3.
    Definition optim_phase3_config : Set :=
      (string * list string * list string * list string * nat).
    Definition optim_phases3_config : Set :=
      list optim_phase3_config.
    
    Fixpoint run_phases3 {E S T:Set}
             {logger_e:optimizer_logger string E}
             {logger_s:optimizer_logger string S}
             {logger_t:optimizer_logger string T}
             (mapdeep:
                (E -> E)->
                (S -> S) ->
                (T -> T) ->
                T -> T)
             (cost:T->nat)
             (optim_list_e:list (OptimizerStep E))
             (optim_list_s:list (OptimizerStep S))
             (optim_list_t:list (OptimizerStep T))
             (opc:optim_phases3_config)
             (q:T)
      : T :=
      match opc with
      | nil => q
      | (phaseName,optims_e,optims_s, optims_t, iterationsBetweenCostCheck) :: opc' =>
        let q :=
            run_phase3 mapdeep cost optim_list_e optim_list_s optim_list_t phaseName optims_e optims_s optims_t iterationsBetweenCostCheck q
        in
        run_phases3 mapdeep cost optim_list_e optim_list_s optim_list_t opc' q
      end.
    
    Lemma run_phases3_correctness
          {E S T:Set}
          {R_e:relation E} {R_s:relation S} {R_t:relation T}
          {pre_e:PreOrder R_e} {pre_s:PreOrder R_s} {pre_t:PreOrder R_t}
          {logger_e:optimizer_logger string E}
          {logger_s:optimizer_logger string S}
          {logger_t:optimizer_logger string T}
          (mapdeep:
             (E -> E)->
             (S -> S) ->
             (T -> T) ->
             T -> T)
          (mapdeep_correct:
             forall f_e f_s f_t, (forall e, R_e e (f_e e)) ->
                                 (forall s, R_s s (f_s s)) ->
                                 (forall t, R_t t (f_t t)) ->
                                 forall t, R_t t (mapdeep f_e f_s f_t t))
          (cost:T->nat)
          {optim_list_e:list (OptimizerStep E)}
          {optim_list_s:list (OptimizerStep S)}
          {optim_list_t:list (OptimizerStep T)}
          (optim_list_e_correct:optim_list_correct R_e optim_list_e)
          (optim_list_s_correct:optim_list_correct R_s optim_list_s)
          (optim_list_t_correct:optim_list_correct R_t optim_list_t)
          (opc: optim_phases3_config) p :
      R_t p (run_phases3 mapdeep cost optim_list_e optim_list_s optim_list_t
                         opc p).
    Proof.
      revert p.
      induction opc; simpl; [reflexivity | ]; intros.
      destruct a as [[[[phaseName optims_e] optims_s] optims_t] iterations]; simpl.
      specialize (IHopc (run_phase3 mapdeep cost optim_list_e optim_list_s optim_list_t phaseName optims_e optims_s optims_t iterations p)).
      generalize (run_phase3_correctness mapdeep_correct cost optim_list_e_correct optim_list_s_correct optim_list_t_correct phaseName optims_e optims_s optims_t iterations p).
      intros; destruct pre_t; eauto.
    Qed.

  End multiphase3.

End OptimizerLogger.

