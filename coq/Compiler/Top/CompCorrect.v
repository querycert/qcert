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

Require Import CompilerRuntime CompilerModel.
Module CompCorrect(model:CompilerModel).

  Require Import String List String EquivDec.
  
  Require Import BasicSystem.
  Require Import Pattern Rule.

  Require Import CompUtil CompFront.
  Require Import CompTop.
  Require Import EvalTop.

  Module runtime:=CompilerModelRuntime model.
  Module CF := CompFront runtime.
  Module CT := CompTop runtime.
  Module ET := EvalTop runtime.
  
  
  Hint Constructors data_normalized.

  (***************
   * NRA Section *
   ***************)

  Require Import NRAEnvRuntime.
  Require Import PatterntoNRA PatterntoNRAEnv.
  Require Import RuletoNRA RuletoNRAEnv.

  Local Open Scope algenv_scope.

  Definition optimizer_correct (optim:CT.optimizer) : Prop :=
    forall (h:list (string*string))
           (op:algenv)
           (d:data)
      (dn:data_normalized h d)
      (cenv:list (string*data))
      (dn_cenv:Forall (fun x => data_normalized h (snd x)) cenv)
      (env:data)
      (dn_env:data_normalized h env),
      h ⊢ₑ (optim op) @ₑ d ⊣ cenv;env = h ⊢ₑ op @ₑ d ⊣ cenv;env.
  
  (* Algebraic optimizers *)

  Require Import ROptimEnvFunc.

  Lemma optimizer_no_optim_correct :
    optimizer_correct CT.optimizer_no_optim.
  Proof.
    unfold optimizer_correct; reflexivity.
  Qed.

  Lemma optimizer_untyped_opt_correct :
    optimizer_correct CT.optimizer_untyped_opt.
  Proof.
    unfold optimizer_correct. intros.
    apply ROptimEnvFunc.optim_correctness; trivial.
  Qed.

  Lemma algenv_optimizer_equiv (optim:CT.optimizer) :
    optimizer_correct optim -> forall (op:algenv), (optim op) ≡ₑ op.
  Proof.
    unfold algenv_eq; intros.
    apply H; trivial.
  Qed.

  (* Compiler from CAMP to NRA+Env *)
  
  Lemma compile_pat_to_algenv_correct
        (optim:CT.optimizer)
        (p:pat)
        cenv
        (any:data)
        (d:data) :
    optimizer_correct optim ->
    forall (h:list (string*string))
      (dn_cenv:Forall (fun x => data_normalized h (snd x)) cenv),
    data_normalized h any ->
    data_normalized h d ->
      lift_failure (interp h cenv p nil d) = h ⊢ₑ (CT.compile_pat_to_algenv optim p) @ₑ d ⊣ cenv;any.
  Proof.
    unfold CT.compile_pat_to_algenv; intros.
    rewrite algenv_optimizer_equiv; trivial.
    rewrite pat_envtrans_correct.
    simpl.
    reflexivity.
  Qed.
  
  Lemma compile_nooptim_correct
        (h:list (string*string))
        (p:pat)
        cenv
        (any:data)
        (d:data) :
    Forall (fun x => data_normalized h (snd x)) cenv ->
    data_normalized h any ->
    data_normalized h d ->
    lift_failure (interp h cenv p nil d) = h ⊢ₑ (CT.compile_pat_to_algenv_no_optim p) @ₑ d ⊣ cenv;any.
  Proof.
    intros.
    apply compile_pat_to_algenv_correct; trivial.
    apply optimizer_no_optim_correct; trivial.
  Qed.

  Lemma compile_untyped_opt_correct
        (h:list (string*string))
        (p:pat)
        cenv
        (any:data)
        (d:data) :
    Forall (fun x => data_normalized h (snd x)) cenv ->
    data_normalized h any ->
    data_normalized h d ->
    lift_failure (interp h cenv p nil d) = h ⊢ₑ (CT.compile_pat_to_algenv_untyped_opt p) @ₑ d ⊣ cenv;any.
  Proof.
    intros.
    apply compile_pat_to_algenv_correct; trivial.
    apply optimizer_untyped_opt_correct; trivial.
  Qed.

  (* Compiler from Rules to NRA+Env *)
  
  Lemma compile_rule_to_algenv_correct
        (h:list (string*string))
        (optim:CT.optimizer)
        (r:rule)
        (world:list data) :
    Forall (data_normalized h) world ->
    optimizer_correct optim ->
    eval_rule h r world = lift_rule_failure (ET.algenv_eval_top h (CT.compile_rule_to_algenv optim r) world).
  Proof.
    unfold CT.compile_rule_to_algenv; intros.
    unfold ET.algenv_eval_top.
    rewrite algenv_optimizer_equiv; auto.
    - rewrite rule_trans_correct_r; reflexivity.
    - repeat (econstructor; eauto).
  Qed.
  
  Lemma compile_rule_nooptim_correct
        (h:list (string*string))
        (r:rule)
        (world: list data) :
    Forall (data_normalized h) world ->
    eval_rule h r world = lift_rule_failure (ET.algenv_eval_top h (CT.compile_rule_to_algenv_no_optim r) world).
  Proof.
    intros.
    apply compile_rule_to_algenv_correct; trivial.
    apply optimizer_no_optim_correct; trivial.
  Qed.

  Lemma compile_rule_untyped_opt_correct
        (h:list (string*string))
        (r:rule)
        (world: list data) :
    Forall (data_normalized h) world ->
    eval_rule h r world = lift_rule_failure (ET.algenv_eval_top h (CT.compile_rule_to_algenv_untyped_opt r) world).
  Proof.
    intros.
    apply compile_rule_to_algenv_correct; trivial.
    apply optimizer_untyped_opt_correct; trivial.
  Qed.

  (********************
   * Calculus Section *
   ********************)

  Require Import NNRCRuntime.
  Require Import NRAEnvtoNNRC NRewFunc.
  Require Import NNRCtoNNRCMR NRewMR.

  (* Calculus rewriter *)

  Definition rewriter_correct  (rew:CT.rewriter) : Prop :=
    forall (h:list(string*string)),
    forall (e:nrc),
      forall (world:list data),
        Forall (fun x => data_normalized h x) world ->
        ET.nrc_eval_top h (rew e) world = ET.nrc_eval_top h e world.
  
  Lemma rewriter_no_rew_correct : rewriter_correct CT.rewriter_no_rew.
  Proof.
    unfold rewriter_correct; intros. reflexivity.
  Qed.
 
  Lemma rewriter_simpl_rew_correct : rewriter_correct CT.rewriter_simpl_rew.
  Proof.
    unfold rewriter_correct; intros. apply head_rew_correctness.
    simpl; auto.
  Qed.
 
  (* Compiler from CAMP to NNRC *)
  
  Lemma compile_pat_to_nnrc_correct optim rew:
    optimizer_correct optim ->
    rewriter_correct rew ->
    forall (h:list (string*string)),
    forall (p:pat)
           world,
    Forall (fun x => data_normalized h x) world ->
      lift_failure (interp h (mkWorld world) p nil dunit)
      = ET.nrc_eval_top h (CT.compile_pat_to_nnrc optim rew p) world.
  Proof.
    Hint Resolve dnrec_sort.
    intros.
    unfold CT.compile_pat_to_nnrc.
    unfold rewriter_correct, ET.nrc_eval_top in *.
    rewrite <- interp_const_sort.
    rewrite (compile_pat_to_algenv_correct optim _ _ (drec nil)); try assumption; trivial.
    generalize (CT.compile_pat_to_algenv optim p); intros op.
    clear p optim H.
    rewrite H0; trivial; eauto 2.
    - rewrite <- (nraenv_sem_correct h op ((init_venv, drec nil) :: (init_vid, dunit) :: (mkConstants (rec_sort (mkWorld world)))) init_vid init_venv (rec_sort (mkWorld world)) dunit);
      unfold init_vid, init_venv; auto; simpl.
      congruence.
    - apply Forall_sorted.
      simpl.
      rewrite Forall_forall.
      intros.
      destruct x; simpl.
      elim H2; try contradiction; intros.
      inversion H3.
      constructor.
      assumption.
    - auto.
  Qed.

  Lemma compile_pat_to_nnrc_untyped_opt_correct:
    forall (h:list (string*string)),
    forall (p:pat)
           (world:list data),
      Forall (fun x => data_normalized h x) world ->
      lift_failure (interp h (mkWorld world) p nil dunit)
      = ET.nrc_eval_top h (CT.compile_pat_to_nnrc_untyped_opt p) world.
  Proof.
    unfold CT.compile_pat_to_nnrc_untyped_opt.
    apply compile_pat_to_nnrc_correct.
    - apply optimizer_untyped_opt_correct; trivial.
    - apply rewriter_simpl_rew_correct; trivial.
  Qed.
    
  (* Compiler from CAMP to NNRC *)
  
  Lemma compile_rule_to_nnrc_correct optim rew:
    optimizer_correct optim ->
    rewriter_correct rew ->
    forall (h:list (string*string)),
    forall (r:rule)
           (world:list data),
      Forall (data_normalized h) world ->
      eval_rule h r world
      = lift_rule_failure (ET.nrc_eval_top h (CT.compile_rule_to_nnrc optim rew r) world).
  Proof.
    intros.
    unfold CT.compile_rule_to_nnrc.
    unfold rewriter_correct, ET.nrc_eval_top in *.
    unfold runtime.compiler_foreign_runtime.
    rewrite (compile_rule_to_algenv_correct h optim r world); try assumption; eauto 2.
    generalize (CT.compile_rule_to_algenv optim r); intros op.
    clear r optim H.
    unfold ET.algenv_eval_top.
    rewrite <- (nraenv_sem_correct h op ((init_venv, drec nil) :: (init_vid, dunit) :: (mkConstants (mkWorld world))) init_vid init_venv); trivial;
      unfold init_vid, init_venv; auto; try congruence.
    rewrite H0; simpl; eauto 2.
  Qed.

  Lemma compile_rule_to_nnrc_topt_correct:
    forall (h:list (string*string)),
    forall (r:rule)
           (world:list data),
      Forall (data_normalized h) world -> 
      eval_rule h r world
      = lift_rule_failure (ET.nrc_eval_top h (CT.compile_rule_to_nnrc_untyped_opt r) world).
  Proof.
    unfold CT.compile_rule_to_nnrc_untyped_opt.
    apply compile_rule_to_nnrc_correct.
    apply optimizer_untyped_opt_correct.
    apply rewriter_simpl_rew_correct.
  Qed.

End CompCorrect.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
