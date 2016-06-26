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
Module TCompCorrect(model:CompilerModel).

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

  (********************
   * Calculus Section *
   ********************)

  Require Import NNRCRuntime.
  Require Import NRAEnvtoNNRC NRewFunc.
  Require Import NNRCtoNNRCMR NRewMR.

  (*****************
   * Typed Section *
   *****************)
  
  (* Typed Compiler from Rules to NRA+Env *)

  Require Import BasicTypes CAMPTypes NRAEnvTypes.
  Require Import TPatterntoNRAEnv.

  (* Note: the ability to prove this is still in question, but hopefully directly
     corresponds to what Topt is trying to prove *)
  Definition toptimizer_correct (optim:CT.optimizer) : Prop :=
    forall (p:algenv), p ⇒ optim p.
  
  (* Note: this was a little more painful than expected and relies on
     a few new lemmas to better encapsulate the typing of rules, as
     well as a change to the top-level semantics of rules (success
     doesn't go through only in case the result in a collection but in
     every case) *)

  Lemma tcompile_rule_to_algenv_correct (optim:CT.optimizer) {τworld τout:rtype} (world:list data) :
    toptimizer_correct optim ->
    forall (tr:{r:rule|rule_type τworld τout r}),
    bindings_type (mkWorld world) (mkTWorld τworld) ->
    (eval_rule brand_relation_brands (proj1_sig tr) world = lift_rule_failure (brand_relation_brands ⊢ₑ (CT.compile_rule_to_algenv optim (proj1_sig tr)) @ₑ dunit ⊣ (mkWorld world);(drec nil))
     /\ (algenv_type (mkTWorld τworld) (CT.compile_rule_to_algenv optim (proj1_sig tr))
         (Rec Closed nil eq_refl) Unit (Coll τout))).
  Proof.
    unfold CT.compile_rule_to_algenv; intros.
    unfold toptimizer_correct, talgenv_rewrites_to in H.
    unfold CT.CF.translate_rule_to_algenv.
    unfold rule_type in *.
    unfold algenv_of_rule.
    generalize (@typed_rule_correct model.compiler_basic_model τworld τout (proj1_sig tr) (proj2_sig tr) world H0).
    intros.
    generalize (rule_trans_correct_r brand_relation_brands (proj1_sig tr) world); intros.
    unfold algenv_of_rule in H2. rewrite H2 in *; clear H2.
    generalize (@algenv_of_rule_type_preserve model.compiler_basic_model τworld τout (proj1_sig tr) (proj2_sig tr)); intros.
    unfold algenv_of_rule in *.
    revert H1 H2.
    unfold runtime.compiler_foreign_runtime.
    generalize ((algenv_of_pat (rule_to_pattern (proj1_sig tr)))); intros p; intros.
    assert (typ2:(p ◯ₑ ‵[||]) ▷ Unit >=> Coll τout ⊣ mkTWorld τworld; Rec Closed nil eq_refl).
    - econstructor; eauto.
      econstructor; simpl.
      apply dtrec_full; econstructor.
    - destruct (H (p ◯ₑ ‵[||]) _ _ _ _ typ2); intros.
      split; try assumption.
      rewrite <- H4; trivial.
      + econstructor.
      + apply dtrec_full; repeat (econstructor; eauto).
  Qed.

  Lemma tcompile_rule_to_algenv_none_correct {τworld τout:rtype} (tr:{r:rule|@rule_type _ τworld τout r}) (world:list data) :
    bindings_type (mkWorld world) (mkTWorld τworld) ->
    eval_rule brand_relation_brands (proj1_sig tr) world = lift_rule_failure (brand_relation_brands ⊢ₑ (CT.tcompile_rule_to_algenv_none (proj1_sig tr)) @ₑ dunit ⊣  (mkWorld world);(drec nil)).
  Proof.
    apply tcompile_rule_to_algenv_correct.
    unfold toptimizer_correct, CT.optimizer_no_optim; simpl; intros; reflexivity.
  Qed.

  Require Import NNRCTypes.
  Require Import TNRAEnvtoNNRC.
  Require Import TOptimEnvFunc.
  
  Lemma tcompile_rule_to_algenv_topt_correct {τworld τout:rtype} (tr:{r:rule|rule_type τworld τout r}) (world:list data) :
    bindings_type (mkWorld world) (mkTWorld τworld) ->
    eval_rule brand_relation_brands (proj1_sig tr) world = lift_rule_failure (brand_relation_brands ⊢ₑ (CT.tcompile_rule_to_algenv_topt (proj1_sig tr)) @ₑ dunit ⊣  (mkWorld world);(drec nil)).
  Proof.
    intros.
    unfold CT.tcompile_rule_to_algenv_topt.
    apply (@tcompile_rule_to_algenv_correct toptim τworld τout world toptim_correctness tr); trivial.
  Qed.
    
  (* Typed compilation from rules to NNRC *)

  (* Note: only the algebra rewrites leverage types, the NNRC rewrites
  (at this point) are operating on the untyped form *)
  
  Definition trewriter_correct (rew:CT.rewriter) : Prop :=
    forall (e:nrc), tnrc_rewrites_to e (rew e).
  
  Lemma tcompile_rule_to_nnrc_correct {τworld τout:rtype} (optim:CT.optimizer) (rew:CT.rewriter):
    toptimizer_correct optim ->
    trewriter_correct rew ->
    forall (tr:{r:rule|rule_type τworld τout r}) (world:list data),
    bindings_type (mkWorld world) (mkTWorld τworld) ->
      eval_rule brand_relation_brands (proj1_sig tr) world
      = lift_rule_failure (ET.nrc_eval_top brand_relation_brands (CT.tcompile_rule_to_nnrc optim rew (proj1_sig tr)) world).
  Proof.
    intros.
    unfold CT.tcompile_rule_to_nnrc.
    unfold trewriter_correct, ET.nrc_eval_top in *.
    generalize (@tcompile_rule_to_algenv_correct optim τworld τout world H tr H1); intros.
    elim H2; clear H2; intros.
    rewrite H2.
    revert H3.
    generalize (CT.compile_rule_to_algenv optim (proj1_sig tr)); intros op; intros.
    unfold tnrc_rewrites_to in H0.
    specialize (H0 (algenv_to_nnrc op init_vid init_venv)
                   ((init_venv, Rec Closed nil eq_refl) :: (init_vid, Unit) ::
                                                          mkConstants (mkTWorld τworld))
                   (Coll τout)).
    cut_to H0; [ | eapply tnraenv_sem_correct; simpl; eauto ].
    elim H0; clear H0 H3.
    intros.
    rewrite <- H3.
    - rewrite <- (nraenv_sem_correct brand_relation_brands op
                      ((init_venv, drec nil) :: (init_vid, dunit) :: (mkConstants (mkWorld world)))
                      init_vid init_venv); simpl; trivial;
      unfold init_venv, init_vid; auto; try congruence.
    - unfold bindings_type in * .
      constructor; simpl.
      + split; trivial.
        apply bindings_type_has_type; trivial.
        econstructor.
      + constructor; simpl.
        * split; trivial.
          econstructor.
        * inversion H1; clear H1; subst.
          econstructor; simpl in * ; trivial.
          intuition.
    - reflexivity.
  Qed.

  Lemma tcompile_rule_to_nnrc_none_correct {τworld τout:rtype}:
    forall (tr:{r:rule|rule_type τworld τout r}) (world:list data),
    bindings_type (mkWorld world) (mkTWorld τworld) ->
      eval_rule brand_relation_brands (proj1_sig tr) world
      = lift_rule_failure (ET.nrc_eval_top brand_relation_brands (CT.tcompile_rule_to_nnrc_none (proj1_sig tr)) world).
  Proof.
    unfold CT.tcompile_rule_to_nnrc_none.
    apply tcompile_rule_to_nnrc_correct.
    unfold toptimizer_correct, CT.optimizer_no_optim; simpl; intros; try reflexivity.
    unfold trewriter_correct. reflexivity.
  Qed.

  Require Import TRewFunc.
  
  Lemma tcompile_rule_to_nnrc_topt_correct {τworld τout:rtype}:
    forall (tr:{r:rule|rule_type τworld τout r}) (world:list data),
    bindings_type (mkWorld world) (mkTWorld τworld) ->
      eval_rule brand_relation_brands (proj1_sig tr) world
      = lift_rule_failure (ET.nrc_eval_top brand_relation_brands (CT.tcompile_rule_to_nnrc_topt (proj1_sig tr)) world).
  Proof.
    unfold CT.tcompile_rule_to_nnrc_topt.
    apply tcompile_rule_to_nnrc_correct.
    - unfold toptimizer_correct; simpl; intros.
      apply toptim_correctness.
    - unfold rewriter_correct; simpl; intros.
      unfold ET.nrc_eval_top.
      unfold trewriter_correct; intros.
      apply trew_correctness.
  Qed.

End CompCorrect.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
