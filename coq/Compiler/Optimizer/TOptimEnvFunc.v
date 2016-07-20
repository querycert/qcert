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

Section TOptimEnvFunc.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.
  Require Import String List ListSet.

  Require Import Utils BasicSystem.
  Require Import RAlgEnv RAlgEnvIgnore RAlgEnvEq ROptimEnv.
  Require Import TDomain TAlgEnv TAlgEnvEq TOptimEnv.
  Require Import ROptimEnvFunc.
  Require Import OptimizerLogger.

  Open Scope algenv_scope.
  
  (* *************************** *)

  Ltac tcorrectness_prover :=
          simpl; repeat progress (try match goal with
        | [|- context [match ?p with | _ => _ end] ] => destruct p
      end; try reflexivity; try unfold Equivalence.equiv in *; try subst).

  Ltac tprove_correctness p :=
    destruct p;
    tcorrectness_prover.

  (****************)

  Lemma talgenv_rewrites_to_trans {model:basic_model} p1 p2 p3:
    p1 ⇒ p2 -> p2 ⇒ p3 -> p1 ⇒ p3.
  Proof.
    apply transitivity.
  Qed.

  Lemma AUX {model:basic_model} f p p':
    (forall p, p ⇒ f p) -> p ⇒ p' -> p ⇒ f p'.
  Proof.
    intros.
    rewrite H0 at 1.
    rewrite (H p') at 1.
    reflexivity.
  Qed.

  Definition talgenv_map {fruntime:foreign_runtime} := ROptimEnvFunc.algenv_map.

  Lemma talgenv_map_correctness {model:basic_model}:
    forall f: algenv -> algenv,
    forall p: algenv,
      (forall p', p' ⇒ f p') -> p ⇒ talgenv_map f p.
  Proof.
    intros.
    algenv_cases (induction p) Case; try solve [simpl; apply Hf]; simpl;
    try reflexivity;
    try (rewrite (H p1) at 1; rewrite (H p2) at 1; reflexivity);
    try rewrite (H p) at 1; try reflexivity.
  Qed.

  (* Java equivalent: NraOptimizer.talgenv_map_deep *)  
  Definition talgenv_map_deep {fruntime:foreign_runtime} := ROptimEnvFunc.algenv_map_deep.
  
  Lemma algenv_map_deep_correctness {model:basic_model}:
    forall f: algenv -> algenv,
    forall p: algenv,
      (forall p', p' ⇒ f p') -> p ⇒ talgenv_map_deep f p.
  Proof.
    intros f p Hf.
    algenv_cases (induction p) Case; try solve [simpl; apply Hf];
    try reflexivity; simpl;
    try (rewrite IHp1 at 1; rewrite IHp2 at 1; rewrite Hf at 1; reflexivity);
    rewrite IHp at 1; rewrite Hf at 1; reflexivity.
  Qed.

  Lemma optim_iter_correctness {model:basic_model} optim n p:
    (forall p', p' ⇒ optim p') -> p ⇒ ROptimEnvFunc.optim_iter optim n p.
  Proof.
    generalize p; clear p.
    induction n; try reflexivity.
    intros p Hoptim.
    simpl.
    apply AUX.
    - clear p; intros p.
      apply IHn.
      assumption.
    - apply Hoptim.
  Qed.
  Hint Rewrite @optim_iter_correctness : optim_correct.

  Lemma optim_cost_correctness {model:basic_model} optim cost p:
    (forall p', p' ⇒ optim p') -> p ⇒ optim_cost optim cost p.
  Proof.
    intros Hoptim.
    functional induction optim_cost optim cost p.
    - apply (talgenv_rewrites_to_trans p (optim p)).
      + apply Hoptim.
      + apply IHa.
    - reflexivity.
  Qed.
  Hint Rewrite @optim_cost_correctness : optim_correct.

  Lemma optim_size_correctness {model:basic_model} optim p:
    (forall p', p' ⇒ optim p') -> p ⇒ optim_size optim p.
  Proof.
    intros Hoptim.
    unfold optim_size.
    apply optim_cost_correctness.
    assumption.
  Qed.
  Hint Rewrite @optim_size_correctness : optim_correct.

  (****************)

  (* P1 ∧ P2 ⇒ P2 ∧ P1 *)

  Definition tand_comm_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANBinop AAnd op1 op2 => ANBinop AAnd op2 op1
      | _ => p
    end.

  Lemma tand_comm_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tand_comm_fun p.
  Proof.
    tprove_correctness p.
    apply tand_comm_arrow.
  Qed.
  Hint Rewrite @tand_comm_fun_correctness : optim_correct.


  (* σ{P1 ∧ P2}(P) ⇒ σ{P2 ∧ P1}(P) *) (* XXX Why neessary ? *)

  Definition tselect_and_comm_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANSelect (ANBinop AAnd op1 op2) op =>
        ANSelect (ANBinop AAnd op2 op1) op
      | _ => p
    end.

  Lemma tselect_and_comm_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tselect_and_comm_fun p.
  Proof.
    tprove_correctness p.
    apply tselect_and_comm_arrow.
  Qed.
  Hint Rewrite @tselect_and_comm_fun_correctness : optim_correct.

  (* σ{P1}(σ{P2}(P3)) ⇒ σ{P2 ∧ P1}(P3)) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tselect_and_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANSelect op1 (ANSelect op2 op) =>
        ANSelect (ANBinop AAnd op2 op1) op
      | _ => p
    end.

  Lemma tselect_and_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tselect_and_fun p.
  Proof.
    tprove_correctness p.
    apply tselect_and_arrow.
  Qed.
  Hint Rewrite @tselect_and_fun_correctness : optim_correct.

  (* [ a1 : p1; a2 : p2 ].a2 ⇒ p2 *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tenvdot_from_duplicate_r_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANUnop (ADot s2)
               (ANBinop AConcat (ANUnop (ARec s1) op1) (ANUnop (ARec s2') op2)) =>
        if s2 == s2' then
          op2
        else
          p
      | _ => p
    end.

  Lemma tenvdot_from_duplicate_r_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tenvdot_from_duplicate_r_fun p.
  Proof.
    tprove_correctness p. 
    apply tenvdot_from_duplicate_r_arrow.
  Qed.
  Hint Rewrite @tenvdot_from_duplicate_r_fun_correctness : optim_correct.

  (* [ a1 : p1; a2 : p2 ].a1 ⇒ p1 *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tenvdot_from_duplicate_l_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANUnop (ADot s1)
               (ANBinop AConcat (ANUnop (ARec s1') op1) (ANUnop (ARec s2) op2)) =>
        if (s1 <> s2) then
          if s1 == s1' then op1
          else p
        else p
      | _ => p
    end.

  Lemma tenvdot_from_duplicate_l_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tenvdot_from_duplicate_l_fun p.
  Proof.
    tprove_correctness p. 
    apply tenvdot_from_duplicate_l_arrow.
    assumption.
  Qed.
  Hint Rewrite @tenvdot_from_duplicate_l_fun_correctness : optim_correct.


  (* ♯flatten({ p }) ⇒ p when p's output type is a collection *)
  (* Java equivalent: NraOptimizer.[same] *)
  Definition tenvflatten_coll_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANUnop AFlatten (ANUnop AColl p) => p
      | _ => p
    end.

  Lemma tenvflatten_coll_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tenvflatten_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tenvflatten_coll_arrow.
  Qed.
  Hint Rewrite @tenvflatten_coll_fun_correctness : optim_correct.

    (* p ⊕ [] ⇒ p when p returns a record *)
  (* Java equivalent: NraOptimizer.[same] *)
  Definition tconcat_empty_record_r_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      |  ANBinop AConcat p (ANConst (drec [])) =>
        p
      | _ => p
    end.

  Lemma tconcat_empty_record_r_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tconcat_empty_record_r_fun p.
  Proof.
    tprove_correctness p.
    apply tconcat_empty_record_r_arrow.
  Qed.
  Hint Rewrite @tconcat_empty_record_r_fun_correctness : optim_correct.

  (* [] ⊕ p ⇒ p when p returns a record *)
  (* Java equivalent: NraOptimizer.[same] *)
  Definition tconcat_empty_record_l_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      |  ANBinop AConcat (ANConst (drec [])) p =>
         p
      | _ => p
    end.

  Lemma tconcat_empty_record_l_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tconcat_empty_record_l_fun p.
  Proof.
    tprove_correctness p.
    apply tconcat_empty_record_l_arrow.
  Qed.
  Hint Rewrite @tconcat_empty_record_l_fun_correctness : optim_correct.

  Definition tdot_over_concat_r_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
    |  (q₁ ⊕ ‵[| (a₁, q₂) |])·a₂ =>
       if a₁ == a₂
       then q₂
       else q₁·a₂
      | _ => p
    end.

  Lemma tdot_over_concat_r_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tdot_over_concat_r_fun p.
  Proof.
    tprove_correctness p.
    - apply tdot_over_concat_eq_r_arrow.
    - apply tdot_over_concat_neq_r_arrow.
      congruence.
  Qed.
  Hint Rewrite @tdot_over_concat_r_fun_correctness : optim_correct.

  Definition tdot_over_concat_l_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
    |  ( ‵[| (a₁, q₁) |]⊕ q₂ )·a₂ =>
       if a₁ == a₂
       then p
       else q₂·a₂
      | _ => p
    end.

  Lemma tdot_over_concat_l_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tdot_over_concat_l_fun p.
  Proof.
    tprove_correctness p.
    apply tdot_over_concat_neq_l_arrow.
    congruence.
  Qed.
  Hint Rewrite @tdot_over_concat_l_fun_correctness : optim_correct.

  (* p ⊗ [] ⇒ { p } when p returns a record *)
  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmerge_empty_record_r_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      |  ANBinop AMergeConcat p (ANConst (drec [])) =>
         ANUnop AColl p
      | _ => p
    end.

  Lemma tmerge_empty_record_r_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tmerge_empty_record_r_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_empty_record_r_arrow.
  Qed.
  Hint Rewrite @tmerge_empty_record_r_fun_correctness : optim_correct.

  (* [] ⊗ p ⇒ { p } when p returns a record *)
  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmerge_empty_record_l_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      |  ANBinop AMergeConcat (ANConst (drec [])) p =>
         ANUnop AColl p
      | _ => p
    end.

  Lemma tmerge_empty_record_l_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tmerge_empty_record_l_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_empty_record_l_arrow.
  Qed.
  Hint Rewrite @tmerge_empty_record_l_fun_correctness : optim_correct.

  (* χ⟨ ID ⟩( p ) ⇒ p *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tenvmap_into_id_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANMap ANID p => p
      | _ => p
    end.

  Lemma tenvmap_into_id_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tenvmap_into_id_fun p.
  Proof.
    tprove_correctness p.
    apply tenvmap_into_id_arrow.
  Qed.
  Hint Rewrite @tenvmap_into_id_fun_correctness : optim_correct.


  (* ♯flatten(χ⟨ { p1 } ⟩( p2 )) ⇒ χ⟨ p1 ⟩( p2 ) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tenvflatten_map_coll_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANUnop AFlatten (ANMap (ANUnop AColl p1) p2) =>
        ANMap p1 p2
      | _ => p
    end.

  Lemma tenvflatten_map_coll_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tenvflatten_map_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tenvflatten_map_coll_arrow.
  Qed.
  Hint Rewrite @tenvflatten_map_coll_fun_correctness : optim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tflatten_flatten_map_either_nil_fun {fruntime:foreign_runtime} (p: algenv) :=
      match p with
          ♯flatten( ♯flatten(χ⟨ANEither p₁ ‵{||} ◯ p₂⟩(p₃))) =>
          ♯flatten( χ⟨ANEither( ♯flatten(p₁)) ‵{||} ◯ p₂⟩(p₃))
      | _ => p
    end.

  Lemma tflatten_flatten_map_either_nil_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tflatten_flatten_map_either_nil_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_flatten_map_either_nil.
  Qed.

  Hint Rewrite @tflatten_flatten_map_either_nil_fun_correctness : optim_correct.

  (* χ⟨ P1 ⟩( χ⟨ P2 ⟩( P3 ) ) ⇒ χ⟨ P1 ◯ P2 ⟩( P3 ) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tenvmap_map_compose_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANMap p1 (ANMap p2 p3) => ANMap (ANApp p1 p2) p3
      | _ => p
    end.

  Lemma tenvmap_map_compose_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tenvmap_map_compose_fun p.
  Proof.
    tprove_correctness p.
    apply tenvmap_map_compose_arrow.
  Qed.
  Hint Rewrite @tenvmap_map_compose_fun_correctness : optim_correct.


  (* χ⟨ P1 ⟩( { P2 } ) ⇒ { P1 ◯ P2 } *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tenvmap_singleton_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANMap p1 (ANUnop AColl p2) => ANUnop AColl (ANApp p1 p2)
      | _ => p
    end.

  Lemma tenvmap_singleton_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tenvmap_singleton_fun p.
  Proof.
    tprove_correctness p.
    apply tenvmap_singleton_arrow.
  Qed.
  Hint Rewrite @tenvmap_singleton_fun_correctness : optim_correct.

  (* p ◯ ID ⇒ p *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_id_r_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANApp p ANID => p
      | _ => p
    end.

  Lemma tapp_over_id_r_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tapp_over_id_r_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_id_r_arrow.
  Qed.
  Hint Rewrite @tapp_over_id_r_fun_correctness : optim_correct.

  (* ENV ◯ p ⇒ ENV *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_env_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANApp ANEnv p => ANEnv
      | _ => p
    end.

  Lemma tapp_over_env_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tapp_over_env_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_env_arrow.
  Qed.
  Hint Rewrite @tapp_over_env_fun_correctness : optim_correct.

  (* ID ◯ p ⇒ p *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_id_l_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANApp ANID p => p
      | _ => p
    end.

  Lemma tapp_over_id_l_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tapp_over_id_l_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_id_l_arrow.
  Qed.
  Hint Rewrite @tapp_over_id_l_fun_correctness : optim_correct.

    (* ignores_id p1 -> p1 ◯ p2 ⇒ p1 *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_ignoreid_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
    | ANApp p1 p2 =>
      if (ignores_id_fun p1)
      then p1 else p
    | _ => p
    end.

  Lemma tapp_over_ignoreid_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tapp_over_ignoreid_fun p.
  Proof.
    destruct p; try solve [unfold talgenv_rewrites_to; simpl; auto].
    simpl.
    case_eq (ignores_id_fun p1); intros; try reflexivity.
    apply tapp_over_ignoreid_arrow.
    rewrite ignores_id_eq; assumption.
  Qed.

  (* ENV ◯ₑ p ⇒ p *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_env_l_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANAppEnv ANEnv p => p
      | _ => p
    end.

  Lemma tappenv_over_env_l_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tappenv_over_env_l_fun p.
  Proof.
    destruct p; try solve [unfold talgenv_rewrites_to; simpl; auto].
    destruct p1; try solve [unfold talgenv_rewrites_to; simpl; auto].
    simpl.
    apply tappenv_over_env_l_arrow.
  Qed.

  (* p ◯ₑ ENV ⇒ p *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_env_r_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANAppEnv p ANEnv => p
      | _ => p
    end.

  Lemma tappenv_over_env_r_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tappenv_over_env_r_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_env_r_arrow.
  Qed.

  (* ignores_env p1 -> p1 ◯ₑ p2 ⇒ p1 *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_ignoreenv_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
    | ANAppEnv p1 p2 =>
      if (ignores_env_fun p1)
      then p1 else p
    | _ => p
    end.

  Lemma tappenv_over_ignoreenv_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tappenv_over_ignoreenv_fun p.
  Proof.
    destruct p; try solve [unfold talgenv_rewrites_to; simpl; auto].
    simpl.
    case_eq (ignores_env_fun p1); intros; try reflexivity.
    apply tappenv_over_ignoreenv_arrow.
    rewrite ignores_env_eq; assumption.
  Qed.

  (* (p1 ◯ p2) ◯ p3 ⇒ p1 ◯ (p2 ◯ p3) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_app_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANApp (ANApp p1 p2) p3 =>
        ANApp p1 (ANApp p2 p3)
      | _ => p
    end.

  Lemma tapp_over_app_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tapp_over_app_fun p.
  Proof.
    destruct p; try solve [unfold talgenv_rewrites_to; simpl; auto].
    destruct p1; try solve [unfold talgenv_rewrites_to; simpl; auto].
    simpl.
    apply tapp_over_app_arrow.
  Qed.
  Hint Rewrite @tapp_over_app_fun_correctness : optim_correct.

  (* (p1 ◯ₑ p2) ◯ₑ p3 ⇒ p1 ◯ₑ (p2 ◯ₑ p3) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_appenv_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANAppEnv (ANAppEnv p1 p2) p3 =>
        ANAppEnv p1 (ANAppEnv p2 p3)
      | _ => p
    end.

  Lemma tappenv_over_appenv_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tappenv_over_appenv_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_appenv_arrow.
  Qed.
  Hint Rewrite @tappenv_over_appenv_fun_correctness : optim_correct.

  (* ignores_id p3 -> (p1 ◯ p2) ◯ₑ p3 ⇒ (p1 ◯ₑ p3) ◯ (p2 ◯ₑ p3) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_app_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANAppEnv (ANApp p1 p2) p3 =>
        if (ignores_env_fun p1) then
          ANApp p1(ANAppEnv p2 p3)
        else if (ignores_id_fun p3) then
        ANApp (ANAppEnv p1 p3) (ANAppEnv p2 p3)
      else p
    | _ => p
    end.

  Lemma tappenv_over_app_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tappenv_over_app_fun p.
  Proof.
    destruct p; try reflexivity.
    destruct p1; try reflexivity.
    simpl.
    case_eq (ignores_env_fun p1_1); intros.
    - apply tappenv_over_app_ie_arrow.
      apply ignores_env_eq; trivial.
    - case_eq (ignores_id_fun p2); intros.
      + apply tappenv_over_app_arrow.
        apply ignores_id_eq; trivial.
      + reflexivity.
  Qed.

  Hint Rewrite @tappenv_over_app_fun_correctness : optim_correct.

  (* ignores_id p1 -> (p1 ◯ₑ p2) ◯ p3 ⇒ p1 ◯ₑ (p2 ◯ p3) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_appenv_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
    | ANApp (ANAppEnv p1 p2) p3 =>
      if (ignores_id_fun p1) then
        ANAppEnv p1 (ANApp p2 p3)
      else p
    | _ => p
    end.

  Lemma tapp_over_appenv_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tapp_over_appenv_fun p.
  Proof.
    destruct p; try reflexivity.
    destruct p1; try reflexivity.
    simpl.
    case_eq (ignores_id_fun p1_1); intros.
    - apply tapp_over_appenv_arrow.
      rewrite ignores_id_eq; assumption.
    - reflexivity.
  Qed.

  (* (ANUnop u p1) ◯ p2 ⇒ (ANUnop u (p1 ◯ p2)) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_unop_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANApp (ANUnop u p1) p2 =>
        ANUnop u (ANApp p1 p2)
      | _ => p
    end.

  Lemma tapp_over_unop_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tapp_over_unop_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_unop_arrow.
  Qed.
  Hint Rewrite @tapp_over_unop_fun_correctness : optim_correct.

  (* (ANUnop u p1) ◯ₑ p2 ⇒ (ANUnop u (p1 ◯ₑ p2)) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_unop_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANAppEnv (ANUnop u p1) p2 =>
        ANUnop u (ANAppEnv p1 p2)
      | _ => p
    end.

  Lemma tappenv_over_unop_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tappenv_over_unop_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_unop_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tunop_over_either_const_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANUnop u (ANEither p₁ (ANConst d)) => ANEither (ANUnop u p₁) (ANUnop u (ANConst d))
      | _ => p
    end.

  Lemma tunop_over_either_const_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tunop_over_either_const_fun p.
  Proof.
    tprove_correctness p.
    apply tunop_over_either.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tunop_over_either_const_app_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANUnop u (ANEither p₁ (ANConst d) ◯ p₃) => ANEither (ANUnop u p₁) (ANUnop u (ANConst d)) ◯ p₃
      | _ => p
    end.

  Lemma tunop_over_either_const_app_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tunop_over_either_const_app_fun p.
  Proof.
    tprove_correctness p.
    apply tunop_over_either_app.
  Qed.
  
  (* χ⟨ p1 ⟩( p2 ) ◯ p0 ⇒ χ⟨ p1 ⟩( p2 ◯ p0 ) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_map_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANApp (ANMap p1 p2) p0 =>
        ANMap p1 (ANApp p2 p0)
      | _ => p
    end.

  Lemma tapp_over_map_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tapp_over_map_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_map_arrow.
  Qed.
  Hint Rewrite @tapp_over_map_fun_correctness : optim_correct.

  (* ⋈ᵈ⟨ q₁ ⟩( q₂ ) ◯ q ⇒ ⋈ᵈ⟨ q₁ ⟩( q₂ ◯ q ) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_mapconcat_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANApp (ANMapConcat p1 p2) p0 =>
        ANMapConcat p1 (ANApp p2 p0)
      | _ => p
    end.

  Lemma tapp_over_mapconcat_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tapp_over_mapconcat_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_mapconcat_arrow.
  Qed.
  Hint Rewrite @tapp_over_mapconcat_fun_correctness : optim_correct.

  (* χ⟨ p1 ⟩( p2 ) ◯ₑ p0 ⇒ χ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_map_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANAppEnv (ANMap p1 p2) p0 =>
        if (ignores_id_fun p0)
        then ANMap (ANAppEnv p1 p0) (ANAppEnv p2 p0)
        else p
      | _ => p
    end.

  Lemma tappenv_over_map_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tappenv_over_map_fun p.
  Proof.
    destruct p; try solve [unfold talgenv_rewrites_to; simpl; auto].
    destruct p1; try solve [unfold talgenv_rewrites_to; simpl; auto].
    simpl.
    case_eq (ignores_id_fun p2); intros; try reflexivity.
    rewrite (tappenv_over_map_arrow p2 p1_1 p1_2).
    reflexivity.
    rewrite ignores_id_eq; assumption.
  Qed.

  (* σ⟨ p1 ⟩( p2 ) ◯ₑ p0 ⇒ σ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_select_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANAppEnv (ANSelect p1 p2) p0 =>
        if (ignores_id_fun p0)
        then ANSelect (ANAppEnv p1 p0) (ANAppEnv p2 p0)
        else p
      | _ => p
    end.

  Lemma tappenv_over_select_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tappenv_over_select_fun p.
  Proof.
    destruct p; try solve [unfold talgenv_rewrites_to; simpl; auto].
    destruct p1; try solve [unfold talgenv_rewrites_to; simpl; auto].
    simpl.
    case_eq (ignores_id_fun p2); intros; try reflexivity.
    rewrite (tappenv_over_select_arrow p2 p1_1 p1_2).
    reflexivity.
    rewrite ignores_id_eq; assumption.
  Qed.

  (* σ⟨ p1 ⟩( p2 ) ◯ p0 ⇒ σ⟨ p1 ⟩( p2 ◯ p0 ) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_select_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANApp (ANSelect p1 p2) p0 =>
        ANSelect p1 (ANApp p2 p0)
      | _ => p
    end.

  Lemma tapp_over_select_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tapp_over_select_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_select_arrow.
  Qed.
  Hint Rewrite @tapp_over_select_fun_correctness : optim_correct.


  (* (ANBinop b p2 p3 ◯ p1) ⇒ (ANBinop b (p2 ◯ p1) (p3 ◯ p1)) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_binop_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANApp (ANBinop b p2 p3) p1 =>
        ANBinop b (ANApp p2 p1) (ANApp p3 p1)
      | _ => p
    end.

  Lemma tapp_over_binop_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tapp_over_binop_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_binop_arrow.
  Qed.
  Hint Rewrite @tapp_over_binop_fun_correctness : optim_correct.


  (* { [ s1 : p1 ] } × { [ s2 : p2 ] } ⇒ { [ s1 : p1; s2 : p2 ] } *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tproduct_singletons_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANProduct (ANUnop AColl (ANUnop (ARec s1) p1))
                  (ANUnop AColl (ANUnop (ARec s2) p2)) =>
        ANUnop AColl
               (ANBinop AConcat (ANUnop (ARec s1) p1) (ANUnop (ARec s2) p2))
      | _ => p
    end.

  Lemma tproduct_singletons_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tproduct_singletons_fun p.
  Proof.
    tprove_correctness p.
    apply tproduct_singletons_arrow.
  Qed.
  Hint Rewrite @tproduct_singletons_fun_correctness : optim_correct.


  (* ♯flatten(χ⟨ χ⟨ { p3 } ⟩( p1 ) ⟩( p2 )) ⇒ χ⟨ { p3 } ⟩(♯flatten(χ⟨ p1 ⟩( p2 ))) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tdouble_flatten_map_coll_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        ANUnop AFlatten
               (ANMap (ANMap (ANUnop AColl p3) p1) p2) =>
        ANMap (ANUnop AColl p3)
              (ANUnop AFlatten (ANMap p1 p2))
      | _ => p
    end.

  Lemma tdouble_flatten_map_coll_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tdouble_flatten_map_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tdouble_flatten_map_coll_arrow.
  Qed.
  Hint Rewrite @tdouble_flatten_map_coll_fun_correctness : optim_correct.

  (* ♯flatten(χ⟨ χ⟨ { p3 } ⟩( p1 ) ⟩( p2 )) ⇒ χ⟨ { p3 } ⟩(♯flatten(χ⟨ p1 ⟩( p2 ))) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tflatten_over_double_map_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | (ANUnop AFlatten
                (ANMap (ANMap q₁ (ANSelect q₂ (ANUnop AColl ANID))) q₃))
        => (ANMap q₁ (ANSelect q₂ q₃))
      | _ => p
    end.

  Lemma tflatten_over_double_map_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tflatten_over_double_map_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_over_double_map_arrow.
  Qed.
  Hint Rewrite @tflatten_over_double_map_fun_correctness : optim_correct.

  (* ♯flatten(χ⟨ χ⟨ { p3 } ⟩( p1 ) ⟩( p2 )) ⇒ χ⟨ { p3 } ⟩(♯flatten(χ⟨ p1 ⟩( p2 ))) *)

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tflatten_over_double_map_with_either_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
    | (ANUnop AFlatten
              (ANMap
                 (ANMap q₁
                        (ANSelect q₂
                                  (ANApp
                                     (ANEither (ANUnop AColl ANID) (ANConst (dcoll []))) q₃)))
                 q₄)) =>
      (ANMap q₁
             (ANSelect q₂
                       (ANUnop AFlatten
                               (ANMap
                                  (ANApp
                                     (ANEither (ANUnop AColl ANID) (ANConst (dcoll []))) q₃)
                                  q₄))))
    | _ => p
    end.

  Lemma tflatten_over_double_map_with_either_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tflatten_over_double_map_with_either_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_over_double_map_with_either_arrow.
  Qed.
  Hint Rewrite @tflatten_over_double_map_with_either_fun_correctness : optim_correct.

  (* ignores_env p1 -> (ENV ⊗ p1) ◯ₑ p2 ⇒ p2 ⊗ p1 *)
  
  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_env_merge_l_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANAppEnv (ENV ⊗ p1) p2 =>
        if (ignores_env_fun p1)
        then (p2 ⊗ p1)
        else p
      | _ => p
    end.
    
  Lemma tappenv_over_env_merge_l_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tappenv_over_env_merge_l_fun p.
  Proof.
    destruct p; try solve [unfold talgenv_rewrites_to; simpl; auto].
    destruct p1; try reflexivity.
    destruct b; try reflexivity.
    destruct p1_1; try reflexivity.
    simpl.
    case_eq (ignores_env_fun p1_2); intros; try reflexivity.
    apply tappenv_over_env_merge_l_arrow.
    rewrite ignores_env_eq; assumption.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmerge_with_empty_rec_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANBinop AMergeConcat p1 (ANConst (drec nil)) =>
        ANUnop AColl p1
      | _ => p
    end.

  Lemma tmerge_with_empty_rec_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tmerge_with_empty_rec_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_empty_record_r_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition ttostring_on_string_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANUnop AToString (ANConst (dstring s)) =>
        ANConst (dstring s)
      | ANUnop AToString (ANUnop AToString p) =>
        ANUnop AToString p
      | ANUnop AToString (ANBinop ASConcat p1 p2) =>
        (ANBinop ASConcat p1 p2)
      | _ => p
    end.

  Lemma ttostring_on_string_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ ttostring_on_string_fun p.
  Proof.
    tprove_correctness p.
    - apply ttostring_dstring_arrow.
    - apply ttostring_sconcat_arrow.
    - apply ttostring_tostring_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmap_full_over_select_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANMap p0 (ANSelect p1 (ANUnop AColl ANID)) => p
      | ANMap p0 (ANSelect p1 (ANUnop AColl p2)) =>
        ANMap (ANApp p0 p2) (ANSelect (ANApp p1 p2) (ANUnop AColl ANID))
      | _ => p
    end.

  Lemma tmap_full_over_select_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tmap_full_over_select_fun p.
  Proof.
    destruct p; simpl; try reflexivity.
    do 3 (match_destr; simpl; try reflexivity).
    destruct p2_2; simpl; try reflexivity;
    apply tmap_full_over_select_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tcompose_selects_in_mapenv_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | (ANAppEnv
           (ANUnop AFlatten
                   (ANMapEnv (ANMap ANEnv (ANSelect p1 (ANUnop AColl ANID)))))
           (ANMap ANEnv (ANSelect p2 (ANUnop AColl ANID)))) =>
        (ANMap ANEnv (ANSelect p1 (ANSelect p2 (ANUnop AColl ANID))))
      | _ => p
    end.
  
  Lemma tcompose_selects_in_mapenv_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tcompose_selects_in_mapenv_fun p.
  Proof.
    tprove_correctness p.
    apply tcompose_selects_in_mapenv_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmapenv_to_env_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | (ANApp (ANMapEnv ANEnv) p1) => ANEnv
      | _ => p
    end.

  Lemma tmapenv_to_env_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tmapenv_to_env_fun p.
  Proof.
    tprove_correctness p.
    apply tmapenv_to_env_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tenv_appenv_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANAppEnv ANEnv p1 => p1
      | _ => p
    end.
  
  Lemma tenv_appenv_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tenv_appenv_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_env_l_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tflatten_mapenv_coll_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ANUnop AFlatten (ANMapEnv (ANUnop AColl p1)) =>
        ANMapEnv p1
      | _ => p
    end.

  Lemma  tflatten_mapenv_coll_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tflatten_mapenv_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_mapenv_coll_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tflatten_nil_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ANUnop AFlatten ‵{||} =>
        ‵{||}
      | _ => p
    end.

  Lemma  tflatten_nil_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tflatten_nil_fun p.
  Proof.
    tprove_correctness p.
    apply tenvflatten_nil_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tflatten_through_appenv_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ANUnop AFlatten (ANAppEnv p1 p2) =>
        ANAppEnv (ANUnop AFlatten p1) p2
      | _ => p
    end.

  Lemma tflatten_through_appenv_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tflatten_through_appenv_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_through_appenv_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_flatten_mapenv_to_map_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | (ANAppEnv (ANUnop AFlatten (ANMapEnv p2))
            (ANBinop AMergeConcat ANEnv (ANUnop (ARec s) ANID))) =>
         (ANUnop AFlatten
            (ANMap (ANAppEnv (ANApp p2 (ANUnop (ADot s) ANEnv)) ANID)
                   (ANBinop AMergeConcat ANEnv (ANUnop (ARec s) ANID))))
      | _ => p
    end.
  
  Lemma tappenv_flatten_mapenv_to_map_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tappenv_flatten_mapenv_to_map_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_flatten_mapenv_to_map_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tselect_over_either_nil_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | σ⟨p₁⟩( ANEither p₂ ‵{||}) => ANEither (σ⟨p₁⟩(p₂)) (‵{||})
      | _ => p
    end.

  Lemma tselect_over_either_nil_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tselect_over_either_nil_fun p.
  Proof.
    tprove_correctness p.
    rewrite tselect_over_either.
    rewrite tselect_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tselect_over_either_nil_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tselect_over_either_nil_app_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | σ⟨p₁⟩( ANEither p₂ ‵{||} ◯ p₄) => ANEither (σ⟨p₁⟩(p₂)) (‵{||}) ◯ p₄
      | _ => p
    end.

  Lemma tselect_over_either_nil_app_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tselect_over_either_nil_app_fun p.
  Proof.
    tprove_correctness p.
    rewrite tselect_over_app_either.
    rewrite tselect_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tselect_over_either_nil_app_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmap_over_either_nil_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | χ⟨p₁⟩( ANEither p₂ ‵{||}) => ANEither (χ⟨p₁⟩(p₂)) (‵{||})
      | _ => p
    end.

  Lemma tmap_over_either_nil_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tmap_over_either_nil_fun p.
  Proof.
    tprove_correctness p.
    rewrite tmap_over_either.
    rewrite tmap_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tmap_over_either_nil_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmap_over_either_nil_app_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | χ⟨p₁⟩( ANEither p₂ ‵{||} ◯ p₄) => ANEither (χ⟨p₁⟩(p₂)) (‵{||}) ◯ p₄
      | _ => p
    end.

  Lemma tmap_over_either_nil_app_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tmap_over_either_nil_app_fun p.
  Proof.
    tprove_correctness p.
    rewrite tmap_over_either_app.
    rewrite tmap_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tmap_over_either_nil_app_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_either_nil_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ANAppEnv (ANEither p₂ ‵{||}) p₃ =>
        if ignores_id_fun p₃ 
        then ANEither (ANAppEnv p₂ p₃) (‵{||})
        else p
      | _ => p
    end.

  Lemma tappenv_over_either_nil_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tappenv_over_either_nil_fun p.
  Proof.
    destruct p; simpl; try reflexivity.
    destruct p1; simpl; try reflexivity.
    destruct p1_2; simpl; try reflexivity.
    destruct d; simpl; try reflexivity.
    destruct l; simpl; try reflexivity.
    match_case; simpl; try reflexivity.
    intros ig; apply ignores_id_eq in ig.
    autorewrite with talgenv_optim.
    - reflexivity.
    - trivial.
  Qed.

  Hint Rewrite @tappenv_over_either_nil_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tselect_over_flatten_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | σ⟨p₁⟩(♯flatten(p₂)) => ♯flatten(χ⟨σ⟨p₁⟩(ID)⟩(p₂))
      | _ => p
    end.

  Lemma tselect_over_flatten_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tselect_over_flatten_fun p.
  Proof.
    tprove_correctness p.
    apply tselect_over_flatten.
  Qed.

  Hint Rewrite @tselect_over_flatten_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmap_over_flatten_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | χ⟨p₁⟩(♯flatten(p₂)) => ♯flatten(χ⟨χ⟨p₁⟩(ID)⟩(p₂))
      | _ => p
    end.

  Lemma tmap_over_flatten_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tmap_over_flatten_fun p.
  Proof.
    tprove_correctness p.
    apply tmap_over_flatten.
  Qed.

  Hint Rewrite @tmap_over_flatten_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmap_over_flatten_map_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | χ⟨p₁⟩(♯flatten(χ⟨p₂⟩(p₃))) => ♯flatten(χ⟨χ⟨p₁⟩(p₂)⟩(p₃))
      | _ => p
    end.

  Lemma tmap_over_flatten_map_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tmap_over_flatten_map_fun p.
  Proof.
    tprove_correctness p.
    rewrite tmap_over_flatten.
    rewrite tenvmap_map_compose_arrow.
    rewrite tapp_over_map_arrow.
    rewrite tapp_over_id_l_arrow.
    reflexivity.
  Qed.

  Hint Rewrite @tmap_over_flatten_map_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tconcat_over_rec_eq_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | (ANBinop AConcat
                 (ANUnop (ARec s₁) p₁) (ANUnop (ARec s₂) p₂))
        => if string_dec s₁ s₂ 
           then (ANUnop (ARec s₂) p₂)
           else p
      | _ => p
    end.

  Definition tconcat_over_rec_eq_fun_correctness {model:basic_model} p :
    p ⇒ tconcat_over_rec_eq_fun p.
  Proof.
    tprove_correctness p.
    rewrite tconcat_over_rec_eq.
    reflexivity.
  Qed.
                  
  Hint Rewrite @tconcat_over_rec_eq_fun_correctness : toptim_correct.


  (* Java equivalent: NraOptimizer.[same] *)
  Definition tapp_over_const_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        (ANApp (ANConst d) p1) => (ANConst d)
      | _ => p
    end.
  
  Lemma tapp_over_const_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tapp_over_const_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_const_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_const_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        (ANAppEnv (ANConst d) p1) => (ANConst d)
      | _ => p
    end.
  
  Lemma tappenv_over_const_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tappenv_over_const_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_const_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tflip_env1_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
    | ANAppEnv (ANMap ANEnv (ANSelect q₁ (ANUnop AColl ANID))) q₂ =>
      match q₂ with
      | ANID => (ANAppEnv (ANSelect q₁ (ANUnop AColl ANID)) ANID)
      | _ =>
        if (ignores_env_fun q₁) then χ⟨q₂⟩( σ⟨ q₁ ⟩(‵{|ID|}))else p
      end
    | _ => p
    end.
  
  Lemma tflip_env1_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tflip_env1_fun p.
  Proof.
    destruct p; try reflexivity.
    destruct p1; try reflexivity.
    destruct p1_1; try reflexivity.
    destruct p1_2; try reflexivity.
    destruct p1_2_2; try reflexivity.
    destruct u; try reflexivity.
    destruct p1_2_2; try reflexivity.
    destruct p2; simpl; try reflexivity;
    try (case_eq (ignores_env_fun p1_2_1); try reflexivity; intros;
         apply tflip_env4_arrow; rewrite ignores_env_eq; assumption).
    apply tflip_env1_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tflip_env2_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      (ANAppEnv (ANSelect p (ANUnop AColl ANID)) ANID) =>
      (ANSelect (ANAppEnv p ANID) (ANUnop AColl ANID))
    | _ => p
    end.
  
  Lemma tflip_env2_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tflip_env2_fun p.
  Proof.
    tprove_correctness p.
    apply tflip_env2_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmapenv_over_singleton_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      (ANAppEnv (ANMapEnv p1) (ANUnop AColl p2)) =>
      (ANUnop AColl (ANAppEnv p1 p2))
    | _ => p
    end.

  Lemma tmapenv_over_singleton_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tmapenv_over_singleton_fun p.
  Proof.
    tprove_correctness p.
    apply tmapenv_over_singleton_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_over_binop_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
        (ANAppEnv (ANBinop b p1 p2) p0) =>
         (ANBinop b (ANAppEnv p1 p0) (ANAppEnv p2 p0))
      | _ => p
    end.
  
  Lemma tappenv_over_binop_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tappenv_over_binop_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_binop.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tflip_env6_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | χ⟨ENV ⊗ ID⟩(σ⟨p1⟩(ENV ⊗ p2)) => χ⟨‵{|ID|}⟩(σ⟨p1⟩(ENV ⊗ p2))
      | _ => p
    end.
  
  Lemma tflip_env6_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tflip_env6_fun p.
  Proof.
    tprove_correctness p.
    apply tflip_env6_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmapenv_to_map_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | (ANAppEnv (ANMapEnv p1) p2) =>
        if (ignores_id_fun p1)
        then (ANMap (ANAppEnv p1 ANID) p2)
        else p
      | _ => p
    end.

  Lemma tmapenv_to_map_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tmapenv_to_map_fun p.
  Proof.
    destruct p; try reflexivity.
    destruct p1; try reflexivity.
    simpl.
    case_eq (ignores_id_fun p1); try reflexivity; intros.
    apply tmapenv_to_map_arrow.
    rewrite ignores_id_eq; assumption.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmerge_concat_to_concat_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ‵[| (s1, p1)|] ⊗ ‵[| (s2, p2)|] =>
        if (s1 == s2)
        then p
        else ANUnop AColl (ANBinop AConcat (‵[| (s1, p1)|]) (‵[| (s2, p2)|]))
      | _ => p
    end.
  
  Lemma tmerge_concat_to_concat_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tmerge_concat_to_concat_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_concat_to_concat_arrow.
    trivial.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmerge_with_concat_to_concat_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      | ‵[| (s1, p1)|] ⊗ (‵[| (s1', p1')|] ⊕ ‵[| (s2, p2)|]) =>
        if (s1 == s2)
        then p
        else
          if (s1 == s1')
          then
            if (p1 == p1')
            then ANUnop AColl (ANBinop AConcat (‵[| (s1, p1)|]) (‵[| (s2, p2)|]))
            else p
          else p
      | _ => p
    end.
  
  Lemma tmerge_with_concat_to_concat_fun_correctness {model:basic_model} (p: algenv) :
    p ⇒ tmerge_with_concat_to_concat_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_with_concat_to_concat_arrow.
    trivial.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tdot_over_rec_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | (‵[| (s1, p1)|]) · s2 =>
        if (s1 == s2) then p1
        else p
      | _ => p
    end.

  Lemma tdot_over_rec_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tdot_over_rec_fun p.
  Proof.
    tprove_correctness p.
    apply tdot_over_rec_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tnested_map_over_singletons_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ♯flatten(χ⟨ σ⟨ q₁ ⟩(‵{|q₂|}) ⟩(q₃))
        => σ⟨ q₁ ⟩(χ⟨ q₂ ⟩(q₃))
      | _ => p
    end.

  Lemma tnested_map_over_singletons_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tnested_map_over_singletons_fun p.
  Proof.
    tprove_correctness p.
    apply tnested_map_over_singletons_arrow.
  Qed.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tappenv_mapenv_to_map_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
    | ANAppEnv (ANMapEnv q) (ANEnv ⊗ ‵[| (a, ID)|]) =>
             χ⟨(q ◯ (ANUnop (ADot a) ANEnv)) ◯ₑ ID⟩( (ENV ⊗ ‵[| (a, ID)|]) )
    | _ => p
    end.

  Lemma tappenv_mapenv_to_map_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tappenv_mapenv_to_map_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_mapenv_to_map_arrow.
  Qed.

  (* optimizations for rproject *)

  (* Java equivalent: NraOptimizer.[same] *)
   Definition trproject_nil_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ANUnop (ARecProject nil) p₁
        => ANConst (drec nil)
      | _ => p
    end.

  Definition trproject_nil_fun_correctness {model:basic_model} p :
    p ⇒ trproject_nil_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_nil.
  Qed.

  Hint Rewrite @trproject_nil_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition trproject_over_const_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ANUnop (ARecProject sl)
          (ANConst (drec l))
        => ANConst (drec (rproject l sl))
      | _ => p
    end.

  Definition trproject_over_const_fun_correctness {model:basic_model} p :
    p ⇒ trproject_over_const_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_over_const.
  Qed.

  Hint Rewrite @trproject_over_const_fun_correctness : toptim_correct.
  
  (* Java equivalent: NraOptimizer.[same] *)
  Definition trproject_over_rec_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ANUnop (ARecProject sl)
          (ANUnop (ARec s) p₁)
        => if in_dec string_dec s sl
           then ANUnop (ARec s) p₁
           else ‵[||]
      | _ => p
    end.

  Definition trproject_over_rec_fun_correctness {model:basic_model} p :
    p ⇒ trproject_over_rec_fun p.
  Proof.
    tprove_correctness p.
    - apply trproject_over_rec_in; trivial.
    - apply trproject_over_rec_nin; trivial. 
  Qed.

  Hint Rewrite @trproject_over_rec_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
   Definition trproject_over_concat_r_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ANUnop (ARecProject sl)
               (ANBinop AConcat
                        p₁ (ANUnop (ARec s) p₂))
        => if in_dec string_dec s sl
           then ANBinop AConcat
                        (ANUnop (ARecProject (remove string_dec s sl)) p₁)
                        (ANUnop (ARec s) p₂)
           else (ANUnop (ARecProject sl) p₁)
      | _ => p
    end.

  Definition trproject_over_concat_r_fun_correctness {model:basic_model} p :
    p ⇒ trproject_over_concat_r_fun p.
  Proof.
    tprove_correctness p.
    - apply trproject_over_concat_rec_r_in; trivial.
    - apply trproject_over_concat_rec_r_nin; trivial.
  Qed.
                  
  Hint Rewrite @trproject_over_concat_r_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
     Definition trproject_over_concat_l_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ANUnop (ARecProject sl)
               (ANBinop AConcat
                        (ANUnop (ARec s) p₁) p₂)
        => if in_dec string_dec s sl
                     (* this case would need shape/type inference to handle, since we don't know if s is in p₂ *)

           then p
           else (ANUnop (ARecProject sl) p₂)
      | _ => p
    end.

  Definition trproject_over_concat_l_fun_correctness {model:basic_model} p :
    p ⇒ trproject_over_concat_l_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_over_concat_rec_l_nin; trivial.
  Qed.
                  
  Hint Rewrite @trproject_over_concat_l_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition trproject_over_rproject_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ANUnop (ARecProject sl1)
          (ANUnop (ARecProject sl2) p1)
        => ANUnop (ARecProject (set_inter string_dec sl2 sl1)) p1
      | _ => p
    end.

  Definition trproject_over_rproject_fun_correctness {model:basic_model} p :
    p ⇒ trproject_over_rproject_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_over_rproject.
  Qed.

  Hint Rewrite @trproject_over_rproject_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
   Definition trproject_over_either_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ANUnop (ARecProject sl)
          (ANEither p₁ p₂)
        => ANEither (ANUnop (ARecProject sl) p₁) (ANUnop (ARecProject sl) p₂)
      | _ => p
    end.

  Definition trproject_over_either_fun_correctness {model:basic_model} p :
    p ⇒ trproject_over_either_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_over_either.
  Qed.

  Hint Rewrite @trproject_over_either_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tcount_over_map_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ♯count(χ⟨p₁⟩(p₂)) => ♯count(p₂)
      | _ => p
    end.

  Definition tcount_over_map_fun_correctness {model:basic_model} p :
    p ⇒ tcount_over_map_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_map.
  Qed.

  Hint Rewrite @tcount_over_map_fun_correctness : toptim_correct.
  
  (* Java equivalent: NraOptimizer.[same] *)
  Definition tcount_over_flat_map_map_fun {fruntime:foreign_runtime} (p:algenv) :=
      match p with
        | ♯count(♯flatten(χ⟨χ⟨p₁⟩(p₂)⟩(p₃))) =>
          ♯count(♯flatten(χ⟨p₂⟩(p₃)))
      | _ => p
    end.

  Definition tcount_over_flat_map_map_fun_correctness {model:basic_model} p :
    p ⇒ tcount_over_flat_map_map_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_flat_map_map.
  Qed.

  Hint Rewrite @tcount_over_flat_map_map_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tcount_over_flat_map_either_nil_map_fun {fruntime:foreign_runtime} (p:algenv) :=
      match p with
        | ♯count(♯flatten(χ⟨ANEither (χ⟨p₁⟩(p₂)) ‵{||}⟩(p₃))) =>
          ♯count(♯flatten(χ⟨ANEither p₂ ‵{||}⟩(p₃)))
      | _ => p
    end.

  Definition tcount_over_flat_map_either_nil_map_fun_correctness {model:basic_model} p :
    p ⇒ tcount_over_flat_map_either_nil_map_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_flat_map_either_nil_map.
  Qed.

  Hint Rewrite @tcount_over_flat_map_either_nil_map_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tcount_over_flat_map_either_nil_app_map_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ♯count(♯flatten(χ⟨ANEither (χ⟨p₁⟩(p₂)) ‵{||} ◯ p₄⟩(p₃))) =>
        ♯count(♯flatten(χ⟨ANEither p₂ ‵{||} ◯ p₄⟩(p₃)))
      | _ => p
    end.

  Definition tcount_over_flat_map_either_nil_app_map_fun_correctness {model:basic_model} p :
    p ⇒ tcount_over_flat_map_either_nil_app_map_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_flat_map_either_nil_app_map.
  Qed.

  Hint Rewrite @tcount_over_flat_map_either_nil_app_map_fun_correctness : toptim_correct.

  (* Java equivalent: NraOptimizer.[same] *)
  Definition tcount_over_flat_map_either_nil_app_singleton_fun {fruntime:foreign_runtime} (p:algenv) :=
    match p with
      | ♯count(♯flatten(χ⟨ANEither (‵{| p₁ |}) ‵{||} ◯ p₃⟩(p₂))) =>
        ♯count(♯flatten(χ⟨ANEither (‵{| ANConst dunit |}) ‵{||} ◯ p₃⟩(p₂)))
      | _ => p
    end.

  Definition tcount_over_flat_map_either_nil_app_singleton_fun_correctness {model:basic_model} p :
    p ⇒ tcount_over_flat_map_either_nil_app_singleton_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_flat_map_either_nil_app_singleton.
  Qed.

  Hint Rewrite @tcount_over_flat_map_either_nil_app_singleton_fun_correctness : toptim_correct.

  (* optimizations for mapconcat *)

  (* ⋈ᵈ⟨ p₁ ⟩(‵{| ‵[||] |}) ⇒ p₁ ◯ (‵[||]) *)
  
  (* Java equivalent: NraOptimizer.[same] *)
  Definition tmapconcat_over_singleton_fun {fruntime:foreign_runtime} (p: algenv) :=
    match p with
      |  ANMapConcat p (ANUnop AColl (ANConst (drec []))) =>
         ANApp p (ANConst (drec []))
      | _ => p
    end.

  Lemma tmapconcat_over_singleton_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tmapconcat_over_singleton_fun p.
  Proof.
    tprove_correctness p.
    apply tmapconcat_over_singleton.
  Qed.
  Hint Rewrite @tmerge_empty_record_r_fun_correctness : optim_correct.

  Definition tdup_elim_fun {fruntime:foreign_runtime} (p:algenv) :=
    dup_elim_fun p.

  Lemma tdup_elim_fun_correctness {model:basic_model} (p:algenv) :
    p ⇒ tdup_elim_fun p.
  Proof.
    destruct p; simpl; try reflexivity.
    destruct u; simpl; try reflexivity.
    match_case; try reflexivity; intros nd.
    apply tdup_elim.
    apply nodupA_checker_correct.
    trivial.
  Qed.

  Hint Rewrite @tdup_elim_fun_correctness : optim_correct.

  
  (* *************************** *)
  Local Open Scope string.
  (* Java equivalent: NraOptimizer.head_optim_list *)
  Definition head_optim_list {fruntime:foreign_runtime} : list (string*(algenv -> algenv)) :=
    [("tapp_over_app_fun", tapp_over_app_fun);
        ("tappenv_over_appenv_fun", tappenv_over_appenv_fun);
        ("tappenv_over_app_fun", tappenv_over_app_fun);
        ("tapp_over_appenv_fun", tapp_over_appenv_fun);
        ("tenvmap_into_id_fun", tenvmap_into_id_fun);
        ("tproduct_singletons_fun", tproduct_singletons_fun);
        ("tenvmap_singleton_fun", tenvmap_singleton_fun);
        ("tenvmap_map_compose_fun", tenvmap_map_compose_fun);
        ("tenvflatten_coll_fun", tenvflatten_coll_fun);
         (* only in tail *)
        (*    tdouble_flatten_map_coll_fun; *)
        ("tenvflatten_map_coll_fun", tenvflatten_map_coll_fun);
        ("tapp_over_id_r_fun", tapp_over_id_r_fun);
        ("tapp_over_id_l_fun", tapp_over_id_l_fun);
        ("tapp_over_unop_fun", tapp_over_unop_fun);
        ("tapp_over_binop_fun", tapp_over_binop_fun);
        ("tapp_over_select_fun", tapp_over_select_fun);
        ("tapp_over_map_fun", tapp_over_map_fun);
        ("tapp_over_mapconcat_fun", tapp_over_mapconcat_fun);
        ("tappenv_over_unop_fun", tappenv_over_unop_fun);
        ("tcompose_selects_in_mapenv_fun", tcompose_selects_in_mapenv_fun);
        ("tmap_full_over_select_fun", tmap_full_over_select_fun);
        ("ttostring_on_string_fun", ttostring_on_string_fun);
        ("tmerge_with_empty_rec_fun", tmerge_with_empty_rec_fun);
        ("tselect_and_fun", tselect_and_fun);
        ("tenvdot_from_duplicate_r_fun", tenvdot_from_duplicate_r_fun);
        ("tenvdot_from_duplicate_l_fun", tenvdot_from_duplicate_l_fun);
        ("tconcat_empty_record_r_fun", tconcat_empty_record_r_fun);
        ("tconcat_empty_record_l_fun", tconcat_empty_record_l_fun);
        ("tdot_over_concat_r_fun", tdot_over_concat_r_fun);
        ("tdot_over_concat_l_fun", tdot_over_concat_l_fun);
        ("tmerge_empty_record_r_fun", tmerge_empty_record_r_fun);
        ("tmerge_empty_record_l_fun", tmerge_empty_record_l_fun);
        ("tmapenv_to_env_fun", tmapenv_to_env_fun);
        ("tenv_appenv_fun", tenv_appenv_fun);
        ("tflatten_mapenv_coll_fun", tflatten_mapenv_coll_fun);
        ("tflatten_nil_fun", tflatten_nil_fun);
         (* only in head *)
        ("tflatten_through_appenv_fun", tflatten_through_appenv_fun);
         (* only in head *)
        ("tappenv_flatten_mapenv_to_map_fun", tappenv_flatten_mapenv_to_map_fun);
        ("tapp_over_const_fun", tapp_over_const_fun);
        ("tappenv_over_const_fun", tappenv_over_const_fun);
        ("tflip_env1_fun", tflip_env1_fun);
        ("tflip_env2_fun", tflip_env2_fun);
        ("tmapenv_over_singleton_fun", tmapenv_over_singleton_fun);
        ("tappenv_over_binop_fun", tappenv_over_binop_fun);
        ("tflip_env6_fun", tflip_env6_fun);
        ("tmapenv_to_map_fun", tmapenv_to_map_fun);
        ("tappenv_over_map_fun", tappenv_over_map_fun);
        ("tapp_over_ignoreid_fun", tapp_over_ignoreid_fun);
        ("tappenv_over_ignoreenv_fun", tappenv_over_ignoreenv_fun);
        ("tappenv_over_env_r_fun", tappenv_over_env_r_fun);
        ("tappenv_over_env_l_fun", tappenv_over_env_l_fun);
        ("tappenv_over_env_merge_l_fun", tappenv_over_env_merge_l_fun);
        ("tappenv_over_select_fun", tappenv_over_select_fun);
        ("tmerge_concat_to_concat_fun", tmerge_concat_to_concat_fun);
        ("tmerge_with_concat_to_concat_fun", tmerge_with_concat_to_concat_fun);
        ("tdot_over_rec_fun", tdot_over_rec_fun);
        ("tnested_map_over_singletons_fun", tnested_map_over_singletons_fun);
        ("tapp_over_env_fun", tapp_over_env_fun);
        ("tselect_over_either_nil_fun", tselect_over_either_nil_fun);
        ("tselect_over_either_nil_app_fun", tselect_over_either_nil_app_fun);
          ("tmap_over_either_nil_fun", tmap_over_either_nil_fun);
        ("tmap_over_either_nil_app_fun", tmap_over_either_nil_app_fun);
        ("tappenv_over_either_nil_fun", tappenv_over_either_nil_fun);
        ("tselect_over_flatten_fun", tselect_over_flatten_fun);
(*    tmap_over_flatten_fun; *)
        ("tconcat_over_rec_eq_fun", tconcat_over_rec_eq_fun);
        ("trproject_nil_fun", trproject_nil_fun);
        ("trproject_over_const_fun", trproject_over_const_fun);
        ("trproject_over_rec_fun", trproject_over_rec_fun);
        ("trproject_over_concat_r_fun", trproject_over_concat_r_fun);
        ("trproject_over_concat_l_fun", trproject_over_concat_l_fun);
        ("trproject_over_rproject_fun", trproject_over_rproject_fun);
        ("trproject_over_either_fun", trproject_over_either_fun);
        ("tcount_over_map_fun", tcount_over_map_fun);
        ("tcount_over_flat_map_map_fun", tcount_over_flat_map_map_fun);
        ("tcount_over_flat_map_either_nil_map_fun", tcount_over_flat_map_either_nil_map_fun);
        ("tcount_over_flat_map_either_nil_app_map_fun", tcount_over_flat_map_either_nil_app_map_fun);
        ("tcount_over_flat_map_either_nil_app_singleton_fun", tcount_over_flat_map_either_nil_app_singleton_fun);
        ("tunop_over_either_const_app_fun", tunop_over_either_const_app_fun);
        ("tunop_over_either_const_fun", tunop_over_either_const_fun);
        ("tmapconcat_over_singleton_fun", tmapconcat_over_singleton_fun)
    ].

  (* Java equivalent: NraOptimizer.head_optim *)
  Definition head_optim
             {fruntime:foreign_runtime}
             {logger:optimizer_logger string algenv} (name:string)
    : algenv -> algenv :=
    apply_steps ("nra_head" ++ name) head_optim_list.
  
  Lemma head_optim_correctness {model:basic_model} {logger:optimizer_logger string algenv} (name:string) (p:algenv) :
    p ⇒ head_optim name p.
  Proof.
    unfold head_optim.
    rewrite tmapconcat_over_singleton_fun_correctness at 1.
    rewrite tunop_over_either_const_fun_correctness at 1.
    rewrite tunop_over_either_const_app_fun_correctness at 1.
    rewrite tcount_over_flat_map_either_nil_app_singleton_fun_correctness at 1.
    rewrite tcount_over_flat_map_either_nil_app_map_fun_correctness at 1.
    rewrite tcount_over_flat_map_either_nil_map_fun_correctness at 1.
    rewrite tcount_over_flat_map_map_fun_correctness at 1.
    rewrite tcount_over_map_fun_correctness at 1.
    rewrite trproject_over_either_fun_correctness at 1.
    rewrite trproject_over_rproject_fun_correctness at 1.
    rewrite trproject_over_concat_l_fun_correctness at 1.
    rewrite trproject_over_concat_r_fun_correctness at 1.
    rewrite trproject_over_rec_fun_correctness at 1.
    rewrite trproject_over_const_fun_correctness at 1.
    rewrite trproject_nil_fun_correctness at 1.
    rewrite tconcat_over_rec_eq_fun_correctness at 1.
(*    rewrite tmap_over_flatten_fun_correctness at 1. *)
    rewrite tselect_over_flatten_fun_correctness at 1.
    rewrite tappenv_over_either_nil_fun_correctness at 1.
    rewrite tmap_over_either_nil_app_fun_correctness at 1.
    rewrite tmap_over_either_nil_fun_correctness at 1.
    rewrite tselect_over_either_nil_app_fun_correctness at 1.
    rewrite tselect_over_either_nil_fun_correctness at 1.
    rewrite tapp_over_env_fun_correctness at 1.
    rewrite tnested_map_over_singletons_fun_correctness at 1.
    rewrite tdot_over_rec_fun_correctness at 1.
    rewrite tmerge_with_concat_to_concat_fun_correctness at 1.
    rewrite tmerge_concat_to_concat_fun_correctness at 1.
    rewrite tappenv_over_select_fun_correctness at 1.
    rewrite tappenv_over_env_merge_l_fun_correctness at 1.
    rewrite tappenv_over_env_l_fun_correctness at 1.
    rewrite tappenv_over_env_r_fun_correctness at 1.
    rewrite tappenv_over_ignoreenv_fun_correctness at 1.
    rewrite tapp_over_ignoreid_fun_correctness at 1.
    rewrite tappenv_over_map_fun_correctness at 1.
    rewrite tmapenv_to_map_fun_correctness at 1.
    rewrite tflip_env6_fun_correctness at 1.
    rewrite tappenv_over_binop_fun_correctness at 1.
    rewrite tmapenv_over_singleton_fun_correctness at 1.
    rewrite tflip_env2_fun_correctness at 1.
    rewrite tflip_env1_fun_correctness at 1.
    rewrite tappenv_over_const_fun_correctness at 1.
    rewrite tapp_over_const_fun_correctness at 1.
    rewrite tappenv_flatten_mapenv_to_map_fun_correctness at 1.
    rewrite tflatten_through_appenv_fun_correctness at 1.
    rewrite tflatten_nil_fun_correctness at 1.
    rewrite tflatten_mapenv_coll_fun_correctness at 1.
    rewrite tenv_appenv_fun_correctness at 1.
    rewrite tmapenv_to_env_fun_correctness at 1.
    rewrite tmerge_empty_record_l_fun_correctness at 1.
    rewrite tmerge_empty_record_r_fun_correctness at 1.
    rewrite tdot_over_concat_l_fun_correctness at 1.
    rewrite tdot_over_concat_r_fun_correctness at 1.
    rewrite tconcat_empty_record_l_fun_correctness at 1.
    rewrite tconcat_empty_record_r_fun_correctness at 1.
    rewrite tenvdot_from_duplicate_l_fun_correctness at 1.
    rewrite tenvdot_from_duplicate_r_fun_correctness at 1.
    rewrite tselect_and_fun_correctness at 1.
    rewrite tmerge_with_empty_rec_fun_correctness at 1.
    rewrite ttostring_on_string_fun_correctness at 1.
    rewrite tmap_full_over_select_fun_correctness at 1; (* only in tail *)
    rewrite tcompose_selects_in_mapenv_fun_correctness at 1.
    rewrite tappenv_over_unop_fun_correctness at 1.
    rewrite tapp_over_mapconcat_fun_correctness at 1.
    rewrite tapp_over_map_fun_correctness at 1.
    rewrite tapp_over_select_fun_correctness at 1.
    rewrite tapp_over_binop_fun_correctness at 1.
    rewrite tapp_over_unop_fun_correctness at 1.
    rewrite tapp_over_id_l_fun_correctness at 1.
    rewrite tapp_over_id_r_fun_correctness at 1.
    rewrite tenvflatten_map_coll_fun_correctness at 1.
    rewrite tenvflatten_coll_fun_correctness at 1.
    rewrite tenvmap_map_compose_fun_correctness at 1.
    rewrite tenvmap_singleton_fun_correctness at 1.
    rewrite tproduct_singletons_fun_correctness at 1.
    rewrite tenvmap_into_id_fun_correctness at 1.
    rewrite tapp_over_appenv_fun_correctness at 1.
    rewrite tappenv_over_app_fun_correctness at 1.
    rewrite tappenv_over_appenv_fun_correctness at 1.
    rewrite tapp_over_app_fun_correctness at 1.
    unfold head_optim_list.
    unfold apply_steps.
    rewrite hide_use_eq.
    simpl fold_right.
    repeat rewrite optimizer_step_result.
    unfold snd.
    red; intros; split; [apply H|reflexivity].
  Qed.

  (* *************************** *)

  (* Java equivalent: NraOptimizer.tail_optim_list *)
  Definition tail_optim_list {fruntime:foreign_runtime} : list (string * (algenv -> algenv)) :=
    [ ("tflatten_flatten_map_either_nil_fun", tflatten_flatten_map_either_nil_fun);
        ("tmap_over_flatten_map_fun", tmap_over_flatten_map_fun);
        ("tapp_over_app_fun", tapp_over_app_fun);
        ("tappenv_over_appenv_fun", tappenv_over_appenv_fun);
        ("tappenv_over_app_fun", tappenv_over_app_fun);
        ("tapp_over_appenv_fun", tapp_over_appenv_fun);
        ("tenvmap_into_id_fun", tenvmap_into_id_fun);
        ("tproduct_singletons_fun", tproduct_singletons_fun);
        ("tenvmap_singleton_fun", tenvmap_singleton_fun);
        ("tenvmap_map_compose_fun", tenvmap_map_compose_fun);
        ("tenvflatten_coll_fun", tenvflatten_coll_fun);
        (* only in tail *)
        ("tdouble_flatten_map_coll_fun", tdouble_flatten_map_coll_fun);
        ("tflatten_over_double_map_fun", tflatten_over_double_map_fun);
        ("tflatten_over_double_map_with_either_fun", tflatten_over_double_map_with_either_fun);
        ("tenvflatten_map_coll_fun", tenvflatten_map_coll_fun);
        ("tapp_over_id_r_fun", tapp_over_id_r_fun);
        ("tapp_over_id_l_fun", tapp_over_id_l_fun);
        ("tapp_over_unop_fun", tapp_over_unop_fun);
        ("tapp_over_binop_fun", tapp_over_binop_fun);
        ("tapp_over_select_fun", tapp_over_select_fun);
        ("tapp_over_map_fun", tapp_over_map_fun);
        ("tapp_over_mapconcat_fun", tapp_over_mapconcat_fun);
        ("tappenv_over_unop_fun", tappenv_over_unop_fun);
        ("tcompose_selects_in_mapenv_fun", tcompose_selects_in_mapenv_fun);
        ("tmap_full_over_select_fun", tmap_full_over_select_fun);
        ("ttostring_on_string_fun", ttostring_on_string_fun);
        ("tmerge_with_empty_rec_fun", tmerge_with_empty_rec_fun);
        ("tselect_and_fun", tselect_and_fun);
        ("tenvdot_from_duplicate_r_fun", tenvdot_from_duplicate_r_fun);
        ("tenvdot_from_duplicate_l_fun", tenvdot_from_duplicate_l_fun);
        ("tconcat_empty_record_r_fun", tconcat_empty_record_r_fun);
        ("tconcat_empty_record_l_fun", tconcat_empty_record_l_fun);
        ("tdot_over_concat_r_fun", tdot_over_concat_r_fun);
        ("tdot_over_concat_l_fun", tdot_over_concat_l_fun);
        ("tmerge_empty_record_r_fun", tmerge_empty_record_r_fun);
        ("tmerge_empty_record_l_fun", tmerge_empty_record_l_fun);
        ("tmapenv_to_env_fun", tmapenv_to_env_fun);
        ("tenv_appenv_fun", tenv_appenv_fun);
        ("tflatten_mapenv_coll_fun", tflatten_mapenv_coll_fun);
        ("tflatten_nil_fun", tflatten_nil_fun);
        ("tapp_over_const_fun", tapp_over_const_fun);
        ("tappenv_over_const_fun", tappenv_over_const_fun);
        ("tflip_env1_fun", tflip_env1_fun);
        ("tflip_env2_fun", tflip_env2_fun);
        ("tmapenv_over_singleton_fun", tmapenv_over_singleton_fun);
        ("tappenv_over_binop_fun", tappenv_over_binop_fun);
        ("tflip_env6_fun", tflip_env6_fun);
        ("tmapenv_to_map_fun", tmapenv_to_map_fun);
        ("tappenv_over_map_fun", tappenv_over_map_fun);
        ("tapp_over_ignoreid_fun", tapp_over_ignoreid_fun);
        ("tappenv_over_ignoreenv_fun", tappenv_over_ignoreenv_fun);
        ("tappenv_over_env_r_fun", tappenv_over_env_r_fun);
        ("tappenv_over_env_l_fun", tappenv_over_env_l_fun);
        ("tappenv_over_env_merge_l_fun", tappenv_over_env_merge_l_fun);
        ("tappenv_over_select_fun", tappenv_over_select_fun);
        ("tmerge_concat_to_concat_fun", tmerge_concat_to_concat_fun);
        ("tmerge_with_concat_to_concat_fun", tmerge_with_concat_to_concat_fun);
        ("tdot_over_rec_fun", tdot_over_rec_fun);
        ("tnested_map_over_singletons_fun", tnested_map_over_singletons_fun);
        ("tapp_over_env_fun", tapp_over_env_fun);
        ("tappenv_mapenv_to_map_fun", tappenv_mapenv_to_map_fun);
        ("tselect_over_either_nil_fun", tselect_over_either_nil_fun);
        ("tselect_over_either_nil_app_fun", tselect_over_either_nil_app_fun); 
        ("tmap_over_either_nil_fun", tmap_over_either_nil_fun);
        ("tmap_over_either_nil_app_fun", tmap_over_either_nil_app_fun); 
        ("tappenv_over_either_nil_fun", tappenv_over_either_nil_fun);
        ("tselect_over_flatten_fun", tselect_over_flatten_fun);
        ("tmap_over_flatten_fun", tmap_over_flatten_fun); 
        ("tconcat_over_rec_eq_fun", tconcat_over_rec_eq_fun);
        ("trproject_nil_fun", trproject_nil_fun);
        ("trproject_over_const_fun", trproject_over_const_fun);
        ("trproject_over_rec_fun", trproject_over_rec_fun);
        ("trproject_over_concat_r_fun", trproject_over_concat_r_fun);
        ("trproject_over_concat_l_fun", trproject_over_concat_l_fun);
        ("trproject_over_rproject_fun", trproject_over_rproject_fun);
        ("trproject_over_either_fun", trproject_over_either_fun);
        ("tcount_over_map_fun", tcount_over_map_fun);
        ("tcount_over_flat_map_map_fun", tcount_over_flat_map_map_fun);
        ("tcount_over_flat_map_either_nil_map_fun", tcount_over_flat_map_either_nil_map_fun);
        ("tcount_over_flat_map_either_nil_app_map_fun", tcount_over_flat_map_either_nil_app_map_fun);
        ("tcount_over_flat_map_either_nil_app_singleton_fun", tcount_over_flat_map_either_nil_app_singleton_fun);
        ("tunop_over_either_const_app_fun", tunop_over_either_const_app_fun);
        ("tunop_over_either_const_fun", tunop_over_either_const_fun);
        ("tmapconcat_over_singleton_fun", tmapconcat_over_singleton_fun)
    ].

  (* Java equivalent: NraOptimizer.tail_optim *)
  Definition tail_optim {fruntime:foreign_runtime} {logger:optimizer_logger string algenv} (name:string) : algenv -> algenv :=
    apply_steps ("tail" ++ name)  tail_optim_list.

  Lemma tail_optim_correctness {model:basic_model}  {logger:optimizer_logger string algenv} (name:string) (p:algenv) :
    p ⇒ tail_optim name p.
  Proof.
    unfold tail_optim.
    rewrite tmapconcat_over_singleton_fun_correctness at 1.
    rewrite tunop_over_either_const_fun_correctness at 1.
    rewrite tunop_over_either_const_app_fun_correctness at 1.
    rewrite tcount_over_flat_map_either_nil_app_singleton_fun_correctness at 1.
    rewrite tcount_over_flat_map_either_nil_app_map_fun_correctness at 1.
    rewrite tcount_over_flat_map_either_nil_map_fun_correctness at 1.
    rewrite tcount_over_flat_map_map_fun_correctness at 1.
    rewrite tcount_over_map_fun_correctness at 1.
    rewrite trproject_over_either_fun_correctness at 1.
    rewrite trproject_over_rproject_fun_correctness at 1.
    rewrite trproject_over_concat_l_fun_correctness at 1.
    rewrite trproject_over_concat_r_fun_correctness at 1.
    rewrite trproject_over_rec_fun_correctness at 1.
    rewrite trproject_over_const_fun_correctness at 1.
    rewrite trproject_nil_fun_correctness at 1.
    rewrite tconcat_over_rec_eq_fun_correctness at 1.
    rewrite tmap_over_flatten_fun_correctness at 1. 
    rewrite tselect_over_flatten_fun_correctness at 1.
    rewrite tappenv_over_either_nil_fun_correctness at 1.
    rewrite tmap_over_either_nil_app_fun_correctness at 1.
    rewrite tmap_over_either_nil_fun_correctness at 1.
    rewrite tselect_over_either_nil_app_fun_correctness at 1.
    rewrite tselect_over_either_nil_fun_correctness at 1.
    rewrite tappenv_mapenv_to_map_fun_correctness at 1.
    rewrite tapp_over_env_fun_correctness at 1.
    rewrite tnested_map_over_singletons_fun_correctness at 1.
    rewrite tdot_over_rec_fun_correctness at 1.
    rewrite tmerge_with_concat_to_concat_fun_correctness at 1.
    rewrite tmerge_concat_to_concat_fun_correctness at 1.
    rewrite tappenv_over_select_fun_correctness at 1.
    rewrite tappenv_over_env_merge_l_fun_correctness at 1.
    rewrite tappenv_over_env_l_fun_correctness at 1.
    rewrite tappenv_over_env_r_fun_correctness at 1.
    rewrite tappenv_over_ignoreenv_fun_correctness at 1.
    rewrite tapp_over_ignoreid_fun_correctness at 1.
    rewrite tappenv_over_map_fun_correctness at 1.
    rewrite tmapenv_to_map_fun_correctness at 1.
    rewrite tflip_env6_fun_correctness at 1.
    rewrite tappenv_over_binop_fun_correctness at 1.
    rewrite tmapenv_over_singleton_fun_correctness at 1.
    rewrite tflip_env2_fun_correctness at 1.
    rewrite tflip_env1_fun_correctness at 1.
    rewrite tappenv_over_const_fun_correctness at 1.
    rewrite tapp_over_const_fun_correctness at 1.
    rewrite tflatten_nil_fun_correctness at 1.
    rewrite tflatten_mapenv_coll_fun_correctness at 1.
    rewrite tenv_appenv_fun_correctness at 1.
    rewrite tmapenv_to_env_fun_correctness at 1.
    rewrite tmerge_empty_record_l_fun_correctness at 1.
    rewrite tmerge_empty_record_r_fun_correctness at 1.
    rewrite tdot_over_concat_l_fun_correctness at 1.
    rewrite tdot_over_concat_r_fun_correctness at 1.
    rewrite tconcat_empty_record_l_fun_correctness at 1.
    rewrite tconcat_empty_record_r_fun_correctness at 1.
    rewrite tenvdot_from_duplicate_l_fun_correctness at 1.
    rewrite tenvdot_from_duplicate_r_fun_correctness at 1.
    rewrite tselect_and_fun_correctness at 1.
    rewrite tmerge_with_empty_rec_fun_correctness at 1.
    rewrite ttostring_on_string_fun_correctness at 1.
    rewrite tmap_full_over_select_fun_correctness at 1.
    rewrite tcompose_selects_in_mapenv_fun_correctness at 1;
    rewrite tappenv_over_unop_fun_correctness at 1.
    rewrite tapp_over_mapconcat_fun_correctness at 1.
    rewrite tapp_over_map_fun_correctness at 1.
    rewrite tapp_over_select_fun_correctness at 1.
    rewrite tapp_over_binop_fun_correctness at 1.
    rewrite tapp_over_unop_fun_correctness at 1.
    rewrite tapp_over_id_l_fun_correctness at 1.
    rewrite tapp_over_id_r_fun_correctness at 1.
    rewrite tenvflatten_map_coll_fun_correctness at 1.
    rewrite tflatten_over_double_map_with_either_fun_correctness at 1.
    rewrite tflatten_over_double_map_fun_correctness at 1.
    rewrite tdouble_flatten_map_coll_fun_correctness at 1.
    rewrite tenvflatten_coll_fun_correctness at 1.
    rewrite tenvmap_map_compose_fun_correctness at 1.
    rewrite tenvmap_singleton_fun_correctness at 1.
    rewrite tproduct_singletons_fun_correctness at 1.
    rewrite tenvmap_into_id_fun_correctness at 1.
    rewrite tapp_over_appenv_fun_correctness at 1.
    rewrite tappenv_over_app_fun_correctness at 1.
    rewrite tappenv_over_appenv_fun_correctness at 1.
    rewrite tapp_over_app_fun_correctness at 1.
    rewrite tmap_over_flatten_map_fun_correctness at 1.
    rewrite tflatten_flatten_map_either_nil_fun_correctness at 1.
    unfold tail_optim_list.
    unfold apply_steps.
    rewrite hide_use_eq.
    simpl fold_right.
    repeat rewrite optimizer_step_result.
    unfold snd.
    red; intros; split; [apply H|reflexivity].
  Qed.

  (* Java equivalent: NraOptimizer.optim1 *)  
  Definition optim1 {fruntime:foreign_runtime} {logger:optimizer_logger string algenv} (p: algenv) :=
    talgenv_map_deep (head_optim "1") p.

  Lemma optim1_correctness {model:basic_model} {logger:optimizer_logger string algenv} (p:algenv) :
    p ⇒ optim1 p.
  Proof.
    unfold optim1.
    assert (p ⇒ talgenv_map_deep (head_optim "1") p).
    apply algenv_map_deep_correctness.
    intro p'.
    rewrite head_optim_correctness at 1.
    reflexivity.
    assumption.
  Qed.

  (* Java equivalent: NraOptimizer.optim2 *)  
  Definition optim2 {fruntime:foreign_runtime} {logger:optimizer_logger string algenv} (p: algenv) :=
    talgenv_map_deep (tail_optim "") p.

  Lemma optim2_correctness {model:basic_model} {logger:optimizer_logger string algenv} (p:algenv) :
    p ⇒ optim2 p.
  Proof.
    unfold optim2.
    assert (p ⇒ talgenv_map_deep (tail_optim "") p).
    apply algenv_map_deep_correctness.
    intro p'.
    rewrite tail_optim_correctness at 1.
    reflexivity.
    assumption.
  Qed.

  (* Java equivalent: NraOptimizer.optimize *)
  Definition toptim {fruntime:foreign_runtime} {logger:optimizer_logger string algenv} (p:algenv) :=
    let pass1p := (optim_size (optim_iter optim1 5) p) in
    (optim_size (optim_iter optim2 15) pass1p).

  Lemma toptim_correctness {model:basic_model} {logger:optimizer_logger string algenv} p:
    p ⇒ toptim p.
  Proof.
    unfold toptim.
    rewrite optim_size_correctness at 1; try reflexivity.
    rewrite optim_size_correctness at 1; try reflexivity.
    intros p1.
    rewrite optim_iter_correctness at 1; try reflexivity.
    intros p2.
    rewrite optim2_correctness at 1; try reflexivity.
    intros p1.
    rewrite optim_iter_correctness at 1; try reflexivity.
    intros p2.
    rewrite optim1_correctness at 1; try reflexivity.
  Qed.

End TOptimEnvFunc.

(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
