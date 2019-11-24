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

Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import String.
Require Import List.
Require Import ListSet.
Require Import Utils.
Require Import CommonSystem.
Require Import cNRAEnvSystem.
Require Import NRAEnvSystem.
Require Import OptimizerStep.
Require Import OptimizerLogger.
Require Import NRAEnvRewrite.
Require Import TNRAEnvRewrite.

Section NRAEnvOptimizer.
  Open Scope nraenv_scope.
  
  (* *************************** *)

  Ltac tcorrectness_prover :=
          simpl; repeat progress (try match goal with
        | [|- context [match ?p with | _ => _ end] ] => destruct p
      end; try reflexivity; try unfold Equivalence.equiv in *; try subst).

  Ltac tprove_correctness p :=
    destruct p;
    tcorrectness_prover.

  (* *************************** *)

  Lemma tnraenv_rewrites_to_trans {model:basic_model} p1 p2 p3:
    p1 ⇒ₓ p2 -> p2 ⇒ₓ p3 -> p1 ⇒ₓ p3.
  Proof.
    apply transitivity.
  Qed.

  Lemma AUX {model:basic_model} f p p':
    (forall p, p ⇒ₓ f p) -> p ⇒ₓ p' -> p ⇒ₓ f p'.
  Proof.
    intros.
    rewrite H0 at 1.
    rewrite (H p') at 1.
    reflexivity.
  Qed.

  (** Apply the function f to the direct child of p *)
  Section rewriter.
    Context {fruntime:foreign_runtime}.

    Definition nraenv_map (f: nraenv -> nraenv) (p: nraenv) :=
      match p with
      | NRAEnvID => NRAEnvID
      | NRAEnvConst rd => NRAEnvConst rd
      | NRAEnvBinop bop op1 op2 => NRAEnvBinop bop (f op1) (f op2)
      | NRAEnvUnop uop op1 => NRAEnvUnop uop (f op1)
      | NRAEnvMap op1 op2 => NRAEnvMap (f op1) (f op2)
      | NRAEnvMapProduct op1 op2 => NRAEnvMapProduct (f op1) (f op2)
      | NRAEnvProduct op1 op2 => NRAEnvProduct (f op1) (f op2)
      | NRAEnvSelect op1 op2 => NRAEnvSelect (f op1) (f op2)
      | NRAEnvEither op1 op2 => NRAEnvEither (f op1) (f op2)
      | NRAEnvEitherConcat op1 op2 => NRAEnvEitherConcat (f op1) (f op2)
      | NRAEnvDefault op1 op2 => NRAEnvDefault (f op1) (f op2)
      | NRAEnvApp op1 op2 => NRAEnvApp (f op1) (f op2)
      | NRAEnvGetConstant s => NRAEnvGetConstant s
      | NRAEnvEnv => NRAEnvEnv
      | NRAEnvAppEnv op1 op2 => NRAEnvAppEnv (f op1) (f op2)
      | NRAEnvMapEnv op1 => NRAEnvMapEnv (f op1)
      | NRAEnvFlatMap op1 op2 => NRAEnvFlatMap (f op1) (f op2)
      | NRAEnvJoin op1 op2 op3 => NRAEnvJoin (f op1) (f op2) (f op3)
      | NRAEnvNaturalJoin op1 op2 => NRAEnvNaturalJoin (f op1) (f op2)
      | NRAEnvProject sl op1 => NRAEnvProject sl (f op1)
      | NRAEnvGroupBy s sl op1 => NRAEnvGroupBy s sl (f op1)
      | NRAEnvUnnest a b op1 => NRAEnvUnnest a b (f op1)
      end.
    
    (** Apply the function f to all subexpression fo p. *)
    (* Fixpoint nraenv_map_deep (f: nraenv -> nraenv) (p: nraenv) := *)
    (*   f (nraenv_map (fun p' => nraenv_map_deep f p') p). *)
    Fixpoint nraenv_map_deep (f: nraenv -> nraenv) (p: nraenv) :=
      match p with
      | NRAEnvID => f NRAEnvID
      | NRAEnvConst rd => f (NRAEnvConst rd)
      | NRAEnvBinop bop op1 op2 => f (NRAEnvBinop bop (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvUnop uop op1 => f (NRAEnvUnop uop (nraenv_map_deep f op1))
      | NRAEnvMap op1 op2 => f (NRAEnvMap (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvMapProduct op1 op2 => f (NRAEnvMapProduct (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvProduct op1 op2 => f (NRAEnvProduct (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvSelect op1 op2 => f (NRAEnvSelect (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvDefault op1 op2 => f (NRAEnvDefault (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvEither op1 op2 => f (NRAEnvEither (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvEitherConcat op1 op2 => f (NRAEnvEitherConcat (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvApp op1 op2 => f (NRAEnvApp (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvGetConstant s => f (NRAEnvGetConstant s)
      | NRAEnvEnv => f NRAEnvEnv
      | NRAEnvAppEnv op1 op2 => f (NRAEnvAppEnv (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvMapEnv op1 => f (NRAEnvMapEnv (nraenv_map_deep f op1))
      | NRAEnvFlatMap op1 op2 => f (NRAEnvFlatMap (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvJoin op1 op2 op3 => f (NRAEnvJoin (nraenv_map_deep f op1) (nraenv_map_deep f op2) (nraenv_map_deep f op3))
      | NRAEnvNaturalJoin op1 op2 => f (NRAEnvNaturalJoin (nraenv_map_deep f op1) (nraenv_map_deep f op2))
      | NRAEnvProject sl op1 => f (NRAEnvProject sl (nraenv_map_deep f op1))
      | NRAEnvGroupBy s sl op1 => f (NRAEnvGroupBy s sl (nraenv_map_deep f op1))
      | NRAEnvUnnest a b op1 => f (NRAEnvUnnest a b (nraenv_map_deep f op1))
    end.
  End rewriter.

  Section dup.
    (* optimization for distinct *)
    Definition nraenv_nodupA {fruntime:foreign_runtime} (q:nraenv) : Prop :=
      nodupA (nraenv_to_nraenv_core q).

    Fixpoint nodupA_checker {fruntime:foreign_runtime} (p:nraenv) : bool
    := match p with
       | NRAEnvUnop OpDistinct _ => true
       | NRAEnvBinop OpBagDiff p₁ p₂ => nodupA_checker p₁
       | _ => false
       end.

    Lemma nodupA_checker_correct {bm:basic_model} (p:nraenv) :
      nodupA_checker p = true -> nraenv_nodupA p.
    Proof.
      induction p; simpl; try discriminate.
      - destruct b; try discriminate.
        intros nd.
        repeat red; intros.
        simpl in H.
        unfold olift2 in H.
        match_case_in H
        ; intros; rewrite H0 in H; try discriminate.
        match_case_in H
        ; intros; rewrite H1 in H; try discriminate.
        unfold rondcoll2 in H.
        apply some_lift in H.
        destruct H as [? ? ?].
        subst.
        unfold ondcoll2 in e.
        match_destr_in e.
        match_destr_in e.
        invcs e.
        apply bminus_NoDup.
        specialize (IHp1 nd).
        specialize (IHp1 h c dn_c env dn_env x dn_x _ H0).
        simpl in IHp1.
        trivial.
      - destruct u; try discriminate.
        intros _ .
        repeat red; intros.
        simpl in H.
        unfold olift in H.
        match_case_in H
        ; intros; rewrite H0 in H; try discriminate.
        unfold rondcoll in H.
        apply some_lift in H.
        destruct H as [? ? ?].
        invcs e0.
        unfold ondcoll in e.
        match_destr_in e.
        invcs e.
        apply bdistinct_NoDup.
    Qed.

    Definition dup_elim_fun {fruntime:foreign_runtime} (p:nraenv) :=
      match p with
      | NRAEnvUnop OpDistinct q  =>
        if nodupA_checker q then q else p
      | _ => p
      end.
    
    Lemma dup_elim_fun_correctness {bm:basic_model} (p:nraenv) :
      dup_elim_fun p ≡ₓ p.
    Proof.
      destruct p; simpl; try reflexivity.
      destruct u; simpl; try reflexivity.
      match_case; try reflexivity.
      intros nd.
      symmetry.
      rewrite lift_nraenv_eq_to_nraenv_core_eq. simpl.
      rewrite dup_elim.
      reflexivity.
      apply nodupA_checker_correct; trivial.
    Qed.

  End dup.
  
  Definition tnraenv_map {fruntime:foreign_runtime} := nraenv_map.

  Lemma tnraenv_map_correctness {model:basic_model}:
    forall f: nraenv -> nraenv,
    forall p: nraenv,
      (forall p', p' ⇒ₓ f p') -> p ⇒ₓ tnraenv_map f p.
  Proof.
    intros.
    nraenv_cases (induction p) Case; try solve [simpl; apply Hf]; simpl;
    try reflexivity;
    try (rewrite (H p1) at 1; rewrite (H p2) at 1; rewrite (H p3) at 1; reflexivity);
    try (rewrite (H p1) at 1; rewrite (H p2) at 1; reflexivity);
    try rewrite (H p) at 1; try reflexivity.
  Qed.

  Definition tnraenv_map_deep {fruntime:foreign_runtime} := nraenv_map_deep.
  
  Lemma nraenv_map_deep_correctness {model:basic_model}:
    forall f: nraenv -> nraenv,
    forall p: nraenv,
      (forall p', p' ⇒ₓ f p') -> p ⇒ₓ tnraenv_map_deep f p.
  Proof.
    intros f p Hf.
    nraenv_cases (induction p) Case; try solve [simpl; apply Hf];
    try reflexivity; simpl;
    try (rewrite IHp1 at 1; rewrite IHp2 at 1; rewrite IHp3 at 1; rewrite Hf at 1; reflexivity);
    try (rewrite IHp1 at 1; rewrite IHp2 at 1; rewrite Hf at 1; reflexivity);
    rewrite IHp at 1; rewrite Hf at 1; reflexivity.
  Qed.

  (****************)

  (* P1 ∧ P2 ⇒ₓ P2 ∧ P1 *)

  Definition tand_comm_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvBinop OpAnd op1 op2 => NRAEnvBinop OpAnd op2 op1
      | _ => p
    end.

  Lemma tand_comm_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tand_comm_fun p.
  Proof.
    tprove_correctness p.
    apply tand_comm_arrow.
  Qed.
  Hint Rewrite @tand_comm_fun_correctness : optim_correct.

  Definition tand_comm_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "and commute" (* name *)
         "Swap the arguments to the boolean and operator" (* description *)
         "tand_comm_fun" (* lemma name *)
         tand_comm_fun (* lemma *).

  Definition tand_comm_step_correct {model:basic_model}
    := mkOptimizerStepModel tand_comm_step tand_comm_fun_correctness.

  (* σ{P1 ∧ P2}(P) ⇒ₓ σ{P2 ∧ P1}(P) *) (* XXX Why neessary ? *)

  Definition tselect_and_comm_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvSelect (NRAEnvBinop OpAnd op1 op2) op =>
        NRAEnvSelect (NRAEnvBinop OpAnd op2 op1) op
      | _ => p
    end.

  Lemma tselect_and_comm_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tselect_and_comm_fun p.
  Proof.
    tprove_correctness p.
    apply tselect_and_comm_arrow.
  Qed.
  Hint Rewrite @tselect_and_comm_fun_correctness : optim_correct.

  Definition tselect_and_comm_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "select/and swap" (* name *)
         "Swap the arguments to the boolean operator when it is used in a selection" (* description *)
         "tselect_and_comm_fun" (* lemma name *)
         tselect_and_comm_fun (* lemma *).

  Definition tselect_and_comm_step_correct {model:basic_model}
    := mkOptimizerStepModel tselect_and_comm_step tselect_and_comm_fun_correctness.

  (** σ⟨ q ⟩(q₁ ⋃ q₂) ⇒ σ⟨ q ⟩(q₁) ⋃ σ⟨ q ⟩(q₂) *)

  Definition select_union_distr_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvSelect op (NRAEnvBinop OpBagUnion op1 op2) =>
        NRAEnvBinop OpBagUnion (NRAEnvSelect op op1) (NRAEnvSelect op op2)
      | _ => p
    end.

  Lemma select_union_distr_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ select_union_distr_fun p.
  Proof.
    tprove_correctness p.
    apply tselect_union_distr.
  Qed.
  Hint Rewrite @select_union_distr_fun_correctness : optim_correct.

  Definition select_union_distr_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "select/union distr" (* name *)
         "Pushes selection through union" (* description *)
         "select_union_distr_fun" (* lemma name *)
         select_union_distr_fun (* lemma *).

  Definition select_union_distr_step_correct {model:basic_model}
    := mkOptimizerStepModel select_union_distr_step select_union_distr_fun_correctness.

  (* σ{P1}(σ{P2}(P3)) ⇒ₓ σ{P2 ∧ P1}(P3)) *)

  Definition tselect_and_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvSelect op1 (NRAEnvSelect op2 op) =>
        NRAEnvSelect (NRAEnvBinop OpAnd op2 op1) op
      | _ => p
    end.

  Lemma tselect_and_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tselect_and_fun p.
  Proof.
    tprove_correctness p.
    apply tselect_and_arrow.
  Qed.
  Hint Rewrite @tselect_and_fun_correctness : optim_correct.

  Definition tselect_and_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "select/select fusion" (* name *)
         "Fuse nested selections into a single selection using a conjunction" (* description *)
         "tselect_and_fun" (* lemma name *)
         tselect_and_fun (* lemma *).

  Definition tselect_and_step_correct {model:basic_model}
    := mkOptimizerStepModel tselect_and_step tselect_and_fun_correctness.

  (* [ a1 : p1; a2 : p2 ].a2 ⇒ₓ p2 *)

  Definition tdot_from_duplicate_r_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvUnop (OpDot s2)
               (NRAEnvBinop OpRecConcat (NRAEnvUnop (OpRec s1) op1) (NRAEnvUnop (OpRec s2') op2)) =>
        if s2 == s2' then
          op2
        else
          p
      | _ => p
    end.

  Lemma tdot_from_duplicate_r_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tdot_from_duplicate_r_fun p.
  Proof.
    tprove_correctness p. 
    apply tenvdot_from_duplicate_r_arrow.
  Qed.
  Hint Rewrite @tdot_from_duplicate_r_fun_correctness : optim_correct.

  Definition tdot_from_duplicate_r_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "dot/concat/rec right dup" (* name *)
         "Simplifies field lookup of a concatenation with a record creation of that field" (* description *)
         "tdot_from_duplicate_r_fun" (* lemma name *)
         tdot_from_duplicate_r_fun (* lemma *).

  Definition tdot_from_duplicate_r_step_correct {model:basic_model}
    := mkOptimizerStepModel tdot_from_duplicate_r_step tdot_from_duplicate_r_fun_correctness.

  (* [ a1 : p1; a2 : p2 ].a1 ⇒ₓ p1 *)

  Definition tdot_from_duplicate_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvUnop (OpDot s1)
               (NRAEnvBinop OpRecConcat (NRAEnvUnop (OpRec s1') op1) (NRAEnvUnop (OpRec s2) op2)) =>
        if (s1 <> s2) then
          if s1 == s1' then op1
          else p
        else p
      | _ => p
    end.

  Lemma tdot_from_duplicate_l_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tdot_from_duplicate_l_fun p.
  Proof.
    tprove_correctness p. 
    apply tenvdot_from_duplicate_l_arrow.
    assumption.
  Qed.
  Hint Rewrite @tdot_from_duplicate_l_fun_correctness : optim_correct.

  Definition tdot_from_duplicate_l_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "dot/concat/rec left dup" (* name *)
         "Simplifies field lookup of a concatenation with a record creation of that field" (* description *)
         "tdot_from_duplicate_l_fun" (* lemma name *)
         tdot_from_duplicate_l_fun (* lemma *).

  Definition tdot_from_duplicate_l_step_correct {model:basic_model}
    := mkOptimizerStepModel tdot_from_duplicate_l_step tdot_from_duplicate_l_fun_correctness.

  (* ♯flatten({ p }) ⇒ₓ p when p's output type is a collection *)
  Definition tflatten_coll_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvUnop OpFlatten (NRAEnvUnop OpBag p) => p
      | _ => p
    end.

  Lemma tflatten_coll_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tflatten_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tenvflatten_coll_arrow.
  Qed.
  Hint Rewrite @tflatten_coll_fun_correctness : optim_correct.
  
  Definition tflatten_coll_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/coll" (* name *)
         "Simplify flatten of a bag constructor" (* description *)
         "tflatten_coll_fun" (* lemma name *)
         tflatten_coll_fun (* lemma *).

  Definition tflatten_coll_step_correct {model:basic_model}
    := mkOptimizerStepModel tflatten_coll_step tflatten_coll_fun_correctness.

  (* p ⊕ [] ⇒ₓ p when p returns a record *)
  Definition tconcat_empty_record_r_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      |  NRAEnvBinop OpRecConcat p (NRAEnvConst (drec [])) =>
        p
      | _ => p
    end.

  Lemma tconcat_empty_record_r_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tconcat_empty_record_r_fun p.
  Proof.
    tprove_correctness p.
    apply tconcat_empty_record_r_arrow.
  Qed.
  Hint Rewrite @tconcat_empty_record_r_fun_correctness : optim_correct.

  Definition tconcat_empty_record_r_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "concat/nil right" (* name *)
         "Remove concatenation with an empty record" (* description *)
         "tconcat_empty_record_r_fun" (* lemma name *)
         tconcat_empty_record_r_fun (* lemma *).

  Definition tconcat_empty_record_r_step_correct {model:basic_model}
    := mkOptimizerStepModel tconcat_empty_record_r_step tconcat_empty_record_r_fun_correctness.

  (* [] ⊕ p ⇒ₓ p when p returns a record *)
  Definition tconcat_empty_record_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      |  NRAEnvBinop OpRecConcat (NRAEnvConst (drec [])) p =>
         p
      | _ => p
    end.

  Lemma tconcat_empty_record_l_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tconcat_empty_record_l_fun p.
  Proof.
    tprove_correctness p.
    apply tconcat_empty_record_l_arrow.
  Qed.
  Hint Rewrite @tconcat_empty_record_l_fun_correctness : optim_correct.

    Definition tconcat_empty_record_l_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "concat/nil left" (* name *)
         "Remove concatenation with an empty record" (* description *)
         "tconcat_empty_record_l_fun" (* lemma name *)
         tconcat_empty_record_l_fun (* lemma *).

  Definition tconcat_empty_record_l_step_correct {model:basic_model}
    := mkOptimizerStepModel tconcat_empty_record_l_step tconcat_empty_record_l_fun_correctness.

  Definition tdot_over_concat_r_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    |  NRAEnvUnop (OpDot a₂) (NRAEnvBinop OpRecConcat q₁ (NRAEnvUnop (OpRec a₁) q₂)) =>
       if a₁ == a₂
       then q₂
       else NRAEnvUnop (OpDot a₂) q₁
      | _ => p
    end.

  Lemma tdot_over_concat_r_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tdot_over_concat_r_fun p.
  Proof.
    tprove_correctness p.
    - apply tdot_over_concat_eq_r_arrow.
    - apply tdot_over_concat_neq_r_arrow.
      congruence.
  Qed.
  Hint Rewrite @tdot_over_concat_r_fun_correctness : optim_correct.

  Definition tdot_over_concat_r_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "dot/concat/rec right" (* name *)
         "Simplify field lookup of a concatenation of a record construction" (* description *)
         "tdot_over_concat_r_fun" (* lemma name *)
         tdot_over_concat_r_fun (* lemma *).

  Definition tdot_over_concat_r_step_correct {model:basic_model}
    := mkOptimizerStepModel tdot_over_concat_r_step tdot_over_concat_r_fun_correctness.

  Definition tdot_over_concat_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    |  NRAEnvUnop (OpDot a₂) (NRAEnvBinop OpRecConcat (NRAEnvUnop (OpRec a₁) q₁) q₂) =>
       if a₁ == a₂
       then p
       else NRAEnvUnop (OpDot a₂) q₂
      | _ => p
    end.

  Lemma tdot_over_concat_l_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tdot_over_concat_l_fun p.
  Proof.
    tprove_correctness p.
    apply tdot_over_concat_neq_l_arrow.
    congruence.
  Qed.
  Hint Rewrite @tdot_over_concat_l_fun_correctness : optim_correct.

   Definition tdot_over_concat_l_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "dot/concat/rec left" (* name *)
         "Simplify field lookup of a concatenation of a record construction" (* description *)
         "tdot_over_concat_l_fun" (* lemma name *)
         tdot_over_concat_l_fun (* lemma *).

  Definition tdot_over_concat_l_step_correct {model:basic_model}
    := mkOptimizerStepModel tdot_over_concat_l_step tdot_over_concat_l_fun_correctness.
  
  (* p ⊗ [] ⇒ₓ { p } when p returns a record *)
  Definition tmerge_empty_record_r_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      |  NRAEnvBinop OpRecMerge p (NRAEnvConst (drec [])) =>
         NRAEnvUnop OpBag p
      | _ => p
    end.

  Lemma tmerge_empty_record_r_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmerge_empty_record_r_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_empty_record_r_arrow.
  Qed.
  Hint Rewrite @tmerge_empty_record_r_fun_correctness : optim_correct.

  Definition tmerge_empty_record_r_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "merge-concat/nil right" (* name *)
         "Simplify merge concat of an empty record" (* description *)
         "tmerge_empty_record_r_fun" (* lemma name *)
         tmerge_empty_record_r_fun (* lemma *).

  Definition tmerge_empty_record_r_step_correct {model:basic_model}
    := mkOptimizerStepModel tmerge_empty_record_r_step tmerge_empty_record_r_fun_correctness.

  (* [] ⊗ p ⇒ₓ { p } when p returns a record *)
  Definition tmerge_empty_record_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      |  NRAEnvBinop OpRecMerge (NRAEnvConst (drec [])) p =>
         NRAEnvUnop OpBag p
      | _ => p
    end.

  Lemma tmerge_empty_record_l_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmerge_empty_record_l_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_empty_record_l_arrow.
  Qed.
  Hint Rewrite @tmerge_empty_record_l_fun_correctness : optim_correct.

  Definition tmerge_empty_record_l_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "merge-concat/nil left" (* name *)
         "Simplify merge concat of an empty record" (* description *)
         "tmerge_empty_record_l_fun" (* lemma name *)
         tmerge_empty_record_l_fun (* lemma *).

  Definition tmerge_empty_lecord_l_step_correct {model:basic_model}
    := mkOptimizerStepModel tmerge_empty_record_l_step tmerge_empty_record_l_fun_correctness.

  (* χ⟨ ID ⟩( p ) ⇒ₓ p *)
  Definition tmap_into_id_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvMap NRAEnvID p => p
      | _ => p
    end.

  Lemma tmap_into_id_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmap_into_id_fun p.
  Proof.
    tprove_correctness p.
    apply tenvmap_into_id_arrow.
  Qed.
  Hint Rewrite @tmap_into_id_fun_correctness : optim_correct.

  Definition tmap_into_id_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "map/id" (* name *)
         "Simplify map of ID" (* description *)
         "tmap_into_id_fun" (* lemma name *)
         tmap_into_id_fun (* lemma *).

  Definition tmap_into_id_step_correct {model:basic_model}
    := mkOptimizerStepModel tmap_into_id_step tmap_into_id_fun_correctness.

  (* ♯flatten(χ⟨ { p1 } ⟩( p2 )) ⇒ₓ χ⟨ p1 ⟩( p2 ) *)
  Definition tflatten_map_coll_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvUnop OpFlatten (NRAEnvMap (NRAEnvUnop OpBag p1) p2) =>
        NRAEnvMap p1 p2
      | _ => p
    end.

  Lemma tflatten_map_coll_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tflatten_map_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tenvflatten_map_coll_arrow.
  Qed.
  Hint Rewrite @tflatten_map_coll_fun_correctness : optim_correct.

  Definition tflatten_map_coll_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/map/coll" (* name *)
         "Simplify flatten of the map of a bag constructor" (* description *)
         "tflatten_map_coll_fun" (* lemma name *)
         tflatten_map_coll_fun (* lemma *).

  Definition tflatten_map_coll_step_correct {model:basic_model}
    := mkOptimizerStepModel tflatten_map_coll_step tflatten_map_coll_fun_correctness.

  Definition tflatten_flatten_map_either_nil_fun {fruntime:foreign_runtime} (p: nraenv) :=
      match p with
        NRAEnvUnop OpFlatten
                   (NRAEnvUnop OpFlatten (NRAEnvMap (NRAEnvApp (NRAEnvEither p₁ (NRAEnvConst (dcoll nil))) p₂) p₃)) =>
        NRAEnvUnop OpFlatten (NRAEnvMap (NRAEnvApp
                                          (NRAEnvEither (NRAEnvUnop OpFlatten p₁)
                                                        (NRAEnvConst (dcoll nil))) p₂) p₃)
      | _ => p
    end.

  Lemma tflatten_flatten_map_either_nil_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tflatten_flatten_map_either_nil_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_flatten_map_either_nil.
  Qed.

  Hint Rewrite @tflatten_flatten_map_either_nil_fun_correctness : optim_correct.

  Definition tflatten_flatten_map_either_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/flatten/map/app/either/nil right" (* name *)
         "Simplify nested flatten of an either nil (under an application)" (* description *)
         "tflatten_flatten_map_either_nil_fun" (* lemma name *)
         tflatten_flatten_map_either_nil_fun (* lemma *).

  Definition tflatten_flatten_map_either_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tflatten_flatten_map_either_nil_step tflatten_flatten_map_either_nil_fun_correctness.

  (* χ⟨ P1 ⟩( χ⟨ P2 ⟩( P3 ) ) ⇒ₓ χ⟨ P1 ◯ P2 ⟩( P3 ) *)
  Definition tmap_map_compose_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvMap p1 (NRAEnvMap p2 p3) => NRAEnvMap (NRAEnvApp p1 p2) p3
      | _ => p
    end.

  Lemma tmap_map_compose_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmap_map_compose_fun p.
  Proof.
    tprove_correctness p.
    apply tenvmap_map_compose_arrow.
  Qed.
  Hint Rewrite @tmap_map_compose_fun_correctness : optim_correct.

  Definition tmap_map_compose_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "map/map" (* name *)
         "Fuses nested maps together" (* description *)
         "tmap_map_compose_fun" (* lemma name *)
         tmap_map_compose_fun (* lemma *).

  Definition tmap_map_compose_step_correct {model:basic_model}
    := mkOptimizerStepModel tmap_map_compose_step tmap_map_compose_fun_correctness.

  (* χ⟨ P1 ⟩( { P2 } ) ⇒ₓ { P1 ◯ P2 } *)
  Definition tmap_singleton_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvMap p1 (NRAEnvUnop OpBag p2) => NRAEnvUnop OpBag (NRAEnvApp p1 p2)
      | _ => p
    end.

  Lemma tmap_singleton_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmap_singleton_fun p.
  Proof.
    tprove_correctness p.
    apply tenvmap_singleton_arrow.
  Qed.
  Hint Rewrite @tmap_singleton_fun_correctness : optim_correct.

  Definition tmap_singleton_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "map/coll" (* name *)
         "Lowers a map over a bag constructor" (* description *)
         "tmap_singleton_fun" (* lemma name *)
         tmap_singleton_fun (* lemma *).

  Definition tmap_singleton_step_correct {model:basic_model}
    := mkOptimizerStepModel tmap_singleton_step tmap_singleton_fun_correctness.

  (* p ◯ ID ⇒ₓ p *)
  Definition tapp_over_id_r_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvApp p NRAEnvID => p
      | _ => p
    end.

  Lemma tapp_over_id_r_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_id_r_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_id_r_arrow.
  Qed.
  Hint Rewrite @tapp_over_id_r_fun_correctness : optim_correct.

  Definition tapp_over_id_r_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/id arg" (* name *)
         "Simplifies application to ID" (* description *)
         "tapp_over_id_r_fun" (* lemma name *)
         tapp_over_id_r_fun (* lemma *).

  Definition tapp_over_id_r_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_id_r_step tapp_over_id_r_fun_correctness.

  (* ENV ◯ p ⇒ₓ ENV *)
  Definition tapp_over_env_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvApp NRAEnvEnv p => NRAEnvEnv
      | _ => p
    end.

  Lemma tapp_over_env_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_env_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_env_arrow.
  Qed.
  Hint Rewrite @tapp_over_env_fun_correctness : optim_correct.

  Definition tapp_over_env_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/env body" (* name *)
         "Simplify applications of ENV" (* description *)
         "tapp_over_env_fun" (* lemma name *)
         tapp_over_env_fun (* lemma *).

  Definition tapp_over_env_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_env_step tapp_over_env_fun_correctness.
  
  (* ID ◯ p ⇒ₓ p *)
  Definition tapp_over_id_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvApp NRAEnvID p => p
      | _ => p
    end.

  Lemma tapp_over_id_l_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_id_l_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_id_l_arrow.
  Qed.
  Hint Rewrite @tapp_over_id_l_fun_correctness : optim_correct.

  Definition tapp_over_id_l_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/id body" (* name *)
         "Simplify applications of ID" (* description *)
         "tapp_over_id_l_fun" (* lemma name *)
         tapp_over_id_l_fun (* lemma *).

  Definition tapp_over_id_l_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_id_l_step tapp_over_id_l_fun_correctness.

  (* ignores_id p1 -> p1 ◯ p2 ⇒ₓ p1 *)
  Definition tapp_over_ignoreid_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvApp p1 p2 =>
      if (nraenv_ignores_id_fun p1)
      then p1 else p
    | _ => p
    end.

  Lemma tapp_over_ignoreid_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_ignoreid_fun p.
  Proof.
    destruct p; try solve [unfold tnraenv_rewrites_to; simpl; auto].
    simpl.
    case_eq (nraenv_ignores_id_fun p1); intros; try reflexivity.
    apply tapp_over_ignoreid_arrow.
    rewrite <- nraenv_ignores_id_eq in H.
    apply nraenv_ignores_id_nraenv_core_eq; assumption.
  Qed.

  Definition tapp_over_ignoreid_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/ignore-id body" (* name *)
         "Simplify application of expressions that ignore ID" (* description *)
         "tapp_over_ignoreid_fun" (* lemma name *)
         tapp_over_ignoreid_fun (* lemma *).

  Definition tapp_over_ignoreid_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_ignoreid_step tapp_over_ignoreid_fun_correctness.

  (* ENV ◯ₑ p ⇒ₓ p *)
  Definition tappenv_over_env_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvAppEnv NRAEnvEnv p => p
      | _ => p
    end.

  Lemma tappenv_over_env_l_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_over_env_l_fun p.
  Proof.
    destruct p; try solve [unfold tnraenv_rewrites_to; simpl; auto].
    destruct p1; try solve [unfold tnraenv_rewrites_to; simpl; auto].
    simpl.
    apply tappenv_over_env_l_arrow.
  Qed.

  Definition tappenv_over_env_l_step {fruntime:foreign_runtime}
      := mkOptimizerStep
         "app-env/env body" (* name *)
         "Simplify environment applications of the environment" (* description *)
         "tappenv_over_env_l_fun" (* lemma name *)
         tappenv_over_env_l_fun (* lemma *).

  Definition tappenv_over_env_l_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_env_l_step tappenv_over_env_l_fun_correctness.


  (* p ◯ₑ ENV ⇒ₓ p *)
  Definition tappenv_over_env_r_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvAppEnv p NRAEnvEnv => p
      | _ => p
    end.

  Lemma tappenv_over_env_r_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_over_env_r_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_env_r_arrow.
  Qed.

  Definition tappenv_over_env_r_step {fruntime:foreign_runtime}
      := mkOptimizerStep
         "app-env/env arg" (* name *)
         "Simplify environment applications to the environment" (* description *)
         "tappenv_over_env_r_fun" (* lemma name *)
         tappenv_over_env_r_fun (* lemma *).

  Definition tappenv_over_env_r_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_env_r_step tappenv_over_env_r_fun_correctness.

  (* ignores_env p1 -> p1 ◯ₑ p2 ⇒ₓ p1 *)
  Definition tappenv_over_ignoreenv_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvAppEnv p1 p2 =>
      if (nraenv_ignores_env_fun p1)
      then p1 else p
    | _ => p
    end.

  Lemma tappenv_over_ignoreenv_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_over_ignoreenv_fun p.
  Proof.
    destruct p; try solve [unfold tnraenv_rewrites_to; simpl; auto].
    simpl.
    case_eq (nraenv_ignores_env_fun p1); intros; try reflexivity.
    apply tappenv_over_ignoreenv_arrow.
    rewrite <- nraenv_ignores_env_eq in H.
    apply nraenv_ignores_env_nraenv_core_eq; assumption.
  Qed.

  Definition tappenv_over_ignoreenv_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/ignore-env arg" (* name *)
         "Simplify environment applications that ignore the environment" (* description *)
         "tappenv_over_ignoreenv_fun" (* lemma name *)
         tappenv_over_ignoreenv_fun (* lemma *).

  Definition tappenv_over_ignoreenv_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_ignoreenv_step tappenv_over_ignoreenv_fun_correctness.

  (* (p1 ◯ p2) ◯ p3 ⇒ₓ p1 ◯ (p2 ◯ p3) *)
  Definition tapp_over_app_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvApp (NRAEnvApp p1 p2) p3 =>
        NRAEnvApp p1 (NRAEnvApp p2 p3)
      | _ => p
    end.

  Lemma tapp_over_app_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_app_fun p.
  Proof.
    destruct p; try solve [unfold tnraenv_rewrites_to; simpl; auto].
    destruct p1; try solve [unfold tnraenv_rewrites_to; simpl; auto].
    simpl.
    apply tapp_over_app_arrow.
  Qed.
  Hint Rewrite @tapp_over_app_fun_correctness : optim_correct.

  Definition tapp_over_app_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/app" (* name *)
         "Reorder nested applications" (* description *)
         "tapp_over_app_fun" (* lemma name *)
         tapp_over_app_fun (* lemma *).

  Definition tapp_over_app_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_app_step tapp_over_app_fun_correctness.

  (* (p1 ◯ₑ p2) ◯ₑ p3 ⇒ₓ p1 ◯ₑ (p2 ◯ₑ p3) *)
  Definition tappenv_over_appenv_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvAppEnv (NRAEnvAppEnv p1 p2) p3 =>
        NRAEnvAppEnv p1 (NRAEnvAppEnv p2 p3)
      | _ => p
    end.

  Lemma tappenv_over_appenv_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_over_appenv_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_appenv_arrow.
  Qed.
  Hint Rewrite @tappenv_over_appenv_fun_correctness : optim_correct.

   Definition tappenv_over_appenv_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/app-env" (* name *)
         "Reorder nested environment applications" (* description *)
         "tappenv_over_appenv_fun" (* lemma name *)
         tappenv_over_appenv_fun (* lemma *).

  Definition tappenv_over_appenv_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_appenv_step tappenv_over_appenv_fun_correctness.

  (* ignores_id p3 -> (p1 ◯ p2) ◯ₑ p3 ⇒ₓ (p1 ◯ₑ p3) ◯ (p2 ◯ₑ p3) *)
  Definition tappenv_over_app_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvAppEnv (NRAEnvApp p1 p2) p3 =>
        if (nraenv_ignores_env_fun p1) then
          NRAEnvApp p1(NRAEnvAppEnv p2 p3)
        else if (nraenv_ignores_id_fun p3) then
        NRAEnvApp (NRAEnvAppEnv p1 p3) (NRAEnvAppEnv p2 p3)
      else p
    | _ => p
    end.

  Lemma tappenv_over_app_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_over_app_fun p.
  Proof.
    destruct p; try reflexivity.
    destruct p1; try reflexivity.
    simpl.
    case_eq (nraenv_ignores_env_fun p1_1); intros.
    - apply tappenv_over_app_ie_arrow.
      rewrite <- nraenv_ignores_env_eq in H.
      generalize nraenv_ignores_env_nraenv_core_eq; intros.
      unfold nraenv_to_nraenv_core in *.
      apply H0; assumption.
    - case_eq (nraenv_ignores_id_fun p2); intros.
      + apply tappenv_over_app_arrow.
        rewrite <- nraenv_ignores_id_eq in H0.
        generalize nraenv_ignores_id_nraenv_core_eq; intros.
        unfold nraenv_to_nraenv_core in *.
        apply H1; assumption.
      + reflexivity.
  Qed.

  Hint Rewrite @tappenv_over_app_fun_correctness : optim_correct.

    Definition tappenv_over_app_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/app body" (* name *)
         "Push environment application through application" (* description *)
         "tappenv_over_app_fun" (* lemma name *)
         tappenv_over_app_fun (* lemma *).

  Definition tappenv_over_app_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_app_step tappenv_over_app_fun_correctness.

  (* ignores_id p1 -> (p1 ◯ₑ p2) ◯ p3 ⇒ₓ p1 ◯ₑ (p2 ◯ p3) *)
  Definition tapp_over_appenv_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvApp (NRAEnvAppEnv p1 p2) p3 =>
      if (nraenv_ignores_id_fun p1) then
        NRAEnvAppEnv p1 (NRAEnvApp p2 p3)
      else p
    | _ => p
    end.

  Lemma tapp_over_appenv_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_appenv_fun p.
  Proof.
    destruct p; try reflexivity.
    destruct p1; try reflexivity.
    simpl.
    case_eq (nraenv_ignores_id_fun p1_1); intros.
    - apply tapp_over_appenv_arrow.
      rewrite <- nraenv_ignores_id_eq in H.
      generalize nraenv_ignores_id_nraenv_core_eq; intros.
      unfold nraenv_to_nraenv_core in *.
      apply H0; assumption.
    - reflexivity.
  Qed.

  Definition tapp_over_appenv_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/app-env body" (* name *)
         "Push application through environment application" (* description *)
         "tapp_over_appenv_fun" (* lemma name *)
         tapp_over_appenv_fun (* lemma *).

  Definition tapp_over_appenv_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_appenv_step tapp_over_appenv_fun_correctness.

  (* (NRAEnvUnop u p1) ◯ p2 ⇒ₓ (NRAEnvUnop u (p1 ◯ p2)) *)
  Definition tapp_over_unop_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvApp (NRAEnvUnop u p1) p2 =>
        NRAEnvUnop u (NRAEnvApp p1 p2)
      | _ => p
    end.

  Lemma tapp_over_unop_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_unop_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_unop_arrow.
  Qed.
  Hint Rewrite @tapp_over_unop_fun_correctness : optim_correct.

  Definition tapp_over_unop_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/unop" (* name *)
         "Push application through unary operations" (* description *)
         "tapp_over_unop_fun" (* lemma name *)
         tapp_over_unop_fun (* lemma *).

  Definition tapp_over_unop_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_unop_step tapp_over_unop_fun_correctness.

  (* (NRAEnvUnop u p1) ◯ₑ p2 ⇒ₓ (NRAEnvUnop u (p1 ◯ₑ p2)) *)
  Definition tappenv_over_unop_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvAppEnv (NRAEnvUnop u p1) p2 =>
        NRAEnvUnop u (NRAEnvAppEnv p1 p2)
      | _ => p
    end.

  Lemma tappenv_over_unop_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_over_unop_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_unop_arrow.
  Qed.

  Definition tappenv_over_unop_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/unop" (* name *)
         "Push environment application through unary operations" (* description *)
         "tappenv_over_unop_fun" (* lemma name *)
         tappenv_over_unop_fun (* lemma *).

  Definition tappenv_over_unop_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_unop_step tappenv_over_unop_fun_correctness.

  Definition tunop_over_either_const_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvUnop u (NRAEnvEither p₁ (NRAEnvConst d)) => NRAEnvEither (NRAEnvUnop u p₁) (NRAEnvUnop u (NRAEnvConst d))
      | _ => p
    end.

  Lemma tunop_over_either_const_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tunop_over_either_const_fun p.
  Proof.
    tprove_correctness p.
    apply tunop_over_either.
  Qed.

  Definition tunop_over_either_const_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "unop/either/const right" (* name *)
         "Push a unary operation through an either construct with a right branch that builds a constant" (* description *)
         "tunop_over_either_const_fun" (* lemma name *)
         tunop_over_either_const_fun (* lemma *).

  Definition tunop_over_either_const_step_correct {model:basic_model}
    := mkOptimizerStepModel tunop_over_either_const_step tunop_over_either_const_fun_correctness.


  Definition tunop_over_either_const_app_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvUnop u (NRAEnvApp (NRAEnvEither p₁ (NRAEnvConst d)) p₃) =>
      NRAEnvApp (NRAEnvEither (NRAEnvUnop u p₁) (NRAEnvUnop u (NRAEnvConst d))) p₃
    | _ => p
    end.

  Lemma tunop_over_either_const_app_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tunop_over_either_const_app_fun p.
  Proof.
    tprove_correctness p.
    apply tunop_over_either_app.
  Qed.

  Definition tunop_over_either_const_app_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "unop/app/either/const right" (* name *)
         "Push a unary operation through an application of an either construct with a right branch that builds a constant" (* description *)
         "tunop_over_either_const_app_fun" (* lemma name *)
         tunop_over_either_const_app_fun (* lemma *).

  Definition tunop_over_either_const_app_step_correct {model:basic_model}
    := mkOptimizerStepModel tunop_over_either_const_app_step tunop_over_either_const_app_fun_correctness.
  
  (* χ⟨ p1 ⟩( p2 ) ◯ p0 ⇒ₓ χ⟨ p1 ⟩( p2 ◯ p0 ) *)
  Definition tapp_over_map_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvApp (NRAEnvMap p1 p2) p0 =>
        NRAEnvMap p1 (NRAEnvApp p2 p0)
      | _ => p
    end.

  Lemma tapp_over_map_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_map_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_map_arrow.
  Qed.
  Hint Rewrite @tapp_over_map_fun_correctness : optim_correct.

  Definition tapp_over_map_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/map" (* name *)
         "Push applications through map a body" (* description *)
         "tapp_over_map_fun" (* lemma name *)
         tapp_over_map_fun (* lemma *).

  Definition tapp_over_map_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_map_step tapp_over_map_fun_correctness.

  (* ⋈ᵈ⟨ q₁ ⟩( q₂ ) ◯ q ⇒ₓ ⋈ᵈ⟨ q₁ ⟩( q₂ ◯ q ) *)

  Definition tapp_over_mapconcat_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvApp (NRAEnvMapProduct p1 p2) p0 =>
        NRAEnvMapProduct p1 (NRAEnvApp p2 p0)
      | _ => p
    end.

  Lemma tapp_over_mapconcat_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_mapconcat_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_mapconcat_arrow.
  Qed.
  Hint Rewrite @tapp_over_mapconcat_fun_correctness : optim_correct.

  Definition tapp_over_mapconcat_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/map-concat" (* name *)
         "Push application through a map-concat body" (* description *)
         "tapp_over_mapconcat_fun" (* lemma name *)
         tapp_over_mapconcat_fun (* lemma *).

  Definition tapp_over_mapconcat_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_mapconcat_step tapp_over_mapconcat_fun_correctness.

  (* ⋈(q₁ × q₂) ◯ q ⇒ (q₁  ◯ q) × (q₁ ◯ q) *)

  Definition tapp_over_product_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvApp (NRAEnvProduct p1 p2) p0 =>
        NRAEnvProduct (NRAEnvApp p1 p0) (NRAEnvApp p2 p0)
      | _ => p
    end.

  Lemma tapp_over_product_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_product_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_product_arrow.
  Qed.
  Hint Rewrite @tapp_over_product_fun_correctness : optim_correct.

  Definition tapp_over_product_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/product" (* name *)
         "Push application through a product body" (* description *)
         "tapp_over_product_fun" (* lemma name *)
         tapp_over_product_fun (* lemma *).

  Definition tapp_over_product_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_product_step tapp_over_product_fun_correctness.

  (* χ⟨ p1 ⟩( p2 ) ◯ₑ p0 ⇒ₓ χ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ) *)

  Definition tappenv_over_map_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvAppEnv (NRAEnvMap p1 p2) p0 =>
        if (nraenv_ignores_id_fun p0)
        then NRAEnvMap (NRAEnvAppEnv p1 p0) (NRAEnvAppEnv p2 p0)
        else p
      | _ => p
    end.

  Lemma tappenv_over_map_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_over_map_fun p.
  Proof.
    destruct p; try solve [unfold tnraenv_rewrites_to; simpl; auto].
    destruct p1; try solve [unfold tnraenv_rewrites_to; simpl; auto].
    simpl.
    case_eq (nraenv_ignores_id_fun p2); intros; try reflexivity.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq. simpl.
    rewrite tappenv_over_map_arrow.
    reflexivity.
    rewrite <- nraenv_ignores_id_eq in H.
    apply nraenv_ignores_id_nraenv_core_eq; assumption.
  Qed.

  Definition tappenv_over_map_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/map" (* name *)
         "Push environment application through a map body" (* description *)
         "tappenv_over_map_fun" (* lemma name *)
         tappenv_over_map_fun (* lemma *).

  Definition tappenv_over_map_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_map_step tappenv_over_map_fun_correctness.

  (* σ⟨ p1 ⟩( p2 ) ◯ₑ p0 ⇒ₓ σ⟨ p1 ◯ₑ p0 ⟩( p2 ◯ₑ p0 ) *)

  Definition tappenv_over_select_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvAppEnv (NRAEnvSelect p1 p2) p0 =>
        if (nraenv_ignores_id_fun p0)
        then NRAEnvSelect (NRAEnvAppEnv p1 p0) (NRAEnvAppEnv p2 p0)
        else p
      | _ => p
    end.

  Lemma tappenv_over_select_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_over_select_fun p.
  Proof.
    destruct p; try solve [unfold tnraenv_rewrites_to; simpl; auto].
    destruct p1; try solve [unfold tnraenv_rewrites_to; simpl; auto].
    simpl.
    case_eq (nraenv_ignores_id_fun p2); intros; try reflexivity.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq. simpl.
    rewrite tappenv_over_select_arrow.
    reflexivity.
    rewrite <- nraenv_ignores_id_eq in H.
    apply nraenv_ignores_id_nraenv_core_eq; assumption.
  Qed.

  Definition tappenv_over_select_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/select" (* name *)
         "Push environment application through a selection body" (* description *)
         "tappenv_over_select_fun" (* lemma name *)
         tappenv_over_select_fun (* lemma *).

  Definition tappenv_over_select_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_select_step tappenv_over_select_fun_correctness.

  (* σ⟨ p1 ⟩( p2 ) ◯ p0 ⇒ₓ σ⟨ p1 ⟩( p2 ◯ p0 ) *)

  Definition tapp_over_select_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvApp (NRAEnvSelect p1 p2) p0 =>
        NRAEnvSelect p1 (NRAEnvApp p2 p0)
      | _ => p
    end.

  Lemma tapp_over_select_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_select_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_select_arrow.
  Qed.
  Hint Rewrite @tapp_over_select_fun_correctness : optim_correct.

  Definition tapp_over_select_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/slect" (* name *)
         "Push application through a selection body" (* description *)
         "tapp_over_select_fun" (* lemma name *)
         tapp_over_select_fun (* lemma *).

  Definition tapp_over_select_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_select_step tapp_over_select_fun_correctness.

  (* (NRAEnvBinop b p2 p3 ◯ p1) ⇒ₓ (NRAEnvBinop b (p2 ◯ p1) (p3 ◯ p1)) *)
  Definition tapp_over_binop_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvApp (NRAEnvBinop b p2 p3) p1 =>
        NRAEnvBinop b (NRAEnvApp p2 p1) (NRAEnvApp p3 p1)
      | _ => p
    end.

  Lemma tapp_over_binop_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_binop_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_binop_arrow.
  Qed.
  Hint Rewrite @tapp_over_binop_fun_correctness : optim_correct.

  Definition tapp_over_binop_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/binop" (* name *)
         "Push application through binary operations" (* description *)
         "tapp_over_binop_fun" (* lemma name *)
         tapp_over_binop_fun (* lemma *).

  Definition tapp_over_binop_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_binop_step tapp_over_binop_fun_correctness.

  (* { [ s1 : p1 ] } × { [ s2 : p2 ] } ⇒ₓ { [ s1 : p1; s2 : p2 ] } *)
  Definition tproduct_singletons_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvProduct (NRAEnvUnop OpBag (NRAEnvUnop (OpRec s1) p1))
                  (NRAEnvUnop OpBag (NRAEnvUnop (OpRec s2) p2)) =>
        NRAEnvUnop OpBag
               (NRAEnvBinop OpRecConcat (NRAEnvUnop (OpRec s1) p1) (NRAEnvUnop (OpRec s2) p2))
      | _ => p
    end.

  Lemma tproduct_singletons_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tproduct_singletons_fun p.
  Proof.
    tprove_correctness p.
    apply tproduct_singletons_arrow.
  Qed.
  Hint Rewrite @tproduct_singletons_fun_correctness : optim_correct.

  Definition tproduct_singletons_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "product/singleton singleton" (* name *)
         "Simplify the product of two singRemove loop comprehensions over empty loops" (* description *)
         "tproduct_singletons_fun" (* lemma name *)
         tproduct_singletons_fun (* lemma *).

  Definition tproduct_singletons_step_correct {model:basic_model}
    := mkOptimizerStepModel tproduct_singletons_step tproduct_singletons_fun_correctness.

  (* { p1 × { [] } ⇒ₓ p1 *)
  Definition tproduct_empty_right_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvProduct p1 (NRAEnvUnop OpBag (NRAEnvConst (drec nil))) => p1
    | _ => p
    end.

  Lemma tproduct_empty_right_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tproduct_empty_right_fun p.
  Proof.
    tprove_correctness p.
    apply tproduct_empty_right_arrow.
  Qed.
  Hint Rewrite @tproduct_empty_right_fun_correctness : optim_correct.

  Definition tproduct_empty_right_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "product singleton right" (* name *)
         "Eliminates empty table on the right of a Cartesian product" (* description *)
         "tproduct_empty_right_fun" (* lemma name *)
         tproduct_empty_right_fun (* lemma *).

  Definition tproduct_empty_right_step_correct {model:basic_model}
    := mkOptimizerStepModel tproduct_empty_right_step tproduct_empty_right_fun_correctness.

  (* { { [] } × p1 ⇒ₓ p1 *)
  Definition tproduct_empty_left_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvProduct (NRAEnvUnop OpBag (NRAEnvConst (drec nil))) p1 => p1
    | _ => p
    end.

  Lemma tproduct_empty_left_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tproduct_empty_left_fun p.
  Proof.
    tprove_correctness p.
    apply tproduct_empty_left_arrow.
  Qed.
  Hint Rewrite @tproduct_empty_left_fun_correctness : optim_correct.

  Definition tproduct_empty_left_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "product singleton left" (* name *)
         "Eliminates empty table on the left of a Cartesian product" (* description *)
         "tproduct_empty_left_fun" (* lemma name *)
         tproduct_empty_left_fun (* lemma *).

  Definition tproduct_empty_left_step_correct {model:basic_model}
    := mkOptimizerStepModel tproduct_empty_left_step tproduct_empty_left_fun_correctness.

  (* ♯flatten(χ⟨ χ⟨ { p3 } ⟩( p1 ) ⟩( p2 )) ⇒ₓ χ⟨ { p3 } ⟩(♯flatten(χ⟨ p1 ⟩( p2 ))) *)
  Definition tdouble_flatten_map_coll_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvUnop OpFlatten
               (NRAEnvMap (NRAEnvMap (NRAEnvUnop OpBag p3) p1) p2) =>
        NRAEnvMap (NRAEnvUnop OpBag p3)
              (NRAEnvUnop OpFlatten (NRAEnvMap p1 p2))
      | _ => p
    end.

  Lemma tdouble_flatten_map_coll_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tdouble_flatten_map_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tdouble_flatten_map_coll_arrow.
  Qed.
  Hint Rewrite @tdouble_flatten_map_coll_fun_correctness : optim_correct.

    Definition tdouble_flatten_map_coll_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/map/map/coll" (* name *)
         "Simplify flattenging the map of the map of a bag constructor" (* description *)
         "tdouble_flatten_map_coll_fun" (* lemma name *)
         tdouble_flatten_map_coll_fun (* lemma *).

  Definition tdouble_flatten_map_coll_step_correct {model:basic_model}
    := mkOptimizerStepModel tdouble_flatten_map_coll_step tdouble_flatten_map_coll_fun_correctness.

  (* TODO: horribly named *)
  Definition tflatten_over_double_map_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | (NRAEnvUnop OpFlatten
                (NRAEnvMap (NRAEnvMap q₁ (NRAEnvSelect q₂ (NRAEnvUnop OpBag NRAEnvID))) q₃))
        => (NRAEnvMap q₁ (NRAEnvSelect q₂ q₃))
      | _ => p
    end.

  Lemma tflatten_over_double_map_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tflatten_over_double_map_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_over_double_map_arrow.
  Qed.
  Hint Rewrite @tflatten_over_double_map_fun_correctness : optim_correct.

  Definition tflatten_over_double_map_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/map/map/select" (* name *)
         "Simplify flatten of a map over a map of a selection applied to a bag constructor of the input" (* description *)
         "tflatten_over_double_map_fun" (* lemma name *)
         tflatten_over_double_map_fun (* lemma *).

  Definition tflatten_over_double_map_step_correct {model:basic_model}
    := mkOptimizerStepModel tflatten_over_double_map_step tflatten_over_double_map_fun_correctness.

  (* TODO: poorly named *)
  Definition tflatten_over_double_map_with_either_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | (NRAEnvUnop OpFlatten
              (NRAEnvMap
                 (NRAEnvMap q₁
                        (NRAEnvSelect q₂
                                  (NRAEnvApp
                                     (NRAEnvEither (NRAEnvUnop OpBag NRAEnvID) (NRAEnvConst (dcoll []))) q₃)))
                 q₄)) =>
      (NRAEnvMap q₁
             (NRAEnvSelect q₂
                       (NRAEnvUnop OpFlatten
                               (NRAEnvMap
                                  (NRAEnvApp
                                     (NRAEnvEither (NRAEnvUnop OpBag NRAEnvID) (NRAEnvConst (dcoll []))) q₃)
                                  q₄))))
    | _ => p
    end.

  Lemma tflatten_over_double_map_with_either_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tflatten_over_double_map_with_either_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_over_double_map_with_either_arrow.
  Qed.
  Hint Rewrite @tflatten_over_double_map_with_either_fun_correctness : optim_correct.

  Definition tflatten_over_double_map_with_either_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/map/map/select/app/either" (* name *)
         "???" (* description *)
         "tflatten_over_double_map_with_either_fun" (* lemma name *)
         tflatten_over_double_map_with_either_fun (* lemma *).

  Definition tflatten_over_double_map_with_either_step_correct {model:basic_model}
    := mkOptimizerStepModel tflatten_over_double_map_with_either_step tflatten_over_double_map_with_either_fun_correctness.

  (* ignores_env p1 -> (ENV ⊗ p1) ◯ₑ p2 ⇒ₓ p2 ⊗ p1 *)
  Definition tappenv_over_env_merge_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvAppEnv (NRAEnvBinop OpRecMerge NRAEnvEnv p1) p2 =>
        if (nraenv_ignores_env_fun p1)
        then (NRAEnvBinop OpRecMerge p2 p1)
        else p
      | _ => p
    end.
    
  Lemma tappenv_over_env_merge_l_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_over_env_merge_l_fun p.
  Proof.
    destruct p; try solve [unfold tnraenv_rewrites_to; simpl; auto].
    destruct p1; try reflexivity.
    destruct b; try reflexivity.
    destruct p1_1; try reflexivity.
    simpl.
    case_eq (nraenv_ignores_env_fun p1_2); intros; try reflexivity.
    apply tappenv_over_env_merge_l_arrow.
    rewrite <- nraenv_ignores_env_eq in H.
    generalize nraenv_ignores_env_nraenv_core_eq; intros.
    unfold nraenv_to_nraenv_core in *.
    apply H0; assumption.
  Qed.

  Definition tappenv_over_env_merge_l_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/merge-concat/env left" (* name *)
         "Simplify environment application of a merge-concat where the left part is ENV and the right part ignores the environment" (* description *)
         "tappenv_over_env_merge_l_fun" (* lemma name *)
         tappenv_over_env_merge_l_fun (* lemma *).

  Definition tappenv_over_env_merge_l_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_env_merge_l_step tappenv_over_env_merge_l_fun_correctness.

  Definition tmap_full_over_select_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvMap p0 (NRAEnvSelect p1 (NRAEnvUnop OpBag NRAEnvID)) => p
      | NRAEnvMap p0 (NRAEnvSelect p1 (NRAEnvUnop OpBag p2)) =>
        NRAEnvMap (NRAEnvApp p0 p2) (NRAEnvSelect (NRAEnvApp p1 p2) (NRAEnvUnop OpBag NRAEnvID))
      | _ => p
    end.

  Lemma tmap_full_over_select_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tmap_full_over_select_fun p.
  Proof.
    destruct p; simpl; try reflexivity.
    do 3 (match_destr; simpl; try reflexivity).
    destruct p2_2; simpl; try reflexivity;
    apply tmap_full_over_select_arrow.
  Qed.

  Definition tmap_full_over_select_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "map/select/coll" (* name *)
         "???" (* description *)
         "tmap_full_over_select_fun" (* lemma name *)
         tmap_full_over_select_fun (* lemma *).

  Definition tmap_full_over_select_step_correct {model:basic_model}
    := mkOptimizerStepModel tmap_full_over_select_step tmap_full_over_select_fun_correctness.

  Definition tcompose_selects_in_mapenv_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | (NRAEnvAppEnv
           (NRAEnvUnop OpFlatten
                   (NRAEnvMapEnv (NRAEnvMap NRAEnvEnv (NRAEnvSelect p1 (NRAEnvUnop OpBag NRAEnvID)))))
           (NRAEnvMap NRAEnvEnv (NRAEnvSelect p2 (NRAEnvUnop OpBag NRAEnvID)))) =>
        (NRAEnvMap NRAEnvEnv (NRAEnvSelect p1 (NRAEnvSelect p2 (NRAEnvUnop OpBag NRAEnvID))))
      | _ => p
    end.
  
  Lemma tcompose_selects_in_mapenv_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tcompose_selects_in_mapenv_fun p.
  Proof.
    tprove_correctness p.
    apply tcompose_selects_in_mapenv_arrow.
  Qed.

  Definition tcompose_selects_in_mapenv_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/flatten/map-env/map/select/coll/id" (* name *)
         "???" (* description *)
         "tcompose_selects_in_mapenv_fun" (* lemma name *)
         tcompose_selects_in_mapenv_fun (* lemma *).

  Definition tcompose_selects_in_mapenv_step_correct {model:basic_model}
    := mkOptimizerStepModel tcompose_selects_in_mapenv_step tcompose_selects_in_mapenv_fun_correctness.

  Definition tmapenv_to_env_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | (NRAEnvApp (NRAEnvMapEnv NRAEnvEnv) p1) => NRAEnvEnv
      | _ => p
    end.

  Lemma tmapenv_to_env_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmapenv_to_env_fun p.
  Proof.
    tprove_correctness p.
    apply tmapenv_to_env_arrow.
  Qed.

  Definition tmapenv_to_env_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/map-env/env" (* name *)
         "Simplify applications with body that map-environments over the environment" (* description *)
         "tmapenv_to_env_fun" (* lemma name *)
         tmapenv_to_env_fun (* lemma *).

  Definition tmapenv_to_env_step_correct {model:basic_model}
    := mkOptimizerStepModel tmapenv_to_env_step tmapenv_to_env_fun_correctness.

  Definition tenv_appenv_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvAppEnv NRAEnvEnv p1 => p1
      | _ => p
    end.
  
  Lemma tenv_appenv_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tenv_appenv_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_env_l_arrow.
  Qed.

  Definition tenv_appenv_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/env" (* name *)
         "Simplifies environment applications of the environment" (* description *)
         "tenv_appenv_fun" (* lemma name *)
         tenv_appenv_fun (* lemma *).

  Definition tenv_appenv_step_correct {model:basic_model}
    := mkOptimizerStepModel tenv_appenv_step tenv_appenv_fun_correctness.

  Definition tflatten_mapenv_coll_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop OpFlatten (NRAEnvMapEnv (NRAEnvUnop OpBag p1)) =>
        NRAEnvMapEnv p1
      | _ => p
    end.

  Lemma  tflatten_mapenv_coll_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tflatten_mapenv_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_mapenv_coll_arrow.
  Qed.

  Definition tflatten_mapenv_coll_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/map-env/coll" (* name *)
         "Simplify flattening a map environment of a bag constructor" (* description *)
         "tflatten_mapenv_coll_fun" (* lemma name *)
         tflatten_mapenv_coll_fun (* lemma *).

  Definition tflatten_mapenv_coll_step_correct {model:basic_model}
    := mkOptimizerStepModel tflatten_mapenv_coll_step tflatten_mapenv_coll_fun_correctness.

  Definition tflatten_nil_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop OpFlatten (NRAEnvConst (dcoll nil)) =>
        NRAEnvConst (dcoll nil)
      | _ => p
    end.

  Lemma  tflatten_nil_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tflatten_nil_fun p.
  Proof.
    tprove_correctness p.
    apply tenvflatten_nil_arrow.
  Qed.

  Definition tflatten_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/nil" (* name *)
         "Remove flatten over empty records" (* description *)
         "tflatten_nil_fun" (* lemma name *)
         tflatten_nil_fun (* lemma *).

  Definition tflatten_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tflatten_nil_step tflatten_nil_fun_correctness.

  Definition tflatten_through_appenv_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvUnop OpFlatten (NRAEnvAppEnv p1 p2) =>
        NRAEnvAppEnv (NRAEnvUnop OpFlatten p1) p2
      | _ => p
    end.

  Lemma tflatten_through_appenv_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tflatten_through_appenv_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_through_appenv_arrow.
  Qed.

  Definition tflatten_through_appenv_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/app-env" (* name *)
         "Push flatten operations through environment applications" (* description *)
         "tflatten_through_appenv_fun" (* lemma name *)
         tflatten_through_appenv_fun (* lemma *).

  Definition tflatten_through_appenv_step_correct {model:basic_model}
    := mkOptimizerStepModel tflatten_through_appenv_step tflatten_through_appenv_fun_correctness.

  Definition tappenv_flatten_mapenv_to_map_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | (NRAEnvAppEnv (NRAEnvUnop OpFlatten (NRAEnvMapEnv p2))
            (NRAEnvBinop OpRecMerge NRAEnvEnv (NRAEnvUnop (OpRec s) NRAEnvID))) =>
         (NRAEnvUnop OpFlatten
            (NRAEnvMap (NRAEnvAppEnv (NRAEnvApp p2 (NRAEnvUnop (OpDot s) NRAEnvEnv)) NRAEnvID)
                   (NRAEnvBinop OpRecMerge NRAEnvEnv (NRAEnvUnop (OpRec s) NRAEnvID))))
      | _ => p
    end.
  
  Lemma tappenv_flatten_mapenv_to_map_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tappenv_flatten_mapenv_to_map_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_flatten_mapenv_to_map_arrow.
  Qed.

  Definition tappenv_flatten_mapenv_to_map_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/(flatten/map-env)(merge-concat/(env)(rec/id))" (* name *)
         "Simplify environment application of a flattened environment map to a merge-concat of the environment with a record constructor" (* description *)
         "tappenv_flatten_mapenv_to_map_fun" (* lemma name *)
         tappenv_flatten_mapenv_to_map_fun (* lemma *).

  Definition tappenv_flatten_mapenv_to_map_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_flatten_mapenv_to_map_step tappenv_flatten_mapenv_to_map_fun_correctness.


  Definition tselect_over_either_nil_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvSelect p₁ (NRAEnvEither p₂ (NRAEnvConst (dcoll nil))) =>
      NRAEnvEither (NRAEnvSelect p₁ (p₂)) (NRAEnvConst (dcoll nil))
    | _ => p
    end.

  Lemma tselect_over_either_nil_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tselect_over_either_nil_fun p.
  Proof.
    tprove_correctness p.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq. simpl.
    rewrite tselect_over_either.
    rewrite tselect_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tselect_over_either_nil_fun_correctness : toptim_correct.

  Definition tselect_over_either_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "select/either/nil right" (* name *)
         "Push selection through an either whose right side returns an empty bag" (* description *)
         "tselect_over_either_nil_fun" (* lemma name *)
         tselect_over_either_nil_fun (* lemma *).

  Definition tselect_over_either_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tselect_over_either_nil_step tselect_over_either_nil_fun_correctness.

  Definition tselect_over_either_nil_app_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvSelect p₁ (NRAEnvApp (NRAEnvEither p₂ (NRAEnvConst (dcoll nil))) p₄) =>
      NRAEnvApp (NRAEnvEither (NRAEnvSelect p₁ p₂) ((NRAEnvConst (dcoll nil)))) p₄
    | _ => p
    end.

  Lemma tselect_over_either_nil_app_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tselect_over_either_nil_app_fun p.
  Proof.
    tprove_correctness p.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq. simpl.
    rewrite tselect_over_app_either.
    rewrite tselect_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tselect_over_either_nil_app_fun_correctness : toptim_correct.

  Definition tselect_over_either_nil_app_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "select/app/either/nil right" (* name *)
         "Push selection through an application of an either whose right side returns an empty bag" (* description *)
         "tselect_over_either_nil_app_fun" (* lemma name *)
         tselect_over_either_nil_app_fun (* lemma *).

  Definition tselect_over_either_nil_app_step_correct {model:basic_model}
    := mkOptimizerStepModel tselect_over_either_nil_app_step tselect_over_either_nil_app_fun_correctness.

  Definition tmap_over_either_nil_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvMap p₁ (NRAEnvEither p₂ (NRAEnvConst (dcoll nil))) =>
      NRAEnvEither (NRAEnvMap p₁ p₂) ((NRAEnvConst (dcoll nil)))
    | _ => p
    end.

  Lemma tmap_over_either_nil_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmap_over_either_nil_fun p.
  Proof.
    tprove_correctness p.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq. simpl.
    rewrite tmap_over_either.
    rewrite tmap_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tmap_over_either_nil_fun_correctness : toptim_correct.

  Definition tmap_over_either_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "map/either/nil right" (* name *)
         "Push map through an either whose right side returns an empty bag" (* description *)
         "tmap_over_either_nil_fun" (* lemma name *)
         tmap_over_either_nil_fun (* lemma *).

  Definition tmap_over_either_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tmap_over_either_nil_step tmap_over_either_nil_fun_correctness.

  Definition tmap_over_either_nil_app_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvMap p₁ (NRAEnvApp (NRAEnvEither p₂ (NRAEnvConst (dcoll nil))) p₄) =>
      NRAEnvApp (NRAEnvEither (NRAEnvMap p₁ p₂) (NRAEnvConst (dcoll nil))) p₄
    | _ => p
    end.

  Lemma tmap_over_either_nil_app_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmap_over_either_nil_app_fun p.
  Proof.
    tprove_correctness p.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq. simpl.
    rewrite tmap_over_either_app.
    rewrite tmap_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tmap_over_either_nil_app_fun_correctness : toptim_correct.

  Definition tmap_over_either_nil_app_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "map/app/either/nil right" (* name *)
         "Push map through an application of an either whose right side returns an empty bag" (* description *)
         "tmap_over_either_nil_app_fun" (* lemma name *)
         tmap_over_either_nil_app_fun (* lemma *).

  Definition tmap_over_either_nil_app_step_correct {model:basic_model}
    := mkOptimizerStepModel tmap_over_either_nil_app_step tmap_over_either_nil_app_fun_correctness.

  Definition tappenv_over_either_nil_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvAppEnv (NRAEnvEither p₂ (NRAEnvConst (dcoll nil))) p₃ =>
        if nraenv_ignores_id_fun p₃ 
        then NRAEnvEither (NRAEnvAppEnv p₂ p₃) ((NRAEnvConst (dcoll nil)))
        else p
      | _ => p
    end.

  Lemma tappenv_over_either_nil_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_over_either_nil_fun p.
  Proof.
    destruct p; simpl; try reflexivity.
    destruct p1; simpl; try reflexivity.
    destruct p1_2; simpl; try reflexivity.
    destruct d; simpl; try reflexivity.
    destruct l; simpl; try reflexivity.
    match_case; simpl; try reflexivity.
    intros ig.
    rewrite <- nraenv_ignores_id_eq in ig.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq. simpl.
    autorewrite with tnraenv_core_optim.
    - reflexivity.
    - apply nraenv_ignores_id_nraenv_core_eq; assumption.
  Qed.

  Hint Rewrite @tappenv_over_either_nil_fun_correctness : toptim_correct.

    Definition tappenv_over_either_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/either/nil right" (* name *)
         "Pushes environment application through an either with a right branch that builds an empty bag" (* description *)
         "tappenv_over_either_nil_fun" (* lemma name *)
         tappenv_over_either_nil_fun (* lemma *).

  Definition tappenv_over_either_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_either_nil_step tappenv_over_either_nil_fun_correctness.

  Definition tselect_over_flatten_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvSelect p₁ (NRAEnvUnop OpFlatten p₂) =>
      NRAEnvUnop OpFlatten (NRAEnvMap (NRAEnvSelect p₁ NRAEnvID) p₂)
    | _ => p
    end.

  Lemma tselect_over_flatten_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tselect_over_flatten_fun p.
  Proof.
    tprove_correctness p.
    apply tselect_over_flatten.
  Qed.

  Hint Rewrite @tselect_over_flatten_fun_correctness : toptim_correct.

  Definition tselect_over_flatten_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "select/flatten" (* name *)
         "Pushes selection through a flatten operation" (* description *)
         "tselect_over_flatten_fun" (* lemma name *)
         tselect_over_flatten_fun (* lemma *).

  Definition tselect_over_flatten_step_correct {model:basic_model}
    := mkOptimizerStepModel tselect_over_flatten_step tselect_over_flatten_fun_correctness.

  Definition tmap_over_flatten_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvMap p₁ (NRAEnvUnop OpFlatten p₂) =>
      NRAEnvUnop OpFlatten (NRAEnvMap (NRAEnvMap p₁ NRAEnvID) p₂)
    | _ => p
    end.

  Lemma tmap_over_flatten_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmap_over_flatten_fun p.
  Proof.
    tprove_correctness p.
    apply tmap_over_flatten.
  Qed.

  Hint Rewrite @tmap_over_flatten_fun_correctness : toptim_correct.

  Definition tmap_over_flatten_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "map/flatten" (* name *)
         "Pushes map through a flatten operation" (* description *)
         "tmap_over_flatten_fun" (* lemma name *)
         tmap_over_flatten_fun (* lemma *).

  Definition tmap_over_flatten_step_correct {model:basic_model}
    := mkOptimizerStepModel tmap_over_flatten_step tmap_over_flatten_fun_correctness.

  Definition tmap_over_flatten_map_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvMap p₁ (NRAEnvUnop OpFlatten (NRAEnvMap p₂ p₃)) =>
      NRAEnvUnop OpFlatten (NRAEnvMap (NRAEnvMap p₁ p₂) p₃)
      | _ => p
    end.

  Lemma tmap_over_flatten_map_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmap_over_flatten_map_fun p.
  Proof.
    tprove_correctness p.
    apply tmap_over_flatten_map.
  Qed.

  Hint Rewrite @tmap_over_flatten_map_fun_correctness : toptim_correct.

  Definition tmap_over_flatten_map_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "map/flatten/map" (* name *)
         "Pushes map through a flatten of a map" (* description *)
         "tmap_over_flatten_map_fun" (* lemma name *)
         tmap_over_flatten_map_fun (* lemma *).

  Definition tmap_over_flatten_map_step_correct {model:basic_model}
    := mkOptimizerStepModel tmap_over_flatten_map_step tmap_over_flatten_map_fun_correctness.

  Definition tconcat_over_rec_eq_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | (NRAEnvBinop OpRecConcat
                 (NRAEnvUnop (OpRec s₁) p₁) (NRAEnvUnop (OpRec s₂) p₂))
        => if string_dec s₁ s₂ 
           then (NRAEnvUnop (OpRec s₂) p₂)
           else p
      | _ => p
    end.

  Definition tconcat_over_rec_eq_fun_correctness {model:basic_model} p :
    p ⇒ₓ tconcat_over_rec_eq_fun p.
  Proof.
    tprove_correctness p.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq. simpl.
    rewrite tconcat_over_rec_eq.
    reflexivity.
  Qed.
                  
  Hint Rewrite @tconcat_over_rec_eq_fun_correctness : toptim_correct.

  Definition tconcat_over_rec_eq_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "concat/(rec)(rec)" (* name *)
         "Simplifies a concatentation of two record constructors" (* description *)
         "tconcat_over_rec_eq_fun" (* lemma name *)
         tconcat_over_rec_eq_fun (* lemma *).

  Definition tconcat_over_rec_eq_step_correct {model:basic_model}
    := mkOptimizerStepModel tconcat_over_rec_eq_step tconcat_over_rec_eq_fun_correctness.

  Definition tapp_over_const_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        (NRAEnvApp (NRAEnvConst d) p1) => (NRAEnvConst d)
      | _ => p
    end.
  
  Lemma tapp_over_const_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tapp_over_const_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_const_arrow.
  Qed.

  Definition tapp_over_const_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app/const" (* name *)
         "Simplifies application of a constant" (* description *)
         "tapp_over_const_fun" (* lemma name *)
         tapp_over_const_fun (* lemma *).

  Definition tapp_over_const_step_correct {model:basic_model}
    := mkOptimizerStepModel tapp_over_const_step tapp_over_const_fun_correctness.

  Definition tappenv_over_const_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        (NRAEnvAppEnv (NRAEnvConst d) p1) => (NRAEnvConst d)
      | _ => p
    end.
  
  Lemma tappenv_over_const_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tappenv_over_const_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_const_arrow.
  Qed.

  Definition tappenv_over_const_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/const" (* name *)
         "Simplifies environment application of a constant" (* description *)
         "tappenv_over_const_fun" (* lemma name *)
         tappenv_over_const_fun (* lemma *).

  Definition tappenv_over_const_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_const_step tappenv_over_const_fun_correctness.

  Definition tflip_env1_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvAppEnv (NRAEnvMap NRAEnvEnv (NRAEnvSelect q₁ (NRAEnvUnop OpBag NRAEnvID))) q₂ =>
      match q₂ with
      | NRAEnvID => (NRAEnvAppEnv (NRAEnvSelect q₁ (NRAEnvUnop OpBag NRAEnvID)) NRAEnvID)
      | _ =>
        if (nraenv_ignores_env_fun q₁)
        then NRAEnvMap q₂ (NRAEnvSelect q₁ (NRAEnvUnop OpBag NRAEnvID))
        else p
      end
    | _ => p
    end.
  
  Lemma tflip_env1_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tflip_env1_fun p.
  Proof.
    destruct p; try reflexivity.
    destruct p1; try reflexivity.
    destruct p1_1; try reflexivity.
    destruct p1_2; try reflexivity.
    destruct p1_2_2; try reflexivity.
    destruct u; try reflexivity.
    destruct p1_2_2; try reflexivity.
    destruct p2; simpl; try reflexivity;
    try (apply tflip_env1_arrow);
    case_eq (nraenv_ignores_env_fun p1_2_1);
      try reflexivity; intros; rewrite <- nraenv_ignores_env_eq in H;
    apply tflip_env4_arrow;
    generalize nraenv_ignores_env_nraenv_core_eq; intros;
    unfold nraenv_to_nraenv_core in *;
    apply H0; assumption.
  Qed.

  Definition tflip_env1_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "env flip1" (* name *)
         "???" (* description *)
         "tflip_env1_fun" (* lemma name *)
         tflip_env1_fun (* lemma *).

  Definition tflip_env1_step_correct {model:basic_model}
    := mkOptimizerStepModel tflip_env1_step tflip_env1_fun_correctness.

  Definition tflip_env2_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      (NRAEnvAppEnv (NRAEnvSelect p (NRAEnvUnop OpBag NRAEnvID)) NRAEnvID) =>
      (NRAEnvSelect (NRAEnvAppEnv p NRAEnvID) (NRAEnvUnop OpBag NRAEnvID))
    | _ => p
    end.
  
  Lemma tflip_env2_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tflip_env2_fun p.
  Proof.
    tprove_correctness p.
    apply tflip_env2_arrow.
  Qed.

  Definition tflip_env2_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/select/coll/id" (* name *)
         "Pushes environment application through selection of a bag constructor over the input" (* description *)
         "tflip_env2_fun" (* lemma name *)
         tflip_env2_fun (* lemma *).

  Definition tflip_env2_step_correct {model:basic_model}
    := mkOptimizerStepModel tflip_env2_step tflip_env2_fun_correctness.

  Definition tmapenv_over_singleton_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      (NRAEnvAppEnv (NRAEnvMapEnv p1) (NRAEnvUnop OpBag p2)) =>
      (NRAEnvUnop OpBag (NRAEnvAppEnv p1 p2))
    | _ => p
    end.

  Lemma tmapenv_over_singleton_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tmapenv_over_singleton_fun p.
  Proof.
    tprove_correctness p.
    apply tmapenv_over_singleton_arrow.
  Qed.

    Definition tmapenv_over_singleton_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/(map-env)(coll)" (* name *)
         "Simplifies the environment application of a map environment over a bag constructor" (* description *)
         "tmapenv_over_singleton_fun" (* lemma name *)
         tmapenv_over_singleton_fun (* lemma *).

  Definition tmapenv_over_singleton_step_correct {model:basic_model}
    := mkOptimizerStepModel tmapenv_over_singleton_step tmapenv_over_singleton_fun_correctness.
  
  Definition tappenv_over_binop_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        (NRAEnvAppEnv (NRAEnvBinop b p1 p2) p0) =>
         (NRAEnvBinop b (NRAEnvAppEnv p1 p0) (NRAEnvAppEnv p2 p0))
      | _ => p
    end.
  
  Lemma tappenv_over_binop_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tappenv_over_binop_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_over_binop.
  Qed.

  Definition tappenv_over_binop_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/binop" (* name *)
         "Pushes an environment application through a binary operation" (* description *)
         "tappenv_over_binop_fun" (* lemma name *)
         tappenv_over_binop_fun (* lemma *).

  Definition tappenv_over_binop_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_over_binop_step tappenv_over_binop_fun_correctness.

  Definition tflip_env6_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvMap (NRAEnvBinop OpRecMerge NRAEnvEnv NRAEnvID)
                (NRAEnvSelect p1 (NRAEnvBinop OpRecMerge NRAEnvEnv p2)) =>
      NRAEnvMap (NRAEnvUnop OpBag NRAEnvID)
                (NRAEnvSelect p1 (NRAEnvBinop OpRecMerge NRAEnvEnv p2))
    | _ => p
    end.
  
  Lemma tflip_env6_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tflip_env6_fun p.
  Proof.
    tprove_correctness p.
    apply tflip_env6_arrow.
  Qed.

  Definition tflip_env6_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "env flip6" (* name *)
         "???" (* description *)
         "tflip_env6_fun" (* lemma name *)
         tflip_env6_fun (* lemma *).

  Definition tflip_env6_step_correct {model:basic_model}
    := mkOptimizerStepModel tflip_env6_step tflip_env6_fun_correctness.

  (* TODO: horribly named *)
  Definition tmapenv_to_map_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | (NRAEnvAppEnv (NRAEnvMapEnv p1) p2) =>
        if (nraenv_ignores_id_fun p1)
        then (NRAEnvMap (NRAEnvAppEnv p1 NRAEnvID) p2)
        else p
      | _ => p
    end.

  Lemma tmapenv_to_map_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tmapenv_to_map_fun p.
  Proof.
    destruct p; try reflexivity.
    destruct p1; try reflexivity.
    simpl.
    case_eq (nraenv_ignores_id_fun p1); try reflexivity; intros.
    apply tmapenv_to_map_arrow.
    rewrite <- nraenv_ignores_id_eq in H.
    generalize nraenv_ignores_id_nraenv_core_eq; intros.
    unfold nraenv_to_nraenv_core in *.
    apply H0; assumption.
  Qed.

  Definition tmapenv_to_map_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/map-env" (* name *)
         "Push environment application through map environment" (* description *)
         "tmapenv_to_map_fun" (* lemma name *)
         tmapenv_to_map_fun (* lemma *).

  Definition tmapenv_to_map_step_correct {model:basic_model}
    := mkOptimizerStepModel tmapenv_to_map_step tmapenv_to_map_fun_correctness.

  Definition tmerge_concat_to_concat_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvBinop OpRecMerge (NRAEnvUnop (OpRec s1) p1) (NRAEnvUnop (OpRec s2) p2) =>
      if (s1 == s2)
      then p
      else NRAEnvUnop OpBag
                      (NRAEnvBinop OpRecConcat
                                   (NRAEnvUnop (OpRec s1) p1)
                                   (NRAEnvUnop (OpRec s2) p2))
    | _ => p
    end.

  Lemma tmerge_concat_to_concat_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tmerge_concat_to_concat_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_concat_to_concat_arrow.
    trivial.
  Qed.

  Definition tmerge_concat_to_concat_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "merge-concat/(rec)(rec)" (* name *)
         "Simplifies a merge-concat of two record constructors into a simpler concatentation" (* description *)
         "tmerge_concat_to_concat_fun" (* lemma name *)
         tmerge_concat_to_concat_fun (* lemma *).

  Definition tmerge_concat_to_concat_step_correct {model:basic_model}
    := mkOptimizerStepModel tmerge_concat_to_concat_step tmerge_concat_to_concat_fun_correctness.

  Definition tmerge_with_concat_to_concat_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvBinop OpRecMerge (NRAEnvUnop (OpRec s1) p1)
                  (NRAEnvBinop OpRecConcat (NRAEnvUnop (OpRec s1') p1')
                               (NRAEnvUnop (OpRec s2) p2)) =>
        if (s1 == s2)
        then p
        else
          if (s1 == s1')
          then
            if (p1 == p1')
            then NRAEnvUnop OpBag (NRAEnvBinop OpRecConcat
                                               (NRAEnvUnop (OpRec s1) p1)
                                               (NRAEnvUnop (OpRec s2) p2))
            else p
          else p
      | _ => p
    end.
  
  Lemma tmerge_with_concat_to_concat_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tmerge_with_concat_to_concat_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_with_concat_to_concat_arrow.
    trivial.
  Qed.

  Definition tmerge_with_concat_to_concat_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "merge-concat/(rec)(concat(rec)(rec))" (* name *)
         "Simplifies a merge concatenation of a record constructor and a concatenation of record constructors into a simpler concatenation" (* description *)
         "tmerge_with_concat_to_concat_fun" (* lemma name *)
         tmerge_with_concat_to_concat_fun (* lemma *).

  Definition tmerge_with_concat_to_concat_step_correct {model:basic_model}
    := mkOptimizerStepModel tmerge_with_concat_to_concat_step tmerge_with_concat_to_concat_fun_correctness.

  Definition tdot_over_rec_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop (OpDot s2)
                 (NRAEnvUnop (OpRec s1) p1) =>
      if (s1 == s2) then p1
      else p
    | _ => p
    end.

  Lemma tdot_over_rec_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tdot_over_rec_fun p.
  Proof.
    tprove_correctness p.
    apply tdot_over_rec_arrow.
  Qed.

  Definition tdot_over_rec_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "dot/rec" (* name *)
         "Simplifies field lookup of a record construction" (* description *)
         "tdot_over_rec_fun" (* lemma name *)
         tdot_over_rec_fun (* lemma *).

  Definition tdot_over_rec_step_correct {model:basic_model}
    := mkOptimizerStepModel tdot_over_rec_step tdot_over_rec_fun_correctness.

  Definition tnested_map_over_singletons_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop OpFlatten
                 (NRAEnvMap (NRAEnvSelect q₁ (NRAEnvUnop OpBag q₂)) q₃) =>
      NRAEnvSelect q₁ (NRAEnvMap q₂ q₃)
    | _ => p
    end.

  Lemma tnested_map_over_singletons_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tnested_map_over_singletons_fun p.
  Proof.
    tprove_correctness p.
    apply tnested_map_over_singletons_arrow.
  Qed.

  Definition tnested_map_over_singletons_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/map/select/coll" (* name *)
         "Simplifies a flatten of a map of a select over a bag constructor" (* description *)
         "tnested_map_over_singletons_fun" (* lemma name *)
         tnested_map_over_singletons_fun (* lemma *).

  Definition tnested_map_over_singletons_step_correct {model:basic_model}
    := mkOptimizerStepModel tnested_map_over_singletons_step tnested_map_over_singletons_fun_correctness.

  Definition tappenv_mapenv_to_map_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvAppEnv (NRAEnvMapEnv q)
                   (NRAEnvBinop OpRecMerge NRAEnvEnv (NRAEnvUnop (OpRec a) NRAEnvID)) =>
      NRAEnvMap (NRAEnvAppEnv (NRAEnvApp q (NRAEnvUnop (OpDot a) NRAEnvEnv)) NRAEnvID)
                (NRAEnvBinop OpRecMerge NRAEnvEnv (NRAEnvUnop (OpRec a) NRAEnvID))
    | _ => p
    end.

  Lemma tappenv_mapenv_to_map_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_mapenv_to_map_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_mapenv_to_map_arrow.
  Qed.

  Definition tappenv_mapenv_to_map_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "app-env/(map-env)(merge-concat(env)(rec/id))" (* name *)
         "???" (* description *)
         "tappenv_mapenv_to_map_fun" (* lemma name *)
         tappenv_mapenv_to_map_fun (* lemma *).

  Definition tappenv_mapenv_to_map_step_correct {model:basic_model}
    := mkOptimizerStepModel tappenv_mapenv_to_map_step tappenv_mapenv_to_map_fun_correctness.

  (* optimizations for rproject *)

   Definition trproject_nil_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (OpRecProject nil) p₁
        => NRAEnvConst (drec nil)
      | _ => p
    end.

  Definition trproject_nil_fun_correctness {model:basic_model} p :
    p ⇒ₓ trproject_nil_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_nil.
  Qed.

  Hint Rewrite @trproject_nil_fun_correctness : toptim_correct.

  Definition trproject_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "rproject/nil" (* name *)
         "Remove record projection of an empty record" (* description *)
         "trproject_nil_fun" (* lemma name *)
         trproject_nil_fun (* lemma *).

  Definition trproject_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel trproject_nil_step trproject_nil_fun_correctness.

  Definition trproject_over_const_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (OpRecProject sl)
          (NRAEnvConst (drec l))
        => NRAEnvConst (drec (rproject l sl))
      | _ => p
    end.

  Definition trproject_over_const_fun_correctness {model:basic_model} p :
    p ⇒ₓ trproject_over_const_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_over_const.
  Qed.

  Hint Rewrite @trproject_over_const_fun_correctness : toptim_correct.

  Definition trproject_over_const_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "rproject/const" (* name *)
         "Simplify record projection of a constant record" (* description *)
         "trproject_over_const_fun" (* lemma name *)
         trproject_over_const_fun (* lemma *).

  Definition trproject_over_const_step_correct {model:basic_model}
    := mkOptimizerStepModel trproject_over_const_step trproject_over_const_fun_correctness.

  Definition trproject_over_rec_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (OpRecProject sl)
          (NRAEnvUnop (OpRec s) p₁)
        => if in_dec string_dec s sl
           then NRAEnvUnop (OpRec s) p₁
           else NRAEnvConst (drec nil)
      | _ => p
    end.

  Definition trproject_over_rec_fun_correctness {model:basic_model} p :
    p ⇒ₓ trproject_over_rec_fun p.
  Proof.
    tprove_correctness p.
    - apply trproject_over_rec_in; trivial.
    - apply trproject_over_rec_nin; trivial. 
  Qed.

  Hint Rewrite @trproject_over_rec_fun_correctness : toptim_correct.

  Definition trproject_over_rec_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "rproject/rec" (* name *)
         "Simplify record projection of a record construction" (* description *)
         "trproject_over_rec_fun" (* lemma name *)
         trproject_over_rec_fun (* lemma *).

  Definition trproject_over_rec_step_correct {model:basic_model}
    := mkOptimizerStepModel trproject_over_rec_step trproject_over_rec_fun_correctness.

  Definition trproject_over_concat_r_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (OpRecProject sl)
               (NRAEnvBinop OpRecConcat
                        p₁ (NRAEnvUnop (OpRec s) p₂))
        => if in_dec string_dec s sl
           then NRAEnvBinop OpRecConcat
                        (NRAEnvUnop (OpRecProject (remove string_dec s sl)) p₁)
                        (NRAEnvUnop (OpRec s) p₂)
           else (NRAEnvUnop (OpRecProject sl) p₁)
      | _ => p
    end.

  Definition trproject_over_concat_r_fun_correctness {model:basic_model} p :
    p ⇒ₓ trproject_over_concat_r_fun p.
  Proof.
    tprove_correctness p.
    - apply trproject_over_concat_rec_r_in; trivial.
    - apply trproject_over_concat_rec_r_nin; trivial.
  Qed.

  Hint Rewrite @trproject_over_concat_r_fun_correctness : toptim_correct.

  Definition trproject_over_concat_r_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "rproject/concat/rec right" (* name *)
         "Simplify record projection of a concatenation with a record constructor" (* description *)
         "trproject_over_concat_r_fun" (* lemma name *)
         trproject_over_concat_r_fun (* lemma *).

  Definition trproject_over_concat_r_step_correct {model:basic_model}
    := mkOptimizerStepModel trproject_over_concat_r_step trproject_over_concat_r_fun_correctness.

  Definition trproject_over_concat_l_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (OpRecProject sl)
               (NRAEnvBinop OpRecConcat
                        (NRAEnvUnop (OpRec s) p₁) p₂)
        => if in_dec string_dec s sl
                     (* this case would need shape/type inference to handle, since we don't know if s is in p₂ *)

           then p
           else (NRAEnvUnop (OpRecProject sl) p₂)
      | _ => p
    end.

  Definition trproject_over_concat_l_fun_correctness {model:basic_model} p :
    p ⇒ₓ trproject_over_concat_l_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_over_concat_rec_l_nin; trivial.
  Qed.

  Hint Rewrite @trproject_over_concat_l_fun_correctness : toptim_correct.

  Definition trproject_over_concat_l_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "rproject/concat/rec left" (* name *)
         "Simplify record projection of a concatenation with a record constructor" (* description *)
         "trproject_over_concat_l_fun" (* lemma name *)
         trproject_over_concat_l_fun (* lemma *).

  Definition trproject_over_concat_l_step_correct {model:basic_model}
    := mkOptimizerStepModel trproject_over_concat_l_step trproject_over_concat_l_fun_correctness.

  Definition trproject_over_rproject_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (OpRecProject sl1)
          (NRAEnvUnop (OpRecProject sl2) p1)
        => NRAEnvUnop (OpRecProject (set_inter string_dec sl2 sl1)) p1
      | _ => p
    end.

  Definition trproject_over_rproject_fun_correctness {model:basic_model} p :
    p ⇒ₓ trproject_over_rproject_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_over_rproject.
  Qed.

  Hint Rewrite @trproject_over_rproject_fun_correctness : toptim_correct.

  Definition trproject_over_rproject_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "rproject/rproject" (* name *)
         "Fuse nested record projections" (* description *)
         "trproject_over_rproject_fun" (* lemma name *)
         trproject_over_rproject_fun (* lemma *).

  Definition trproject_over_rproject_step_correct {model:basic_model}
    := mkOptimizerStepModel trproject_over_rproject_step trproject_over_rproject_fun_correctness.

  Definition trproject_over_either_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (OpRecProject sl)
          (NRAEnvEither p₁ p₂)
        => NRAEnvEither (NRAEnvUnop (OpRecProject sl) p₁) (NRAEnvUnop (OpRecProject sl) p₂)
      | _ => p
    end.

  Definition trproject_over_either_fun_correctness {model:basic_model} p :
    p ⇒ₓ trproject_over_either_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_over_either.
  Qed.

  Hint Rewrite @trproject_over_either_fun_correctness : toptim_correct.

  Definition trproject_over_either_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "rproject/either" (* name *)
         "Push record projection through an either" (* description *)
         "trproject_over_either_fun" (* lemma name *)
         trproject_over_either_fun (* lemma *).

  Definition trproject_over_either_step_correct {model:basic_model}
    := mkOptimizerStepModel trproject_over_either_step trproject_over_either_fun_correctness.

  Definition tcount_over_map_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop OpCount (NRAEnvMap p₁ p₂) => NRAEnvUnop OpCount p₂
      | _ => p
    end.

  Definition tcount_over_map_fun_correctness {model:basic_model} p :
    p ⇒ₓ tcount_over_map_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_map.
  Qed.

  Hint Rewrite @tcount_over_map_fun_correctness : toptim_correct.

  Definition tcount_over_map_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "count/map" (* name *)
         "Simplify count of a map (by removing the map)" (* description *)
         "tcount_over_map_fun" (* lemma name *)
         tcount_over_map_fun (* lemma *).

  Definition tcount_over_map_step_correct {model:basic_model}
    := mkOptimizerStepModel tcount_over_map_step tcount_over_map_fun_correctness.

  Definition tcount_over_flat_map_map_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop OpCount
                 (NRAEnvUnop OpFlatten
                             (NRAEnvMap (NRAEnvMap p₁ p₂) p₃)) =>
      NRAEnvUnop OpCount (NRAEnvUnop OpFlatten (NRAEnvMap p₂ p₃))
    | _ => p
    end.

  Definition tcount_over_flat_map_map_fun_correctness {model:basic_model} p :
    p ⇒ₓ tcount_over_flat_map_map_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_flat_map_map.
  Qed.

  Hint Rewrite @tcount_over_flat_map_map_fun_correctness : toptim_correct.

  Definition tcount_over_flat_map_map_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "count/flatten/map/map" (* name *)
         "Simplify the count of a flatten of a map'ed map" (* description *)
         "tcount_over_flat_map_map_fun" (* lemma name *)
         tcount_over_flat_map_map_fun (* lemma *).

  Definition tcount_over_flat_map_map_step_correct {model:basic_model}
    := mkOptimizerStepModel tcount_over_flat_map_map_step tcount_over_flat_map_map_fun_correctness.


  Definition tcount_over_flat_map_either_nil_map_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop OpCount
                 (NRAEnvUnop OpFlatten
                             (NRAEnvMap (NRAEnvEither (NRAEnvMap p₁ p₂)
                                                      (NRAEnvConst (dcoll nil)))
                                        p₃)) =>
      NRAEnvUnop OpCount
                 (NRAEnvUnop OpFlatten
                             (NRAEnvMap (NRAEnvEither p₂
                                                      (NRAEnvConst (dcoll nil))) p₃))
    | _ => p
    end.

  Definition tcount_over_flat_map_either_nil_map_fun_correctness {model:basic_model} p :
    p ⇒ₓ tcount_over_flat_map_either_nil_map_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_flat_map_either_nil_map.
  Qed.

  Hint Rewrite @tcount_over_flat_map_either_nil_map_fun_correctness : toptim_correct.

  Definition tcount_over_flat_map_either_nil_map_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "count/flatten/map/either(map)(nil)" (* name *)
         "Simplify count of a flatten of a map over an either where the right part builds an empty bag" (* description *)
         "tcount_over_flat_map_either_nil_map_fun" (* lemma name *)
         tcount_over_flat_map_either_nil_map_fun (* lemma *).

  Definition tcount_over_flat_map_either_nil_map_step_correct {model:basic_model}
    := mkOptimizerStepModel tcount_over_flat_map_either_nil_map_step tcount_over_flat_map_either_nil_map_fun_correctness.

  Definition tcount_over_flat_map_either_nil_app_map_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop OpCount
                 (NRAEnvUnop OpFlatten
                             (NRAEnvMap (NRAEnvApp (NRAEnvEither (NRAEnvMap p₁ p₂)
                                                                 (NRAEnvConst (dcoll nil))) p₄)
                                        p₃)) =>
      NRAEnvUnop OpCount
                 (NRAEnvUnop OpFlatten
                             (NRAEnvMap (NRAEnvApp
                                           (NRAEnvEither p₂ (NRAEnvConst (dcoll nil)))
                                           p₄)
                                        p₃))
      | _ => p
    end.

  Definition tcount_over_flat_map_either_nil_app_map_fun_correctness {model:basic_model} p :
    p ⇒ₓ tcount_over_flat_map_either_nil_app_map_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_flat_map_either_nil_app_map.
  Qed.

  Hint Rewrite @tcount_over_flat_map_either_nil_app_map_fun_correctness : toptim_correct.

  Definition tcount_over_flat_map_either_nil_app_map_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "count/flatten/map/app/either(map)(nil)" (* name *)
         "Simplify count of a flatten of a map over an application of an either where the right part builds an empty bag" (* description *)
         "tcount_over_flat_map_either_nil_app_map_fun" (* lemma name *)
         tcount_over_flat_map_either_nil_app_map_fun (* lemma *).

  Definition tcount_over_flat_map_either_nil_app_map_step_correct {model:basic_model}
    := mkOptimizerStepModel tcount_over_flat_map_either_nil_app_map_step tcount_over_flat_map_either_nil_app_map_fun_correctness.

  Definition tcount_over_flat_map_either_nil_app_singleton_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop OpCount
                 (NRAEnvUnop OpFlatten
                             (NRAEnvMap (NRAEnvApp (NRAEnvEither (NRAEnvUnop OpBag p₁)
                                                                 (NRAEnvConst (dcoll nil))) p₃) p₂)) =>
      NRAEnvUnop OpCount
                 (NRAEnvUnop OpFlatten
                             (NRAEnvMap (NRAEnvApp (NRAEnvEither (NRAEnvUnop OpBag (NRAEnvConst dunit))
                                                                 (NRAEnvConst (dcoll nil))) p₃) p₂))
    | _ => p
    end.

  Definition tcount_over_flat_map_either_nil_app_singleton_fun_correctness {model:basic_model} p :
    p ⇒ₓ tcount_over_flat_map_either_nil_app_singleton_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_flat_map_either_nil_app_singleton.
  Qed.

  Hint Rewrite @tcount_over_flat_map_either_nil_app_singleton_fun_correctness : toptim_correct.

  Definition tcount_over_flat_map_either_nil_app_singleton_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "count/flatten/map/app/either(coll)(nil)" (* name *)
         "Simplify count of a flatten of a map over an application of an either where the left side builds a bag and the right part builds an empty bag" (* description *)
         "tcount_over_flat_map_either_nil_app_singleton_fun" (* lemma name *)
         tcount_over_flat_map_either_nil_app_singleton_fun (* lemma *).

  Definition tcount_over_flat_map_either_nil_app_singleton_step_correct {model:basic_model}
    := mkOptimizerStepModel tcount_over_flat_map_either_nil_app_singleton_step tcount_over_flat_map_either_nil_app_singleton_fun_correctness.

  (* optimizations for mapconcat *)

  (* ⋈ᵈ⟨ p₁ ⟩(‵{| ‵[||] |}) ⇒ₓ p₁ ◯ (‵[||]) *)
  Definition tmapconcat_over_singleton_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      |  NRAEnvMapProduct p (NRAEnvUnop OpBag (NRAEnvConst (drec []))) =>
         NRAEnvApp p (NRAEnvConst (drec []))
      | _ => p
    end.

  Lemma tmapconcat_over_singleton_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmapconcat_over_singleton_fun p.
  Proof.
    tprove_correctness p.
    apply tmapconcat_over_singleton.
  Qed.
  Hint Rewrite @tmerge_empty_record_r_fun_correctness : optim_correct.

  Definition tmapconcat_over_singleton_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "map-concat/coll right/nil" (* name *)
         "Simplufy map concat with a bag with an empty record" (* description *)
         "tmapconcat_over_singleton_fun" (* lemma name *)
         tmapconcat_over_singleton_fun (* lemma *).

  Definition tmapconcat_over_singleton_step_correct {model:basic_model}
    := mkOptimizerStepModel tmapconcat_over_singleton_step tmapconcat_over_singleton_fun_correctness.

  Definition tdup_elim_fun {fruntime:foreign_runtime} (p:nraenv) :=
    dup_elim_fun p.

  Lemma tdup_elim_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tdup_elim_fun p.
  Proof.
    destruct p; simpl; try reflexivity.
    destruct u; simpl; try reflexivity.
    match_case; try reflexivity; intros nd.
    apply tdup_elim.
    apply nodupA_checker_correct.
    trivial.
  Qed.

  Hint Rewrite @tdup_elim_fun_correctness : optim_correct.

  Definition tdup_elim_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "distinct/nodup" (* name *)
         "Removes applications of the distinct operator to bags statically known to already be duplicate free" (* description *)
         "tdup_elim_fun" (* lemma name *)
         tdup_elim_fun (* lemma *).

  Definition tdup_elim_step_correct {model:basic_model}
    := mkOptimizerStepModel tdup_elim_step tdup_elim_fun_correctness.
  
  (* *************************** *)
  Local Open Scope string.

  (* list of all optimizations *)
  Definition tnraenv_optim_list {fruntime:foreign_runtime} : list (@OptimizerStep nraenv)
    := [
        tand_comm_step
        ; tselect_and_comm_step
        ; tselect_and_step
        ; select_union_distr_step
        ; tdot_from_duplicate_r_step
        ; tdot_from_duplicate_l_step
        ; tflatten_coll_step
        ; tconcat_empty_record_r_step
        ; tconcat_empty_record_l_step
        ; tdot_over_concat_r_step
        ; tdot_over_concat_l_step
        ; tmerge_empty_record_r_step
        ; tmerge_empty_record_l_step
        ; tmap_into_id_step
        ; tflatten_map_coll_step
        ; tflatten_flatten_map_either_nil_step
        ; tmap_map_compose_step
        ; tmap_singleton_step
        ; tapp_over_id_r_step
        ; tapp_over_env_step
        ; tapp_over_id_l_step
        ; tapp_over_ignoreid_step
        ; tappenv_over_env_l_step
        ; tappenv_over_env_r_step
        ; tappenv_over_ignoreenv_step
        ; tapp_over_app_step
        ; tappenv_over_appenv_step
        ; tappenv_over_app_step
        ; tapp_over_appenv_step
        ; tapp_over_unop_step
        ; tappenv_over_unop_step
        ; tunop_over_either_const_step
        ; tunop_over_either_const_app_step
        ; tapp_over_map_step
        ; tapp_over_mapconcat_step
        ; tapp_over_product_step
        ; tappenv_over_map_step
        ; tappenv_over_select_step
        ; tapp_over_select_step
        ; tapp_over_binop_step
        ; tproduct_singletons_step
        ; tproduct_empty_right_step
        ; tproduct_empty_left_step
        ; tdouble_flatten_map_coll_step
        ; tflatten_over_double_map_step
        ; tflatten_over_double_map_with_either_step
        ; tappenv_over_env_merge_l_step
        ; tmap_full_over_select_step
        ; tcompose_selects_in_mapenv_step
        ; tmapenv_to_env_step
        ; tenv_appenv_step
        ; tflatten_mapenv_coll_step
        ; tflatten_nil_step
        ; tflatten_through_appenv_step
        ; tappenv_flatten_mapenv_to_map_step
        ; tselect_over_either_nil_step
        ; tselect_over_either_nil_app_step
        ; tmap_over_either_nil_step
        ; tmap_over_either_nil_app_step
        ; tappenv_over_either_nil_step
        ; tselect_over_flatten_step
        ; tmap_over_flatten_step
        ; tmap_over_flatten_map_step
        ; tconcat_over_rec_eq_step
        ; tapp_over_const_step
        ; tappenv_over_const_step
        ; tflip_env1_step
        ; tflip_env2_step
        ; tmapenv_over_singleton_step
        ; tappenv_over_binop_step
        ; tflip_env6_step
        ; tmapenv_to_map_step
        ; tmerge_concat_to_concat_step
        ; tmerge_with_concat_to_concat_step
        ; tdot_over_rec_step
        ; tnested_map_over_singletons_step
        ; tappenv_mapenv_to_map_step
        ; trproject_nil_step
        ; trproject_over_const_step
        ; trproject_over_rec_step
        ; trproject_over_concat_r_step
        ; trproject_over_concat_l_step
        ; trproject_over_rproject_step
        ; trproject_over_either_step
        ; tcount_over_map_step
        ; tcount_over_flat_map_map_step
        ; tcount_over_flat_map_either_nil_map_step
        ; tcount_over_flat_map_either_nil_app_map_step
        ; tcount_over_flat_map_either_nil_app_singleton_step
        ; tmapconcat_over_singleton_step
        ; tdup_elim_step
      ].

  Definition tnraenv_optim_model_list {model:basic_model} : list (OptimizerStepModel tnraenv_rewrites_to)
    := [
        tand_comm_step_correct
        ; tselect_and_comm_step_correct
        ; tselect_and_step_correct
        ; select_union_distr_step_correct
        ; tdot_from_duplicate_r_step_correct
        ; tdot_from_duplicate_l_step_correct
        ; tflatten_coll_step_correct
        ; tconcat_empty_record_r_step_correct
        ; tconcat_empty_record_l_step_correct
        ; tdot_over_concat_r_step_correct
        ; tdot_over_concat_l_step_correct
        ; tmerge_empty_record_r_step_correct
        ; tmerge_empty_lecord_l_step_correct
        ; tmap_into_id_step_correct
        ; tflatten_map_coll_step_correct
        ; tflatten_flatten_map_either_nil_step_correct
        ; tmap_map_compose_step_correct
        ; tmap_singleton_step_correct
        ; tapp_over_id_r_step_correct
        ; tapp_over_env_step_correct
        ; tapp_over_id_l_step_correct
        ; tapp_over_ignoreid_step_correct
        ; tappenv_over_env_l_step_correct
        ; tappenv_over_env_r_step_correct
        ; tappenv_over_ignoreenv_step_correct
        ; tapp_over_app_step_correct
        ; tappenv_over_appenv_step_correct
        ; tappenv_over_app_step_correct
        ; tapp_over_appenv_step_correct
        ; tapp_over_unop_step_correct
        ; tappenv_over_unop_step_correct
        ; tunop_over_either_const_step_correct
        ; tunop_over_either_const_app_step_correct
        ; tapp_over_map_step_correct
        ; tapp_over_mapconcat_step_correct
        ; tapp_over_product_step_correct
        ; tappenv_over_map_step_correct
        ; tappenv_over_select_step_correct
        ; tapp_over_select_step_correct
        ; tapp_over_binop_step_correct
        ; tproduct_singletons_step_correct
        ; tproduct_empty_right_step_correct
        ; tproduct_empty_left_step_correct
        ; tdouble_flatten_map_coll_step_correct
        ; tflatten_over_double_map_step_correct
        ; tflatten_over_double_map_with_either_step_correct
        ; tappenv_over_env_merge_l_step_correct
        ; tmap_full_over_select_step_correct
        ; tcompose_selects_in_mapenv_step_correct
        ; tmapenv_to_env_step_correct
        ; tenv_appenv_step_correct
        ; tflatten_mapenv_coll_step_correct
        ; tflatten_nil_step_correct
        ; tflatten_through_appenv_step_correct
        ; tappenv_flatten_mapenv_to_map_step_correct
        ; tselect_over_either_nil_step_correct
        ; tselect_over_either_nil_app_step_correct
        ; tmap_over_either_nil_step_correct
        ; tmap_over_either_nil_app_step_correct
        ; tappenv_over_either_nil_step_correct
        ; tselect_over_flatten_step_correct
        ; tmap_over_flatten_step_correct
        ; tmap_over_flatten_map_step_correct
        ; tconcat_over_rec_eq_step_correct
        ; tapp_over_const_step_correct
        ; tappenv_over_const_step_correct
        ; tflip_env1_step_correct
        ; tflip_env2_step_correct
        ; tmapenv_over_singleton_step_correct
        ; tappenv_over_binop_step_correct
        ; tflip_env6_step_correct
        ; tmapenv_to_map_step_correct
        ; tmerge_concat_to_concat_step_correct
        ; tmerge_with_concat_to_concat_step_correct
        ; tdot_over_rec_step_correct
        ; tnested_map_over_singletons_step_correct
        ; tappenv_mapenv_to_map_step_correct
        ; trproject_nil_step_correct
        ; trproject_over_const_step_correct
        ; trproject_over_rec_step_correct
        ; trproject_over_concat_r_step_correct
        ; trproject_over_concat_l_step_correct
        ; trproject_over_rproject_step_correct
        ; trproject_over_either_step_correct
        ; tcount_over_map_step_correct
        ; tcount_over_flat_map_map_step_correct
        ; tcount_over_flat_map_either_nil_map_step_correct
        ; tcount_over_flat_map_either_nil_app_map_step_correct
        ; tcount_over_flat_map_either_nil_app_singleton_step_correct
        ; tmapconcat_over_singleton_step_correct
        ; tdup_elim_step_correct
      ].

  Lemma tnraenv_optim_model_list_complete {model:basic_model}
    : optim_model_list_complete tnraenv_optim_list tnraenv_optim_model_list.
  Proof.
    optim_correct_list_complete_prover.
  Qed.

  Definition tnraenv_optim_list_correct {model:basic_model}
    : optim_list_correct tnraenv_rewrites_to tnraenv_optim_list
    := optim_list_correct_from_model tnraenv_optim_model_list_complete.

  Lemma tnraenv_optim_list_distinct {fruntime:foreign_runtime}:
    optim_list_distinct tnraenv_optim_list.
  Proof.
    apply optim_list_distinct_prover.
    vm_compute.
    apply eq_refl.
  Qed.

  Definition run_nraenv_optims 
             {fruntime:foreign_runtime}
             {logger:optimizer_logger string nraenv}
             (opc:optim_phases_config)
    : nraenv -> nraenv :=
    run_phases tnraenv_map_deep nraenv_size tnraenv_optim_list opc.

  Lemma run_nraenv_optims_correctness
        {model:basic_model} {logger:optimizer_logger string nraenv}
        (opc:optim_phases_config)
        (p:nraenv) :
    tnraenv_rewrites_to p ( run_nraenv_optims opc p).
  Proof.
    unfold run_nraenv_optims.
    apply run_phases_correctness.
    - intros. apply nraenv_map_deep_correctness; auto.
    - apply tnraenv_optim_list_correct.
  Qed.

  Section default.
  
  Definition nraenv_default_head_optim_list {fruntime:foreign_runtime} : list string :=
    [
      optim_step_name tapp_over_app_step
      ; optim_step_name tappenv_over_appenv_step
      ; optim_step_name tappenv_over_app_step
      ; optim_step_name tapp_over_appenv_step
      ; optim_step_name tmap_into_id_step
      ; optim_step_name tproduct_singletons_step
      ; optim_step_name tproduct_empty_right_step
      ; optim_step_name tproduct_empty_left_step
      ; optim_step_name tmap_singleton_step
      ; optim_step_name tmap_map_compose_step
      ; optim_step_name tflatten_coll_step
      (* only in tail *)
      (* ; optim_step_name tdouble_flatten_map_coll_step *)
      ; optim_step_name tflatten_map_coll_step
      ; optim_step_name tapp_over_id_r_step
      ; optim_step_name tapp_over_id_l_step
      ; optim_step_name tapp_over_unop_step
      ; optim_step_name tapp_over_binop_step
      ; optim_step_name tapp_over_select_step
      ; optim_step_name tapp_over_map_step
      ; optim_step_name tapp_over_mapconcat_step
      ; optim_step_name tapp_over_product_step
      ; optim_step_name tappenv_over_unop_step
      ; optim_step_name tcompose_selects_in_mapenv_step
      ; optim_step_name tmap_full_over_select_step
      ; optim_step_name tmerge_empty_record_r_step
      ; optim_step_name tselect_and_step
      ; optim_step_name select_union_distr_step
      ; optim_step_name tdot_from_duplicate_r_step
      ; optim_step_name tdot_from_duplicate_l_step
      ; optim_step_name tconcat_empty_record_r_step
      ; optim_step_name tconcat_empty_record_l_step
      ; optim_step_name tdot_over_concat_r_step
      ; optim_step_name tdot_over_concat_l_step
      ; optim_step_name tmerge_empty_record_r_step
      ; optim_step_name tmerge_empty_record_l_step
      ; optim_step_name tmapenv_to_env_step
      ; optim_step_name tenv_appenv_step
      ; optim_step_name tflatten_mapenv_coll_step
      ; optim_step_name tflatten_nil_step
      (*optim_step_name  only in head *)
      ; optim_step_name tflatten_through_appenv_step
      (*optim_step_name  only in head *)
      ; optim_step_name tappenv_flatten_mapenv_to_map_step
      ; optim_step_name tapp_over_const_step
      ; optim_step_name tappenv_over_const_step
      ; optim_step_name tflip_env1_step
      ; optim_step_name tflip_env2_step
      ; optim_step_name tmapenv_over_singleton_step
      ; optim_step_name tappenv_over_binop_step
      ; optim_step_name tflip_env6_step
      ; optim_step_name tmapenv_to_map_step
      ; optim_step_name tappenv_over_map_step
      ; optim_step_name tapp_over_ignoreid_step
      ; optim_step_name tappenv_over_ignoreenv_step
      ; optim_step_name tappenv_over_env_r_step
      ; optim_step_name tappenv_over_env_l_step
      ; optim_step_name tappenv_over_env_merge_l_step
      ; optim_step_name tappenv_over_select_step
      ; optim_step_name tmerge_concat_to_concat_step
      ; optim_step_name tmerge_with_concat_to_concat_step
      ; optim_step_name tdot_over_rec_step
      ; optim_step_name tnested_map_over_singletons_step
      ; optim_step_name tapp_over_env_step
      ; optim_step_name tselect_over_either_nil_step
      ; optim_step_name tselect_over_either_nil_app_step
      ; optim_step_name tmap_over_either_nil_step
      ; optim_step_name tmap_over_either_nil_app_step
      ; optim_step_name tappenv_over_either_nil_step
      ; optim_step_name tselect_over_flatten_step
      (* ; optim_step_name tmap_over_flatten_step *)
      ; optim_step_name tconcat_over_rec_eq_step
      ; optim_step_name trproject_nil_step
      ; optim_step_name trproject_over_const_step
      ; optim_step_name trproject_over_rec_step
      ; optim_step_name trproject_over_concat_r_step
      ; optim_step_name trproject_over_concat_l_step
      ; optim_step_name trproject_over_rproject_step
      ; optim_step_name trproject_over_either_step
      ; optim_step_name tcount_over_map_step
      ; optim_step_name tcount_over_flat_map_map_step
      ; optim_step_name tcount_over_flat_map_either_nil_map_step
      ; optim_step_name tcount_over_flat_map_either_nil_app_map_step
      ; optim_step_name tcount_over_flat_map_either_nil_app_singleton_step
      ; optim_step_name tunop_over_either_const_app_step
      ; optim_step_name tunop_over_either_const_step
      ; optim_step_name tmapconcat_over_singleton_step
    ].

  Remark nraenv_default_head_optim_list_valid  {fruntime:foreign_runtime}
    : valid_optims tnraenv_optim_list nraenv_default_head_optim_list = (nraenv_default_head_optim_list,nil).
  Proof.
    vm_compute; trivial.
  Qed.

  (* *************************** *)
  Definition nraenv_default_tail_optim_list {fruntime:foreign_runtime} : list string :=
    [ optim_step_name tflatten_flatten_map_either_nil_step
      ; optim_step_name tmap_over_flatten_map_step
      ; optim_step_name tapp_over_app_step
      ; optim_step_name tappenv_over_appenv_step
      ; optim_step_name tappenv_over_app_step
      ; optim_step_name tapp_over_appenv_step
      ; optim_step_name tmap_into_id_step
      ; optim_step_name tproduct_singletons_step
      ; optim_step_name tproduct_empty_right_step
      ; optim_step_name tproduct_empty_left_step
      ; optim_step_name tmap_singleton_step
      ; optim_step_name tmap_map_compose_step
      ; optim_step_name tflatten_coll_step
      (* only in tail *)
      ; optim_step_name tdouble_flatten_map_coll_step
      ; optim_step_name tflatten_over_double_map_step
      ; optim_step_name tflatten_over_double_map_with_either_step
      ; optim_step_name tflatten_map_coll_step
      ; optim_step_name tapp_over_id_r_step
      ; optim_step_name tapp_over_id_l_step
      ; optim_step_name tapp_over_unop_step
      ; optim_step_name tapp_over_binop_step
      ; optim_step_name tapp_over_select_step
      ; optim_step_name tapp_over_map_step
      ; optim_step_name tapp_over_mapconcat_step
      ; optim_step_name tapp_over_product_step
      ; optim_step_name tappenv_over_unop_step
      ; optim_step_name tcompose_selects_in_mapenv_step
      ; optim_step_name tmap_full_over_select_step
      ; optim_step_name tmerge_empty_record_r_step
      ; optim_step_name tselect_and_step
      ; optim_step_name select_union_distr_step
      ; optim_step_name tdot_from_duplicate_r_step
      ; optim_step_name tdot_from_duplicate_l_step
      ; optim_step_name tconcat_empty_record_r_step
      ; optim_step_name tconcat_empty_record_l_step
      ; optim_step_name tdot_over_concat_r_step
      ; optim_step_name tdot_over_concat_l_step
      ; optim_step_name tmerge_empty_record_r_step
      ; optim_step_name tmerge_empty_record_l_step
      ; optim_step_name tmapenv_to_env_step
      ; optim_step_name tenv_appenv_step
      ; optim_step_name tflatten_mapenv_coll_step
      ; optim_step_name tflatten_nil_step
      ; optim_step_name tapp_over_const_step
      ; optim_step_name tappenv_over_const_step
      ; optim_step_name tflip_env1_step
      ; optim_step_name tflip_env2_step
      ; optim_step_name tmapenv_over_singleton_step
      ; optim_step_name tappenv_over_binop_step
      ; optim_step_name tflip_env6_step
      ; optim_step_name tmapenv_to_map_step
      ; optim_step_name tappenv_over_map_step
      ; optim_step_name tapp_over_ignoreid_step
      ; optim_step_name tappenv_over_ignoreenv_step
      ; optim_step_name tappenv_over_env_r_step
      ; optim_step_name tappenv_over_env_l_step
      ; optim_step_name tappenv_over_env_merge_l_step
      ; optim_step_name tappenv_over_select_step
      ; optim_step_name tmerge_concat_to_concat_step
      ; optim_step_name tmerge_with_concat_to_concat_step
      ; optim_step_name tdot_over_rec_step
      ; optim_step_name tnested_map_over_singletons_step
      ; optim_step_name tapp_over_env_step
      ; optim_step_name tappenv_mapenv_to_map_step
      ; optim_step_name tselect_over_either_nil_step
      ; optim_step_name tselect_over_either_nil_app_step
      ; optim_step_name tmap_over_either_nil_step
      ; optim_step_name tmap_over_either_nil_app_step
      ; optim_step_name tappenv_over_either_nil_step
      ; optim_step_name tselect_over_flatten_step
      ; optim_step_name tmap_over_flatten_step
      ; optim_step_name tconcat_over_rec_eq_step
      ; optim_step_name trproject_nil_step
      ; optim_step_name trproject_over_const_step
      ; optim_step_name trproject_over_rec_step
      ; optim_step_name trproject_over_concat_r_step
      ; optim_step_name trproject_over_concat_l_step
      ; optim_step_name trproject_over_rproject_step
      ; optim_step_name trproject_over_either_step
      ; optim_step_name tcount_over_map_step
      ; optim_step_name tcount_over_flat_map_map_step
      ; optim_step_name tcount_over_flat_map_either_nil_map_step
      ; optim_step_name tcount_over_flat_map_either_nil_app_map_step
      ; optim_step_name tcount_over_flat_map_either_nil_app_singleton_step
      ; optim_step_name tunop_over_either_const_app_step
      ; optim_step_name tunop_over_either_const_step
      ; optim_step_name tmapconcat_over_singleton_step
    ].

    Remark nraenv_default_tail_optim_list_valid  {fruntime:foreign_runtime}
    : valid_optims tnraenv_optim_list nraenv_default_tail_optim_list = (nraenv_default_tail_optim_list,nil).
  Proof.
    vm_compute; trivial.
  Qed.

    Definition default_nraenv_optim_phases {fruntime:foreign_runtime} :=
      ("[nraenv] head"%string,nraenv_default_head_optim_list,5)
        :: ("[nraenv] tail"%string,nraenv_default_tail_optim_list,15)
        :: nil.

  End default.

  Definition toptim_old_nraenv_head {fruntime:foreign_runtime} {logger:optimizer_logger string nraenv}
    := run_nraenv_optims (("head",nraenv_default_head_optim_list,5)::nil).

  Lemma toptim_old_nraenv_head_correctness {model:basic_model} {logger:optimizer_logger string nraenv} p:
    p ⇒ₓ toptim_old_nraenv_head p.
  Proof.
    unfold toptim_old_nraenv_head.
    apply run_nraenv_optims_correctness.
  Qed.
  
  Definition toptim_old_nraenv_tail {fruntime:foreign_runtime} {logger:optimizer_logger string nraenv} 
    := run_nraenv_optims (("tail",nraenv_default_head_optim_list,15)::nil).

  Lemma toptim_old_nraenv_tail_correctness {model:basic_model} {logger:optimizer_logger string nraenv} p:
    p ⇒ₓ toptim_old_nraenv_tail p.
  Proof.
    unfold toptim_old_nraenv_tail.
    apply run_nraenv_optims_correctness.
  Qed.

  Definition toptim_old_nraenv {fruntime:foreign_runtime} {logger:optimizer_logger string nraenv} :=
    compose toptim_old_nraenv_tail toptim_old_nraenv_head.

  Lemma compose_transitivity {A:Type} {R:relation A} {trans:Transitive R}
        (x y:A) (f g :A->A):
    R x (g y) ->
    R (g y) (f (g y)) ->
    R x ((compose f g) y).
  Proof.
    intros.
    etransitivity; eauto.
  Qed.
    
  Lemma toptim_old_nraenv_correctness {model:basic_model} {logger:optimizer_logger string nraenv} p:
    p ⇒ₓ toptim_old_nraenv p.
  Proof.
    unfold toptim_old_nraenv.
    apply compose_transitivity.
    - apply toptim_old_nraenv_head_correctness.
    - apply toptim_old_nraenv_tail_correctness.
  Qed.

End NRAEnvOptimizer.

