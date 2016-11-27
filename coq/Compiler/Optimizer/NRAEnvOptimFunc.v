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

Section NRAEnvOptimFunc.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.
  Require Import String List ListSet.

  Require Import Utils BasicSystem.
  Require Import NRAEnvSystem.
  Require Import OptimizerLogger.

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
      | NRAEnvMapConcat op1 op2 => NRAEnvMapConcat (f op1) (f op2)
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
      | NRAEnvProject sl op1 => NRAEnvProject sl (f op1)
      | NRAEnvGroupBy s sl op1 => NRAEnvGroupBy s sl (f op1)
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
      | NRAEnvMapConcat op1 op2 => f (NRAEnvMapConcat (nraenv_map_deep f op1) (nraenv_map_deep f op2))
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
      | NRAEnvProject sl op1 => f (NRAEnvProject sl (nraenv_map_deep f op1))
      | NRAEnvGroupBy s sl op1 => f (NRAEnvGroupBy s sl (nraenv_map_deep f op1))
    end.

    Fixpoint optim_iter (optim: nraenv -> nraenv) (fuel: nat) (p: nraenv) :=
      match fuel with
      | 0 => p
      | S n => optim_iter optim n (optim p)
      end.

    Require Import Recdef.
    Require Import Compare_dec.

    Function optim_cost (optim: nraenv -> nraenv) (cost: nraenv -> nat) (p: nraenv) { measure cost p } :=
      let p' := optim p in
      match nat_compare (cost p') (cost p) with
      | Lt => optim_cost optim cost p'
      | _ => p
      end.
    Proof.
      intros optim cost p Hcmp.
      apply nat_compare_lt in Hcmp.
      exact Hcmp.
    Defined.

    Definition optim_size (optim: nraenv -> nraenv) (p: nraenv) :=
      optim_cost optim nraenv_size p.

  End rewriter.

  Section dup.
    Fixpoint nodupA_checker {bm:basic_model} (p:nraenv) : bool
    := match p with
       | NRAEnvUnop ADistinct _ => true
       | NRAEnvBinop AMinus p₁ p₂ => nodupA_checker p₂
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
        specialize (IHp2 nd).
        specialize (IHp2 h c dn_c env dn_env x dn_x _ H1).
        simpl in IHp2.
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

    Definition dup_elim_fun {bm:basic_model} (p:nraenv) :=
      match p with
      | NRAEnvUnop ADistinct q  =>
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
      rewrite lift_nraenv_eq_to_algenv_eq. simpl.
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

  Lemma optim_iter_correctness {model:basic_model} optim n p:
    (forall p', p' ⇒ₓ optim p') -> p ⇒ₓ optim_iter optim n p.
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
    (forall p', p' ⇒ₓ optim p') -> p ⇒ₓ optim_cost optim cost p.
  Proof.
    intros Hoptim.
    functional induction optim_cost optim cost p.
    - apply (tnraenv_rewrites_to_trans p (optim p)).
      + apply Hoptim.
      + apply IHn.
    - reflexivity.
  Qed.
  Hint Rewrite @optim_cost_correctness : optim_correct.

  Lemma optim_size_correctness {model:basic_model} optim p:
    (forall p', p' ⇒ₓ optim p') -> p ⇒ₓ optim_size optim p.
  Proof.
    intros Hoptim.
    unfold optim_size.
    apply optim_cost_correctness.
    assumption.
  Qed.
  Hint Rewrite @optim_size_correctness : optim_correct.

  (****************)

  (* P1 ∧ P2 ⇒ₓ P2 ∧ P1 *)

  Definition tand_comm_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvBinop AAnd op1 op2 => NRAEnvBinop AAnd op2 op1
      | _ => p
    end.

  Lemma tand_comm_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tand_comm_fun p.
  Proof.
    tprove_correctness p.
    apply tand_comm_arrow.
  Qed.
  Hint Rewrite @tand_comm_fun_correctness : optim_correct.


  (* σ{P1 ∧ P2}(P) ⇒ₓ σ{P2 ∧ P1}(P) *) (* XXX Why neessary ? *)

  Definition tselect_and_comm_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvSelect (NRAEnvBinop AAnd op1 op2) op =>
        NRAEnvSelect (NRAEnvBinop AAnd op2 op1) op
      | _ => p
    end.

  Lemma tselect_and_comm_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tselect_and_comm_fun p.
  Proof.
    tprove_correctness p.
    apply tselect_and_comm_arrow.
  Qed.
  Hint Rewrite @tselect_and_comm_fun_correctness : optim_correct.

  (* σ{P1}(σ{P2}(P3)) ⇒ₓ σ{P2 ∧ P1}(P3)) *)

  Definition tselect_and_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvSelect op1 (NRAEnvSelect op2 op) =>
        NRAEnvSelect (NRAEnvBinop AAnd op2 op1) op
      | _ => p
    end.

  Lemma tselect_and_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tselect_and_fun p.
  Proof.
    tprove_correctness p.
    apply tselect_and_arrow.
  Qed.
  Hint Rewrite @tselect_and_fun_correctness : optim_correct.

  (* [ a1 : p1; a2 : p2 ].a2 ⇒ₓ p2 *)

  Definition tenvdot_from_duplicate_r_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvUnop (ADot s2)
               (NRAEnvBinop AConcat (NRAEnvUnop (ARec s1) op1) (NRAEnvUnop (ARec s2') op2)) =>
        if s2 == s2' then
          op2
        else
          p
      | _ => p
    end.

  Lemma tenvdot_from_duplicate_r_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tenvdot_from_duplicate_r_fun p.
  Proof.
    tprove_correctness p. 
    apply tenvdot_from_duplicate_r_arrow.
  Qed.
  Hint Rewrite @tenvdot_from_duplicate_r_fun_correctness : optim_correct.

  (* [ a1 : p1; a2 : p2 ].a1 ⇒ₓ p1 *)

  Definition tenvdot_from_duplicate_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvUnop (ADot s1)
               (NRAEnvBinop AConcat (NRAEnvUnop (ARec s1') op1) (NRAEnvUnop (ARec s2) op2)) =>
        if (s1 <> s2) then
          if s1 == s1' then op1
          else p
        else p
      | _ => p
    end.

  Lemma tenvdot_from_duplicate_l_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tenvdot_from_duplicate_l_fun p.
  Proof.
    tprove_correctness p. 
    apply tenvdot_from_duplicate_l_arrow.
    assumption.
  Qed.
  Hint Rewrite @tenvdot_from_duplicate_l_fun_correctness : optim_correct.


  (* ♯flatten({ p }) ⇒ₓ p when p's output type is a collection *)
  Definition tenvflatten_coll_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvUnop AFlatten (NRAEnvUnop AColl p) => p
      | _ => p
    end.

  Lemma tenvflatten_coll_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tenvflatten_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tenvflatten_coll_arrow.
  Qed.
  Hint Rewrite @tenvflatten_coll_fun_correctness : optim_correct.

  (* p ⊕ [] ⇒ₓ p when p returns a record *)
  Definition tconcat_empty_record_r_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      |  NRAEnvBinop AConcat p (NRAEnvConst (drec [])) =>
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

  (* [] ⊕ p ⇒ₓ p when p returns a record *)
  Definition tconcat_empty_record_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      |  NRAEnvBinop AConcat (NRAEnvConst (drec [])) p =>
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

  Definition tdot_over_concat_r_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    |  NRAEnvUnop (ADot a₂) (NRAEnvBinop AConcat q₁ (NRAEnvUnop (ARec a₁) q₂)) =>
       if a₁ == a₂
       then q₂
       else NRAEnvUnop (ADot a₂) q₁
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

  Definition tdot_over_concat_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    |  NRAEnvUnop (ADot a₂) (NRAEnvBinop AConcat (NRAEnvUnop (ARec a₁) q₁) q₂) =>
       if a₁ == a₂
       then p
       else NRAEnvUnop (ADot a₂) q₂
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

  (* p ⊗ [] ⇒ₓ { p } when p returns a record *)
  Definition tmerge_empty_record_r_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      |  NRAEnvBinop AMergeConcat p (NRAEnvConst (drec [])) =>
         NRAEnvUnop AColl p
      | _ => p
    end.

  Lemma tmerge_empty_record_r_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmerge_empty_record_r_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_empty_record_r_arrow.
  Qed.
  Hint Rewrite @tmerge_empty_record_r_fun_correctness : optim_correct.

  (* [] ⊗ p ⇒ₓ { p } when p returns a record *)
  Definition tmerge_empty_record_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      |  NRAEnvBinop AMergeConcat (NRAEnvConst (drec [])) p =>
         NRAEnvUnop AColl p
      | _ => p
    end.

  Lemma tmerge_empty_record_l_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmerge_empty_record_l_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_empty_record_l_arrow.
  Qed.
  Hint Rewrite @tmerge_empty_record_l_fun_correctness : optim_correct.

  (* χ⟨ ID ⟩( p ) ⇒ₓ p *)
  Definition tenvmap_into_id_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvMap NRAEnvID p => p
      | _ => p
    end.

  Lemma tenvmap_into_id_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tenvmap_into_id_fun p.
  Proof.
    tprove_correctness p.
    apply tenvmap_into_id_arrow.
  Qed.
  Hint Rewrite @tenvmap_into_id_fun_correctness : optim_correct.


  (* ♯flatten(χ⟨ { p1 } ⟩( p2 )) ⇒ₓ χ⟨ p1 ⟩( p2 ) *)
  Definition tenvflatten_map_coll_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvUnop AFlatten (NRAEnvMap (NRAEnvUnop AColl p1) p2) =>
        NRAEnvMap p1 p2
      | _ => p
    end.

  Lemma tenvflatten_map_coll_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tenvflatten_map_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tenvflatten_map_coll_arrow.
  Qed.
  Hint Rewrite @tenvflatten_map_coll_fun_correctness : optim_correct.

  Definition tflatten_flatten_map_either_nil_fun {fruntime:foreign_runtime} (p: nraenv) :=
      match p with
        NRAEnvUnop AFlatten
                   (NRAEnvUnop AFlatten (NRAEnvMap (NRAEnvApp (NRAEnvEither p₁ (NRAEnvConst (dcoll nil))) p₂) p₃)) =>
        NRAEnvUnop AFlatten (NRAEnvMap (NRAEnvApp
                                          (NRAEnvEither (NRAEnvUnop AFlatten p₁)
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

  (* χ⟨ P1 ⟩( χ⟨ P2 ⟩( P3 ) ) ⇒ₓ χ⟨ P1 ◯ P2 ⟩( P3 ) *)
  Definition tenvmap_map_compose_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvMap p1 (NRAEnvMap p2 p3) => NRAEnvMap (NRAEnvApp p1 p2) p3
      | _ => p
    end.

  Lemma tenvmap_map_compose_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tenvmap_map_compose_fun p.
  Proof.
    tprove_correctness p.
    apply tenvmap_map_compose_arrow.
  Qed.
  Hint Rewrite @tenvmap_map_compose_fun_correctness : optim_correct.


  (* χ⟨ P1 ⟩( { P2 } ) ⇒ₓ { P1 ◯ P2 } *)
  Definition tenvmap_singleton_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvMap p1 (NRAEnvUnop AColl p2) => NRAEnvUnop AColl (NRAEnvApp p1 p2)
      | _ => p
    end.

  Lemma tenvmap_singleton_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tenvmap_singleton_fun p.
  Proof.
    tprove_correctness p.
    apply tenvmap_singleton_arrow.
  Qed.
  Hint Rewrite @tenvmap_singleton_fun_correctness : optim_correct.

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
    apply nraenv_ignores_id_algenv_eq; assumption.
  Qed.

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
    apply nraenv_ignores_env_algenv_eq; assumption.
  Qed.

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
      generalize nraenv_ignores_env_algenv_eq; intros.
      unfold algenv_of_nraenv in *.
      apply H0; assumption.
    - case_eq (nraenv_ignores_id_fun p2); intros.
      + apply tappenv_over_app_arrow.
        rewrite <- nraenv_ignores_id_eq in H0.
        generalize nraenv_ignores_id_algenv_eq; intros.
        unfold algenv_of_nraenv in *.
        apply H1; assumption.
      + reflexivity.
  Qed.

  Hint Rewrite @tappenv_over_app_fun_correctness : optim_correct.

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
      generalize nraenv_ignores_id_algenv_eq; intros.
      unfold algenv_of_nraenv in *.
      apply H0; assumption.
    - reflexivity.
  Qed.

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

  (* ⋈ᵈ⟨ q₁ ⟩( q₂ ) ◯ q ⇒ₓ ⋈ᵈ⟨ q₁ ⟩( q₂ ◯ q ) *)

  Definition tapp_over_mapconcat_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvApp (NRAEnvMapConcat p1 p2) p0 =>
        NRAEnvMapConcat p1 (NRAEnvApp p2 p0)
      | _ => p
    end.

  Lemma tapp_over_mapconcat_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tapp_over_mapconcat_fun p.
  Proof.
    tprove_correctness p.
    apply tapp_over_mapconcat_arrow.
  Qed.
  Hint Rewrite @tapp_over_mapconcat_fun_correctness : optim_correct.

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
    rewrite lift_tnraenv_eq_to_talgenv_eq. simpl.
    rewrite tappenv_over_map_arrow.
    reflexivity.
    rewrite <- nraenv_ignores_id_eq in H.
    apply nraenv_ignores_id_algenv_eq; assumption.
  Qed.

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
    rewrite lift_tnraenv_eq_to_talgenv_eq. simpl.
    rewrite tappenv_over_select_arrow.
    reflexivity.
    rewrite <- nraenv_ignores_id_eq in H.
    apply nraenv_ignores_id_algenv_eq; assumption.
  Qed.

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


  (* { [ s1 : p1 ] } × { [ s2 : p2 ] } ⇒ₓ { [ s1 : p1; s2 : p2 ] } *)
  Definition tproduct_singletons_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvProduct (NRAEnvUnop AColl (NRAEnvUnop (ARec s1) p1))
                  (NRAEnvUnop AColl (NRAEnvUnop (ARec s2) p2)) =>
        NRAEnvUnop AColl
               (NRAEnvBinop AConcat (NRAEnvUnop (ARec s1) p1) (NRAEnvUnop (ARec s2) p2))
      | _ => p
    end.

  Lemma tproduct_singletons_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tproduct_singletons_fun p.
  Proof.
    tprove_correctness p.
    apply tproduct_singletons_arrow.
  Qed.
  Hint Rewrite @tproduct_singletons_fun_correctness : optim_correct.


  (* ♯flatten(χ⟨ χ⟨ { p3 } ⟩( p1 ) ⟩( p2 )) ⇒ₓ χ⟨ { p3 } ⟩(♯flatten(χ⟨ p1 ⟩( p2 ))) *)
  Definition tdouble_flatten_map_coll_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
        NRAEnvUnop AFlatten
               (NRAEnvMap (NRAEnvMap (NRAEnvUnop AColl p3) p1) p2) =>
        NRAEnvMap (NRAEnvUnop AColl p3)
              (NRAEnvUnop AFlatten (NRAEnvMap p1 p2))
      | _ => p
    end.

  Lemma tdouble_flatten_map_coll_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tdouble_flatten_map_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tdouble_flatten_map_coll_arrow.
  Qed.
  Hint Rewrite @tdouble_flatten_map_coll_fun_correctness : optim_correct.

  (* ♯flatten(χ⟨ χ⟨ { p3 } ⟩( p1 ) ⟩( p2 )) ⇒ₓ χ⟨ { p3 } ⟩(♯flatten(χ⟨ p1 ⟩( p2 ))) *)
  Definition tflatten_over_double_map_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | (NRAEnvUnop AFlatten
                (NRAEnvMap (NRAEnvMap q₁ (NRAEnvSelect q₂ (NRAEnvUnop AColl NRAEnvID))) q₃))
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

  (* ♯flatten(χ⟨ χ⟨ { p3 } ⟩( p1 ) ⟩( p2 )) ⇒ₓ χ⟨ { p3 } ⟩(♯flatten(χ⟨ p1 ⟩( p2 ))) *)
  Definition tflatten_over_double_map_with_either_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | (NRAEnvUnop AFlatten
              (NRAEnvMap
                 (NRAEnvMap q₁
                        (NRAEnvSelect q₂
                                  (NRAEnvApp
                                     (NRAEnvEither (NRAEnvUnop AColl NRAEnvID) (NRAEnvConst (dcoll []))) q₃)))
                 q₄)) =>
      (NRAEnvMap q₁
             (NRAEnvSelect q₂
                       (NRAEnvUnop AFlatten
                               (NRAEnvMap
                                  (NRAEnvApp
                                     (NRAEnvEither (NRAEnvUnop AColl NRAEnvID) (NRAEnvConst (dcoll []))) q₃)
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

  (* ignores_env p1 -> (ENV ⊗ p1) ◯ₑ p2 ⇒ₓ p2 ⊗ p1 *)
  Definition tappenv_over_env_merge_l_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvAppEnv (NRAEnvBinop AMergeConcat NRAEnvEnv p1) p2 =>
        if (nraenv_ignores_env_fun p1)
        then (NRAEnvBinop AMergeConcat p2 p1)
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
    generalize nraenv_ignores_env_algenv_eq; intros.
    unfold algenv_of_nraenv in *.
    apply H0; assumption.
  Qed.

  Definition tmerge_with_empty_rec_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvBinop AMergeConcat p1 (NRAEnvConst (drec nil)) =>
        NRAEnvUnop AColl p1
      | _ => p
    end.

  Lemma tmerge_with_empty_rec_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tmerge_with_empty_rec_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_empty_record_r_arrow.
  Qed.

  Definition ttostring_on_string_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvUnop AToString (NRAEnvConst (dstring s)) =>
        NRAEnvConst (dstring s)
      | NRAEnvUnop AToString (NRAEnvUnop AToString p) =>
        NRAEnvUnop AToString p
      | NRAEnvUnop AToString (NRAEnvBinop ASConcat p1 p2) =>
        (NRAEnvBinop ASConcat p1 p2)
      | _ => p
    end.

  Lemma ttostring_on_string_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ ttostring_on_string_fun p.
  Proof.
    tprove_correctness p.
    - apply ttostring_dstring_arrow.
    - apply ttostring_sconcat_arrow.
    - apply ttostring_tostring_arrow.
  Qed.

  Definition tmap_full_over_select_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvMap p0 (NRAEnvSelect p1 (NRAEnvUnop AColl NRAEnvID)) => p
      | NRAEnvMap p0 (NRAEnvSelect p1 (NRAEnvUnop AColl p2)) =>
        NRAEnvMap (NRAEnvApp p0 p2) (NRAEnvSelect (NRAEnvApp p1 p2) (NRAEnvUnop AColl NRAEnvID))
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

  Definition tcompose_selects_in_mapenv_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | (NRAEnvAppEnv
           (NRAEnvUnop AFlatten
                   (NRAEnvMapEnv (NRAEnvMap NRAEnvEnv (NRAEnvSelect p1 (NRAEnvUnop AColl NRAEnvID)))))
           (NRAEnvMap NRAEnvEnv (NRAEnvSelect p2 (NRAEnvUnop AColl NRAEnvID)))) =>
        (NRAEnvMap NRAEnvEnv (NRAEnvSelect p1 (NRAEnvSelect p2 (NRAEnvUnop AColl NRAEnvID))))
      | _ => p
    end.
  
  Lemma tcompose_selects_in_mapenv_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tcompose_selects_in_mapenv_fun p.
  Proof.
    tprove_correctness p.
    apply tcompose_selects_in_mapenv_arrow.
  Qed.

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

  Definition tflatten_mapenv_coll_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop AFlatten (NRAEnvMapEnv (NRAEnvUnop AColl p1)) =>
        NRAEnvMapEnv p1
      | _ => p
    end.

  Lemma  tflatten_mapenv_coll_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tflatten_mapenv_coll_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_mapenv_coll_arrow.
  Qed.

  Definition tflatten_nil_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop AFlatten (NRAEnvConst (dcoll nil)) =>
        NRAEnvConst (dcoll nil)
      | _ => p
    end.

  Lemma  tflatten_nil_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tflatten_nil_fun p.
  Proof.
    tprove_correctness p.
    apply tenvflatten_nil_arrow.
  Qed.

  Definition tflatten_through_appenv_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | NRAEnvUnop AFlatten (NRAEnvAppEnv p1 p2) =>
        NRAEnvAppEnv (NRAEnvUnop AFlatten p1) p2
      | _ => p
    end.

  Lemma tflatten_through_appenv_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tflatten_through_appenv_fun p.
  Proof.
    tprove_correctness p.
    apply tflatten_through_appenv_arrow.
  Qed.

  Definition tappenv_flatten_mapenv_to_map_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      | (NRAEnvAppEnv (NRAEnvUnop AFlatten (NRAEnvMapEnv p2))
            (NRAEnvBinop AMergeConcat NRAEnvEnv (NRAEnvUnop (ARec s) NRAEnvID))) =>
         (NRAEnvUnop AFlatten
            (NRAEnvMap (NRAEnvAppEnv (NRAEnvApp p2 (NRAEnvUnop (ADot s) NRAEnvEnv)) NRAEnvID)
                   (NRAEnvBinop AMergeConcat NRAEnvEnv (NRAEnvUnop (ARec s) NRAEnvID))))
      | _ => p
    end.
  
  Lemma tappenv_flatten_mapenv_to_map_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tappenv_flatten_mapenv_to_map_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_flatten_mapenv_to_map_arrow.
  Qed.

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
    rewrite lift_tnraenv_eq_to_talgenv_eq. simpl.
    rewrite tselect_over_either.
    rewrite tselect_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tselect_over_either_nil_fun_correctness : toptim_correct.

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
    rewrite lift_tnraenv_eq_to_talgenv_eq. simpl.
    rewrite tselect_over_app_either.
    rewrite tselect_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tselect_over_either_nil_app_fun_correctness : toptim_correct.

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
    rewrite lift_tnraenv_eq_to_talgenv_eq. simpl.
    rewrite tmap_over_either.
    rewrite tmap_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tmap_over_either_nil_fun_correctness : toptim_correct.

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
    rewrite lift_tnraenv_eq_to_talgenv_eq. simpl.
    rewrite tmap_over_either_app.
    rewrite tmap_over_nil.
    reflexivity.
  Qed.

  Hint Rewrite @tmap_over_either_nil_app_fun_correctness : toptim_correct.

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
    rewrite lift_tnraenv_eq_to_talgenv_eq. simpl.
    autorewrite with talgenv_optim.
    - reflexivity.
    - apply nraenv_ignores_id_algenv_eq; assumption.
  Qed.

  Hint Rewrite @tappenv_over_either_nil_fun_correctness : toptim_correct.

  Definition tselect_over_flatten_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvSelect p₁ (NRAEnvUnop AFlatten p₂) =>
      NRAEnvUnop AFlatten (NRAEnvMap (NRAEnvSelect p₁ NRAEnvID) p₂)
    | _ => p
    end.

  Lemma tselect_over_flatten_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tselect_over_flatten_fun p.
  Proof.
    tprove_correctness p.
    apply tselect_over_flatten.
  Qed.

  Hint Rewrite @tselect_over_flatten_fun_correctness : toptim_correct.

  Definition tmap_over_flatten_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvMap p₁ (NRAEnvUnop AFlatten p₂) =>
      NRAEnvUnop AFlatten (NRAEnvMap (NRAEnvMap p₁ NRAEnvID) p₂)
    | _ => p
    end.

  Lemma tmap_over_flatten_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmap_over_flatten_fun p.
  Proof.
    tprove_correctness p.
    apply tmap_over_flatten.
  Qed.

  Hint Rewrite @tmap_over_flatten_fun_correctness : toptim_correct.

  Definition tmap_over_flatten_map_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvMap p₁ (NRAEnvUnop AFlatten (NRAEnvMap p₂ p₃)) =>
      NRAEnvUnop AFlatten (NRAEnvMap (NRAEnvMap p₁ p₂) p₃)
      | _ => p
    end.

  Lemma tmap_over_flatten_map_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tmap_over_flatten_map_fun p.
  Proof.
    tprove_correctness p.
    apply tmap_over_flatten_map.
  Qed.

  Hint Rewrite @tmap_over_flatten_map_fun_correctness : toptim_correct.

  Definition tconcat_over_rec_eq_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | (NRAEnvBinop AConcat
                 (NRAEnvUnop (ARec s₁) p₁) (NRAEnvUnop (ARec s₂) p₂))
        => if string_dec s₁ s₂ 
           then (NRAEnvUnop (ARec s₂) p₂)
           else p
      | _ => p
    end.

  Definition tconcat_over_rec_eq_fun_correctness {model:basic_model} p :
    p ⇒ₓ tconcat_over_rec_eq_fun p.
  Proof.
    tprove_correctness p.
    rewrite lift_tnraenv_eq_to_talgenv_eq. simpl.
    rewrite tconcat_over_rec_eq.
    reflexivity.
  Qed.
                  
  Hint Rewrite @tconcat_over_rec_eq_fun_correctness : toptim_correct.

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

  Definition tflip_env1_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvAppEnv (NRAEnvMap NRAEnvEnv (NRAEnvSelect q₁ (NRAEnvUnop AColl NRAEnvID))) q₂ =>
      match q₂ with
      | NRAEnvID => (NRAEnvAppEnv (NRAEnvSelect q₁ (NRAEnvUnop AColl NRAEnvID)) NRAEnvID)
      | _ =>
        if (nraenv_ignores_env_fun q₁)
        then NRAEnvMap q₂ (NRAEnvSelect q₁ (NRAEnvUnop AColl NRAEnvID))
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
    generalize nraenv_ignores_env_algenv_eq; intros;
    unfold algenv_of_nraenv in *;
    apply H0; assumption.
  Qed.

  Definition tflip_env2_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      (NRAEnvAppEnv (NRAEnvSelect p (NRAEnvUnop AColl NRAEnvID)) NRAEnvID) =>
      (NRAEnvSelect (NRAEnvAppEnv p NRAEnvID) (NRAEnvUnop AColl NRAEnvID))
    | _ => p
    end.
  
  Lemma tflip_env2_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tflip_env2_fun p.
  Proof.
    tprove_correctness p.
    apply tflip_env2_arrow.
  Qed.

  Definition tmapenv_over_singleton_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      (NRAEnvAppEnv (NRAEnvMapEnv p1) (NRAEnvUnop AColl p2)) =>
      (NRAEnvUnop AColl (NRAEnvAppEnv p1 p2))
    | _ => p
    end.

  Lemma tmapenv_over_singleton_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tmapenv_over_singleton_fun p.
  Proof.
    tprove_correctness p.
    apply tmapenv_over_singleton_arrow.
  Qed.

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

  Definition tflip_env6_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvMap (NRAEnvBinop AMergeConcat NRAEnvEnv NRAEnvID)
                (NRAEnvSelect p1 (NRAEnvBinop AMergeConcat NRAEnvEnv p2)) =>
      NRAEnvMap (NRAEnvUnop AColl NRAEnvID)
                (NRAEnvSelect p1 (NRAEnvBinop AMergeConcat NRAEnvEnv p2))
    | _ => p
    end.
  
  Lemma tflip_env6_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tflip_env6_fun p.
  Proof.
    tprove_correctness p.
    apply tflip_env6_arrow.
  Qed.

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
    generalize nraenv_ignores_id_algenv_eq; intros.
    unfold algenv_of_nraenv in *.
    apply H0; assumption.
  Qed.

  Definition tmerge_concat_to_concat_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvBinop AMergeConcat (NRAEnvUnop (ARec s1) p1) (NRAEnvUnop (ARec s2) p2) =>
      if (s1 == s2)
      then p
      else NRAEnvUnop AColl
                      (NRAEnvBinop AConcat
                                   (NRAEnvUnop (ARec s1) p1)
                                   (NRAEnvUnop (ARec s2) p2))
    | _ => p
    end.

  Lemma tmerge_concat_to_concat_fun_correctness {model:basic_model} (p: nraenv) :
    p ⇒ₓ tmerge_concat_to_concat_fun p.
  Proof.
    tprove_correctness p.
    apply tmerge_concat_to_concat_arrow.
    trivial.
  Qed.

  Definition tmerge_with_concat_to_concat_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
    | NRAEnvBinop AMergeConcat (NRAEnvUnop (ARec s1) p1)
                  (NRAEnvBinop AConcat (NRAEnvUnop (ARec s1') p1')
                               (NRAEnvUnop (ARec s2) p2)) =>
        if (s1 == s2)
        then p
        else
          if (s1 == s1')
          then
            if (p1 == p1')
            then NRAEnvUnop AColl (NRAEnvBinop AConcat
                                               (NRAEnvUnop (ARec s1) p1)
                                               (NRAEnvUnop (ARec s2) p2))
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

  Definition tdot_over_rec_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop (ADot s2)
                 (NRAEnvUnop (ARec s1) p1) =>
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

  Definition tnested_map_over_singletons_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop AFlatten
                 (NRAEnvMap (NRAEnvSelect q₁ (NRAEnvUnop AColl q₂)) q₃) =>
      NRAEnvSelect q₁ (NRAEnvMap q₂ q₃)
    | _ => p
    end.

  Lemma tnested_map_over_singletons_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tnested_map_over_singletons_fun p.
  Proof.
    tprove_correctness p.
    apply tnested_map_over_singletons_arrow.
  Qed.

  Definition tappenv_mapenv_to_map_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvAppEnv (NRAEnvMapEnv q)
                   (NRAEnvBinop AMergeConcat NRAEnvEnv (NRAEnvUnop (ARec a) NRAEnvID)) =>
      NRAEnvMap (NRAEnvAppEnv (NRAEnvApp q (NRAEnvUnop (ADot a) NRAEnvEnv)) NRAEnvID)
                (NRAEnvBinop AMergeConcat NRAEnvEnv (NRAEnvUnop (ARec a) NRAEnvID))
    | _ => p
    end.

  Lemma tappenv_mapenv_to_map_fun_correctness {model:basic_model} (p:nraenv) :
    p ⇒ₓ tappenv_mapenv_to_map_fun p.
  Proof.
    tprove_correctness p.
    apply tappenv_mapenv_to_map_arrow.
  Qed.

  (* optimizations for rproject *)

   Definition trproject_nil_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (ARecProject nil) p₁
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

  Definition trproject_over_const_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (ARecProject sl)
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
  
  Definition trproject_over_rec_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (ARecProject sl)
          (NRAEnvUnop (ARec s) p₁)
        => if in_dec string_dec s sl
           then NRAEnvUnop (ARec s) p₁
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

  Definition trproject_over_concat_r_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (ARecProject sl)
               (NRAEnvBinop AConcat
                        p₁ (NRAEnvUnop (ARec s) p₂))
        => if in_dec string_dec s sl
           then NRAEnvBinop AConcat
                        (NRAEnvUnop (ARecProject (remove string_dec s sl)) p₁)
                        (NRAEnvUnop (ARec s) p₂)
           else (NRAEnvUnop (ARecProject sl) p₁)
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

  Definition trproject_over_concat_l_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (ARecProject sl)
               (NRAEnvBinop AConcat
                        (NRAEnvUnop (ARec s) p₁) p₂)
        => if in_dec string_dec s sl
                     (* this case would need shape/type inference to handle, since we don't know if s is in p₂ *)

           then p
           else (NRAEnvUnop (ARecProject sl) p₂)
      | _ => p
    end.

  Definition trproject_over_concat_l_fun_correctness {model:basic_model} p :
    p ⇒ₓ trproject_over_concat_l_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_over_concat_rec_l_nin; trivial.
  Qed.

  Hint Rewrite @trproject_over_concat_l_fun_correctness : toptim_correct.

  Definition trproject_over_rproject_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (ARecProject sl1)
          (NRAEnvUnop (ARecProject sl2) p1)
        => NRAEnvUnop (ARecProject (set_inter string_dec sl2 sl1)) p1
      | _ => p
    end.

  Definition trproject_over_rproject_fun_correctness {model:basic_model} p :
    p ⇒ₓ trproject_over_rproject_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_over_rproject.
  Qed.

  Hint Rewrite @trproject_over_rproject_fun_correctness : toptim_correct.

  Definition trproject_over_either_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop (ARecProject sl)
          (NRAEnvEither p₁ p₂)
        => NRAEnvEither (NRAEnvUnop (ARecProject sl) p₁) (NRAEnvUnop (ARecProject sl) p₂)
      | _ => p
    end.

  Definition trproject_over_either_fun_correctness {model:basic_model} p :
    p ⇒ₓ trproject_over_either_fun p.
  Proof.
    tprove_correctness p.
    apply trproject_over_either.
  Qed.

  Hint Rewrite @trproject_over_either_fun_correctness : toptim_correct.

  Definition tcount_over_map_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
      | NRAEnvUnop ACount (NRAEnvMap p₁ p₂) => NRAEnvUnop ACount p₂
      | _ => p
    end.

  Definition tcount_over_map_fun_correctness {model:basic_model} p :
    p ⇒ₓ tcount_over_map_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_map.
  Qed.

  Hint Rewrite @tcount_over_map_fun_correctness : toptim_correct.
  
  Definition tcount_over_flat_map_map_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop ACount
                 (NRAEnvUnop AFlatten
                             (NRAEnvMap (NRAEnvMap p₁ p₂) p₃)) =>
      NRAEnvUnop ACount (NRAEnvUnop AFlatten (NRAEnvMap p₂ p₃))
    | _ => p
    end.

  Definition tcount_over_flat_map_map_fun_correctness {model:basic_model} p :
    p ⇒ₓ tcount_over_flat_map_map_fun p.
  Proof.
    tprove_correctness p.
    apply tcount_over_flat_map_map.
  Qed.

  Hint Rewrite @tcount_over_flat_map_map_fun_correctness : toptim_correct.

  Definition tcount_over_flat_map_either_nil_map_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop ACount
                 (NRAEnvUnop AFlatten
                             (NRAEnvMap (NRAEnvEither (NRAEnvMap p₁ p₂)
                                                      (NRAEnvConst (dcoll nil)))
                                        p₃)) =>
      NRAEnvUnop ACount
                 (NRAEnvUnop AFlatten
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

  Definition tcount_over_flat_map_either_nil_app_map_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop ACount
                 (NRAEnvUnop AFlatten
                             (NRAEnvMap (NRAEnvApp (NRAEnvEither (NRAEnvMap p₁ p₂)
                                                                 (NRAEnvConst (dcoll nil))) p₄)
                                        p₃)) =>
      NRAEnvUnop ACount
                 (NRAEnvUnop AFlatten
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

  Definition tcount_over_flat_map_either_nil_app_singleton_fun {fruntime:foreign_runtime} (p:nraenv) :=
    match p with
    | NRAEnvUnop ACount
                 (NRAEnvUnop AFlatten
                             (NRAEnvMap (NRAEnvApp (NRAEnvEither (NRAEnvUnop AColl p₁)
                                                                 (NRAEnvConst (dcoll nil))) p₃) p₂)) =>
      NRAEnvUnop ACount
                 (NRAEnvUnop AFlatten
                             (NRAEnvMap (NRAEnvApp (NRAEnvEither (NRAEnvUnop AColl (NRAEnvConst dunit))
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

  (* optimizations for mapconcat *)

  (* ⋈ᵈ⟨ p₁ ⟩(‵{| ‵[||] |}) ⇒ₓ p₁ ◯ (‵[||]) *)
  Definition tmapconcat_over_singleton_fun {fruntime:foreign_runtime} (p: nraenv) :=
    match p with
      |  NRAEnvMapConcat p (NRAEnvUnop AColl (NRAEnvConst (drec []))) =>
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

  Definition tdup_elim_fun {model:basic_model} (p:nraenv) :=
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

  
  (* *************************** *)
  Local Open Scope string.
  Definition head_optim_list {fruntime:foreign_runtime} : list (string*(nraenv -> nraenv)) :=
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

  Definition head_optim
             {fruntime:foreign_runtime}
             {logger:optimizer_logger string nraenv} (name:string)
    : nraenv -> nraenv :=
    apply_steps ("nra_head" ++ name) head_optim_list.
  
  Lemma head_optim_correctness {model:basic_model} {logger:optimizer_logger string nraenv} (name:string) (p:nraenv) :
    p ⇒ₓ head_optim name p.
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

  Definition tail_optim_list {fruntime:foreign_runtime} : list (string * (nraenv -> nraenv)) :=
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

  Definition tail_optim {fruntime:foreign_runtime} {logger:optimizer_logger string nraenv} (name:string) : nraenv -> nraenv :=
    apply_steps ("tail" ++ name)  tail_optim_list.

  Lemma tail_optim_correctness {model:basic_model}  {logger:optimizer_logger string nraenv} (name:string) (p:nraenv) :
    p ⇒ₓ tail_optim name p.
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

  Definition optim1 {fruntime:foreign_runtime} {logger:optimizer_logger string nraenv} (p: nraenv) :=
    tnraenv_map_deep (head_optim "1") p.

  Lemma optim1_correctness {model:basic_model} {logger:optimizer_logger string nraenv} (p:nraenv) :
    p ⇒ₓ optim1 p.
  Proof.
    unfold optim1.
    assert (p ⇒ₓ tnraenv_map_deep (head_optim "1") p).
    apply nraenv_map_deep_correctness.
    intro p'.
    rewrite head_optim_correctness at 1.
    reflexivity.
    assumption.
  Qed.

  Definition optim2 {fruntime:foreign_runtime} {logger:optimizer_logger string nraenv} (p: nraenv) :=
    tnraenv_map_deep (tail_optim "") p.

  Lemma optim2_correctness {model:basic_model} {logger:optimizer_logger string nraenv} (p:nraenv) :
    p ⇒ₓ optim2 p.
  Proof.
    unfold optim2.
    assert (p ⇒ₓ tnraenv_map_deep (tail_optim "") p).
    apply nraenv_map_deep_correctness.
    intro p'.
    rewrite tail_optim_correctness at 1.
    reflexivity.
    assumption.
  Qed.

  Definition toptim_nraenv {fruntime:foreign_runtime} {logger:optimizer_logger string nraenv} (p:nraenv) :=
    let pass1p := (optim_size (optim_iter optim1 5) p) in
    (optim_size (optim_iter optim2 15) pass1p).

  Lemma toptim_nraenv_correctness {model:basic_model} {logger:optimizer_logger string nraenv} p:
    p ⇒ₓ toptim_nraenv p.
  Proof.
    unfold toptim_nraenv.
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

End NRAEnvOptimFunc.

(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
