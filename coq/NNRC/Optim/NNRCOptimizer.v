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
Require Import ListSet.
Require Import Arith.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import cNNRCSystem.
Require Import NNRCSystem.
Require Import NNRCRewriteUtil.
Require Import NNRCRewrite.
Require Import TNNRCRewrite.
Require Import OptimizerLogger.
Require Import OptimizerStep.

Section NNRCOptimizer.
  Local Open Scope nnrc_scope.
  Local Open Scope string.

  Section engine.
    (** Apply the function f to the direct child of p *)
    Context {fruntime:foreign_runtime}.

    Definition nnrc_map (f: nnrc -> nnrc) (e:nnrc) :=
      match e with
      | NNRCGetConstant v => NNRCGetConstant v
      | NNRCVar v => NNRCVar v
      | NNRCConst d => NNRCConst d
      | NNRCBinop bop e1 e2 => NNRCBinop bop (f e1) (f e2)
      | NNRCUnop uop e1 => NNRCUnop uop (f e1)
      | NNRCLet v e1 e2 => NNRCLet v (f e1) (f e2)
      | NNRCFor v e1 e2 => NNRCFor v (f e1) (f e2)
      | NNRCIf e1 e2 e3 => NNRCIf (f e1) (f e2) (f e3)
      | NNRCEither ed xl el xr er => NNRCEither (f ed) xl (f el) xr (f er)
      | NNRCGroupBy g sl e1 => NNRCGroupBy g sl (f e1)
      end.

    Lemma nnrc_map_correctness:
      forall f: nnrc -> nnrc,
      forall e: nnrc,
        (forall e', nnrc_eq (f e') e') -> nnrc_eq (nnrc_map f e) e.
    Proof.
      intros f e Hf.
      nnrc_cases (induction e) Case;
        try solve [simpl; repeat rewrite Hf; reflexivity].
    Qed.

    (** Apply the function f to all subexpression of e. *)
    Fixpoint nnrc_map_deep (f: nnrc -> nnrc) (e: nnrc) :=
      match e with
      | NNRCGetConstant v => f (NNRCGetConstant v)
      | NNRCVar v => f (NNRCVar v)
      | NNRCConst d => f (NNRCConst d)
      | NNRCBinop bop e1 e2 => f (NNRCBinop bop (nnrc_map_deep f e1) (nnrc_map_deep f e2))
      | NNRCUnop uop e1 => f (NNRCUnop uop (nnrc_map_deep f e1))
      | NNRCLet v e1 e2 => f (NNRCLet v (nnrc_map_deep f e1) (nnrc_map_deep f e2))
      | NNRCFor v e1 e2 => f (NNRCFor v (nnrc_map_deep f e1) (nnrc_map_deep f e2))
      | NNRCIf e1 e2 e3 => f (NNRCIf (nnrc_map_deep f e1) (nnrc_map_deep f e2) (nnrc_map_deep f e3))
      | NNRCEither ed xl el xr er => f (NNRCEither (nnrc_map_deep f ed) xl (nnrc_map_deep f  el) xr (nnrc_map_deep f er))
      | NNRCGroupBy g sl e1 => f (NNRCGroupBy g sl (nnrc_map_deep f e1))
      end.

    Lemma nnrc_map_deep_corretness:
      forall f: nnrc -> nnrc,
      forall e: nnrc,
        (forall e', nnrc_eq (f e') e') -> nnrc_eq (nnrc_map_deep f e) e.
    Proof.
      intros f e Hf.
      nnrc_cases (induction e) Case; simpl;
        try solve [repeat rewrite Hf; reflexivity];
        try solve [repeat rewrite Hf; rewrite IHe; reflexivity ];
        try solve [repeat rewrite Hf; rewrite IHe1; rewrite IHe2; reflexivity ];
        try solve [repeat rewrite Hf; rewrite IHe1; rewrite IHe2; rewrite IHe3; reflexivity ].
    Qed.

    (* Java equivalent: NnrcOptimizer.rew_iter *)
    (*  Definition rew_iter (rew: nnrc -> nnrc) (fuel: nat) (p: nnrc)
    := iter rew fuel p.
     *)
    (* Java equivalent: NnrcOptimizer.rew_size *)
    (* Definition rew_size (rew: nnrc -> nnrc) (p: nnrc) :=
    iter_cost rew NNRCSize.nnrc_size p.
     *)
    (* *************************** *)

    (* unshadowing *)

    Definition nunshadow := unshadow_simpl nil.
  
    (* *************************** *)
    Definition head_rew (e: nnrc) :=
      (nunshadow e).
    
    Lemma head_rew_correctness e:
      nnrc_eq (head_rew e) e.
    Proof.
      unfold head_rew.
    apply nnrc_unshadow_preserves.
    Qed.

    Lemma rewriter_simpl_rew_no_free_var :
      forall (op : nnrc) (x : var),
        In x (nnrc_free_vars (head_rew op)) -> In x (nnrc_free_vars op).
    Proof.
      intros.
      unfold head_rew in H.
      eapply unshadow_free_vars; eapply H.
    Qed.
    (* *************************** *)

  End engine.

  Ltac tcorrectness_prover :=
    simpl; repeat progress
                  (try match goal with
                       | [|- context [match ?p with | _ => _ end] ] => destruct p
                       end; try reflexivity; try unfold Equivalence.equiv in *; try subst).
  
  Ltac tprove_correctness p :=
    destruct p;
    tcorrectness_prover.

  Lemma tnnrc_rewrites_to_trans {model:basic_model} e1 e2 e3:
    tnnrc_rewrites_to e1 e2 -> tnnrc_rewrites_to e2 e3 -> tnnrc_rewrites_to e1 e3.
  Proof.
    apply transitivity.
  Qed.

  Lemma AUX {model:basic_model} f e e' :
    (forall e, tnnrc_rewrites_to e (f e)) -> tnnrc_rewrites_to e e' -> tnnrc_rewrites_to e (f e').
  Proof.
    intros.
    rewrite H0 at 1.
    rewrite (H e') at 1.
    reflexivity.
  Qed.

  Definition tnnrc_map {fruntime:foreign_runtime} := nnrc_map.

  Lemma tnnrc_map_correctness {model:basic_model}:
    forall f: nnrc -> nnrc,
    forall p: nnrc,
      (forall p', tnnrc_rewrites_to p' (f p')) -> tnnrc_rewrites_to p (tnnrc_map f p).
  Proof.
    intros.
    nnrc_cases (induction p) Case; try solve [simpl; apply Hf]; simpl;
    try reflexivity;
    try (rewrite (H p1) at 1; rewrite (H p2) at 1; reflexivity).
    rewrite (H p) at 1; reflexivity.
    simpl.
    rewrite (H p1) at 1; rewrite (H p2) at 1; rewrite (H p3) at 1.
    reflexivity.
    rewrite (H p1) at 1; rewrite (H p2) at 1; rewrite (H p3) at 1.
    reflexivity.
    rewrite (H p) at 1; reflexivity.
  Qed.

  Definition tnnrc_map_deep {fruntime:foreign_runtime} := nnrc_map_deep.
  Lemma tnnrc_map_deep_correctness {model:basic_model}:
    forall f: nnrc -> nnrc,
    forall p: nnrc,
      (forall p', tnnrc_rewrites_to p' (f p')) -> tnnrc_rewrites_to p (tnnrc_map_deep f p).
  Proof.
    intros f p Hf.
    nnrc_cases (induction p) Case; try solve [simpl; apply Hf];
    try reflexivity; simpl;
    try (rewrite IHp1 at 1; rewrite IHp2 at 1; rewrite Hf at 1; reflexivity);
    try (rewrite IHp at 1; rewrite Hf at 1; reflexivity).
    rewrite IHp1 at 1; rewrite IHp2 at 1; rewrite IHp3 at 1; rewrite Hf at 1; reflexivity.
    rewrite IHp1 at 1; rewrite IHp2 at 1; rewrite IHp3 at 1; rewrite Hf at 1; reflexivity.
  Qed.

  (****************)
      
  (* Java equivalent: NnrcOptimizer.tunshadow_preserves_fun *)
  Definition tunshadow_preserves_fun {fruntime:foreign_runtime} (e:nnrc) :=
    unshadow_simpl nil e.

  Lemma tunshadow_preserves_fun_correctness {model:basic_model} (e:nnrc):
    tnnrc_rewrites_to e (tunshadow_preserves_fun e).
  Proof.
    unfold tunshadow_preserves_fun, unshadow_simpl.
    apply tunshadow_preserves_arrow.
  Qed.

  Definition tunshadow_preserves_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "unshadow" (* name *)
         "Renames variables to avoid shadowing" (* description *)
         "tunshadow_preserves_fun" (* lemma name *)
         tunshadow_preserves_fun (* lemma *).

  Definition tunshadow_preserves_step_correct {model:basic_model}
    := mkOptimizerStepModel tunshadow_preserves_step tunshadow_preserves_fun_correctness.

  
  Definition tconcat_nil_fun  {fruntime:foreign_runtime}(e:nnrc) :=
    match e with
    | NNRCBinop OpRecConcat (NNRCConst (drec nil)) ee => ee
    | NNRCBinop OpRecConcat ee (NNRCConst (drec nil)) => ee
    | _ => e
    end.
  
  Lemma tconcat_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tconcat_nil_fun e).
  Proof.
    destruct e; simpl; try reflexivity.
    destruct b; simpl; try reflexivity.
    destruct (e1 == (‵[||])).
    - rewrite e.
      apply tconcat_of_nil_l_arrow.
    - destruct (e2 == (‵[||])).
      + repeat rewrite e.
        rewrite tconcat_of_nil_r_arrow.
        repeat (match_destr; try reflexivity).
      + repeat (match_destr; try reflexivity; try congruence).
  Qed.

  Definition tconcat_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "concat/nil" (* name *)
         "Remove record concatenation with an empty bag" (* description *)
         "tconcat_nil_fun" (* lemma name *)
         tconcat_nil_fun (* lemma *).

  Definition tconcat_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tconcat_nil_step tconcat_nil_fun_correctness.

  Definition tmerge_nil_fun  {fruntime:foreign_runtime}(e:nnrc) :=
    match e with
    | NNRCBinop OpRecMerge (NNRCConst (drec nil)) ee => NNRCUnop OpBag ee
    | NNRCBinop OpRecMerge ee (NNRCConst (drec nil)) => NNRCUnop OpBag ee
    | _ => e
    end.
  
  Lemma tmerge_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tmerge_nil_fun e).
  Proof.
    destruct e; simpl; try reflexivity.
    destruct b; simpl; try reflexivity.
    destruct (e1 == (‵[||])).
    - rewrite e.
      apply tmerge_of_nil_l_arrow.
    - destruct (e2 == (‵[||])).
      + repeat rewrite e.
        rewrite tmerge_of_nil_r_arrow.
        repeat (match_destr; try reflexivity).
      + repeat (match_destr; try reflexivity; try congruence).
  Qed.

  Definition tmerge_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "merge/nil" (* name *)
         "Remove record merge with an empty bag" (* description *)
         "tmerge_nil_fun" (* lemma name *)
         tmerge_nil_fun (* lemma *).

  Definition tmerge_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tmerge_nil_step tmerge_nil_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tfor_nil_fun  {fruntime:foreign_runtime}(e:nnrc) :=
    match e with
    | NNRCFor x ‵{||} e2 => ‵{||}
    | _ => e
    end.
  
  Lemma tfor_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tfor_nil_fun e).
  Proof.
    tprove_correctness e.
    apply tfor_nil_arrow.
  Qed.

  Definition tfor_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "for/nil" (* name *)
         "Remove loop comprehensions over empty bags" (* description *)
         "tfor_nil_fun" (* lemma name *)
         tfor_nil_fun (* lemma *).

  Definition tfor_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tfor_nil_step tfor_nil_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tfor_singleton_to_let_fun  {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
    | NNRCFor x (NNRCUnop OpBag e1) e2
      => NNRCUnop OpBag (NNRCLet x e1 e2)
    | _ => e
    end.

  Lemma tfor_singleton_to_let_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tfor_singleton_to_let_fun e).
  Proof.
    tprove_correctness e.
    apply tfor_singleton_to_let_arrow.
  Qed.

  Definition tfor_singleton_to_let_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "for/singleton" (* name *)
         "Lower a loop comprehension over a singleton into a singleton of a let" (* description *)
         "tfor_singleton_to_let_step" (* lemma name *)
         tfor_singleton_to_let_fun (* lemma *).
  
  Definition tfor_singleton_to_let_step_correct {model:basic_model}
    := mkOptimizerStepModel tfor_singleton_to_let_step tfor_singleton_to_let_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tflatten_singleton_fun  {fruntime:foreign_runtime} (e:nnrc)
    := match e with
       | ♯flatten(‵{| e1 |}) => e1
       | _ => e
       end.

  Lemma tflatten_singleton_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tflatten_singleton_fun e).
  Proof.
    tprove_correctness e.
    apply tflatten_singleton_nnrc_arrow.
  Qed.

  Definition tflatten_singleton_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/singleton" (* name *)
         "Simplify a flatten of a singleton bag" (* description *)
         "tflatten_singleton_fun" (* lemma name *)
         tflatten_singleton_fun (* lemma *).
  
  Definition tflatten_singleton_step_correct {model:basic_model}
    := mkOptimizerStepModel tflatten_singleton_step tflatten_singleton_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tflatten_nil_fun  {fruntime:foreign_runtime} (e:nnrc)
    := match e with
       | ♯flatten(‵{||}) => ‵{||}
       | _ => e
       end.

  Lemma tflatten_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tflatten_nil_fun e).
  Proof.
    tprove_correctness e.
    apply tflatten_nil_nnrc_arrow.
  Qed.

  Definition tflatten_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "flatten/nil" (* name *)
         "Simplify flatten of an empty bag" (* description *)
         "tflatten_nil_fun" (* lemma name *)
         tflatten_nil_fun (* lemma *).
  
  Definition tflatten_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tflatten_nil_step tflatten_nil_fun_correctness.

  Definition tsigma_to_if_fun  {fruntime:foreign_runtime}(e:nnrc) :=
    match e with
      | (NNRCUnop OpFlatten
                 (NNRCFor v1 (NNRCUnop OpBag e2)
                         (NNRCIf e1
                                (NNRCUnop OpBag (NNRCVar v2))
                                (NNRCConst (dcoll nil))))) =>
        if (v1 == v2)
        then (NNRCLet v1 e2 (NNRCIf e1 (NNRCUnop OpBag (NNRCVar v1)) (NNRCConst (dcoll nil))))
        else e
      | _ => e
    end.

  (* ♯flatten({ e1 ? { $t1 } : {} | $t1 ∈ { e2 } }) ≡ LET $t1 := e2 IN e1 ? { $t1 } : {} *)

  Lemma tsigma_to_if_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tsigma_to_if_fun e).
  Proof.
    tprove_correctness e.
    apply tsigma_to_if_arrow.
  Qed.

  Definition tsigma_to_if_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "sigma/if" (* name *)
         "???" (* description *)
         "tsigma_to_if_fun" (* lemma name *)
         tsigma_to_if_fun (* lemma *).

  Definition tsigma_to_if_step_correct {model:basic_model}
    := mkOptimizerStepModel tsigma_to_if_step tsigma_to_if_fun_correctness.
  
  (* {| e3 | $t2 ∈ ♯flatten({| e2 ? ‵{|$t1|} : ‵{||} | $t1 ∈ e1 |}) |}
       ⇒ ♯flatten({| e2 ? ‵{| LET $t2 := $t1 IN e3 ]|} : ‵{||} | $t1 ∈ e1 |}) *)

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tmap_sigma_fusion_samevar_fun  {fruntime:foreign_runtime}(e:nnrc) :=
    match e with
      | (NNRCFor v2 
                (NNRCUnop OpFlatten
                         (NNRCFor v1 e1
                                 (NNRCIf e2 (NNRCUnop OpBag ee) (NNRCConst (dcoll nil)))))
                e3) =>
          if (v1 == v2)
          then
            (NNRCUnop OpFlatten
                     (NNRCFor v1 e1
                             (NNRCIf e2
                                    (NNRCUnop OpBag (NNRCLet v1 ee e3))
                                    (NNRCConst (dcoll nil)))))
        else e
      | _ => e
    end.

  Lemma tmap_sigma_fusion_samevar_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tmap_sigma_fusion_samevar_fun e).
  Proof.
    tprove_correctness e.
    apply tmap_sigma_fusion_samevar_arrow.
  Qed.

    Definition tmap_sigma_fusion_samevar_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "sigma/same var fusion" (* name *)
         "???" (* description *)
         "tmap_sigma_fusion_samevar_fun" (* lemma name *)
         tmap_sigma_fusion_samevar_fun (* lemma *).

  Definition tmap_sigma_fusion_samevar_step_correct {model:basic_model}
    := mkOptimizerStepModel tmap_sigma_fusion_samevar_step tmap_sigma_fusion_samevar_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tdot_of_rec_fun  {fruntime:foreign_runtime}(e:nnrc) :=
    match e with
      | (NNRCUnop (OpDot s1)
                (NNRCUnop (OpRec s2) e1)) =>
        if (s1 == s2)
        then e1
        else e
      | _ => e
    end.

  Lemma tdot_of_rec_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tdot_of_rec_fun e).
  Proof.
    tprove_correctness e.
    apply tdot_of_rec.
  Qed.

    Definition tdot_of_rec_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "dot/rec" (* name *)
         "Simplify lookup of a new record constructor" (* description *)
         "tdot_of_rec_fun" (* lemma name *)
         tdot_of_rec_fun (* lemma *).

  Definition tdot_of_rec_step_correct {model:basic_model}
    := mkOptimizerStepModel tdot_of_rec_step tdot_of_rec_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tmerge_concat_to_concat_fun  {fruntime:foreign_runtime}(e:nnrc)
    := match e with
       | (‵[| (s1, p1)|] ⊗ ‵[| (s2, p2)|])
         => if (equiv_decb s1 s2)
            then e
            else (‵{|‵[| (s1, p1)|] ⊕ ‵[| (s2, p2)|]|})
       | _ => e
       end.

  Lemma tmerge_concat_to_concat_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tmerge_concat_to_concat_fun e).
  Proof.
    destruct e; simpl; try reflexivity.
    destruct b; simpl; try reflexivity.
    destruct e1; simpl; try reflexivity.
    destruct u; simpl; try reflexivity.
    destruct e2; simpl; try reflexivity.
    destruct u; simpl; try reflexivity.
    unfold equiv_decb.
    destruct (equiv_dec s s0); try reflexivity.
    apply tnnrc_merge_concat_to_concat_arrow; trivial.
  Qed.

    Definition tmerge_concat_to_concat_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "merge-concat->merge" (* name *)
         "Simplify a merge-concat of two singleton records with different fields using concat" (* description *)
         "tmerge_concat_to_concat_fun" (* lemma name *)
         tmerge_concat_to_concat_fun (* lemma *).

  Definition tmerge_concat_to_concat_step_correct {model:basic_model}
    := mkOptimizerStepModel tmerge_concat_to_concat_step tmerge_concat_to_concat_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tdot_of_concat_rec_fun  {fruntime:foreign_runtime}(e:nnrc)
    := match e with
       | (NNRCUnop (OpDot s) (NNRCBinop OpRecConcat e1 (NNRCUnop (OpRec s2) e2)))
         => if equiv_decb s s2
            then e2
            else (NNRCUnop (OpDot s) e1)
       | _ => e
       end.

  Lemma tdot_of_concat_rec_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tdot_of_concat_rec_fun e).
  Proof.
    destruct e; simpl; try reflexivity.
    destruct u; simpl; try reflexivity.
    destruct e; simpl; try reflexivity.
    destruct b; simpl; try reflexivity.
    destruct e2; simpl; try reflexivity.
    destruct u; simpl; try reflexivity.
    unfold equiv_decb.
    destruct (equiv_dec s s0); try reflexivity.
    - red in e; subst.
      apply tnnrc_dot_of_concat_rec_eq_arrow.
    - apply tnnrc_dot_of_concat_rec_neq_arrow.
      trivial.
  Qed.

    Definition tdot_of_concat_rec_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "dot/concat/rec 2" (* name *)
         "Simplifies lookup of a concatenation with a record constructor" (* description *)
         "tdot_of_concat_rec_fun" (* lemma name *)
         tdot_of_concat_rec_fun (* lemma *).

  Definition tdot_of_concat_rec_step_correct {model:basic_model}
    := mkOptimizerStepModel tdot_of_concat_rec_step tdot_of_concat_rec_fun_correctness.

  (** Inlining *)

  (* TODO: A better/less hacky cost function.  This will probably need many more real
     examples to tune with, as it will always contain some black-magic. *)
  (* Java equivalent: NnrcOptimizer.is_small_unop *)
  Definition is_small_unop {fruntime:foreign_runtime} (u:unary_op) :=
    match u with
    | OpIdentity
    | OpNeg
    | OpBag
    | OpLeft
    | OpRight
    | OpBrand _
    | OpRec _
      => true
    | _ => false
    end.
  
  (* Java equivalent: NnrcOptimizer.should_inline_small *)
  Fixpoint should_inline_small {fruntime:foreign_runtime} (from:nnrc)
    := match from with
       | NNRCVar _
       | NNRCConst _ => true
       | NNRCUnop u e => is_small_unop u && should_inline_small e
       | NNRCBinop OpRecConcat (NNRCUnop (OpRec _) e1) (NNRCUnop (OpRec _) e2) => true
       | _ => false
       end.

  (* Java equivalent: NnrcOptimizer.should_inline_few_occurances *)
  Definition should_inline_few_occurences {fruntime:foreign_runtime} (x:var) (to:nnrc)
    := match use_count x to with
       | NotUsed
       | UsedOnce => true
       | _ => false
       end.
  
  (* Java equivalent: NnrcOptimizer.should_inline *)
  Definition should_inline {fruntime:foreign_runtime} (x:var) (from to:nnrc)
    := should_inline_small from
       || should_inline_few_occurences x to.
  
  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tinline_let_fun  {fruntime:foreign_runtime}(e:nnrc)
    := match e with
       | NNRCLet x e1 e2 =>
         if should_inline x e1 e2
         then nnrc_subst (unshadow_simpl (nnrc_free_vars e1) e2) x e1
         else e
       | _ => e
       end.

  Lemma tinline_let_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tinline_let_fun e).
  Proof.
    tprove_correctness e.
    apply tlet_inline_arrow.
  Qed.

    Definition tinline_let_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "let inline" (* name *)
         "Inline let statements heuristically deemed suitable for inlining" (* description *)
         "tinline_let_fun" (* lemma name *)
         tinline_let_fun (* lemma *).

  Definition tinline_let_step_correct {model:basic_model}
    := mkOptimizerStepModel tinline_let_step tinline_let_fun_correctness.


  (* push map through either and if *)
  (* Java equivalent: NnrcOptimizer.[same] *)
    Definition tfor_over_if_nil_fun  {fruntime:foreign_runtime}(e:nnrc)
      := match e with
         | NNRCFor x (NNRCIf e1 e2 ‵{||}) ebody =>
                     (NNRCIf e1 (NNRCFor x e2 ebody) ‵{||})
       | _ => e
       end.

  Lemma tfor_over_if_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tfor_over_if_nil_fun e).
  Proof.
    tprove_correctness e.
    rewrite tfor_over_if_arrow; simpl.
    rewrite tfor_nil_arrow.
    reflexivity.
  Qed.

    Definition tfor_over_if_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "for/if/else nil" (* name *)
         "Push loop comprehension over an if statement through the if statement when the else clause just constructs an empty bag" (* description *)
         "tfor_over_if_nil_fun" (* lemma name *)
         tfor_over_if_nil_fun (* lemma *).

  Definition tfor_over_if_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tfor_over_if_nil_step tfor_over_if_nil_fun_correctness.

  (* for (map) fusion *)
    Definition tfor_over_for_fun  {fruntime:foreign_runtime}(e:nnrc)
      := match e with
         | NNRCFor x (NNRCFor y source body1) body2 =>
           if (in_dec string_dec y (nnrc_free_vars body2))
           then let fr := really_fresh_in 
                     nnrc_unshadow_sep y (nnrc_free_vars body1 ++ nnrc_bound_vars body1) body2
                in NNRCFor fr source
                     (NNRCLet x (nnrc_subst body1 y (NNRCVar fr)) body2)
           else NNRCFor y source
                        (NNRCLet x body1 body2)
       | _ => e
       end.

  Lemma tfor_over_for_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tfor_over_for_fun e).
  Proof.
    tprove_correctness e.
    - rewrite <- tfor_over_for_arrow; simpl; trivial.
      + apply tproper_NNRCFor; try reflexivity.
        generalize (really_fresh_from_avoid nnrc_unshadow_sep v0 (nnrc_free_vars e1_2 ++ nnrc_bound_vars e1_2) e2)
        ; rewrite in_app_iff; intros inn.
         apply tnnrcfor_rename_arrow; tauto.
      + apply really_fresh_from_free.
    - apply tfor_over_for_arrow; simpl; trivial.
  Qed.

    Definition tfor_over_for_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "for/for" (* name *)
         "Fuse nested loop comprehensions" (* description *)
         "tfor_over_for_fun" (* lemma name *)
         tfor_over_for_fun (* lemma *).

  Definition tfor_over_for_step_correct {model:basic_model}
    := mkOptimizerStepModel tfor_over_for_step tfor_over_for_fun_correctness.

(* END *)  
  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tfor_over_either_nil_fun  {fruntime:foreign_runtime} (e:nnrc)
    := match e with
       |  (NNRCFor x (NNRCEither e1 xl el xr ‵{||}) ebody)
          => 
            (    let xl' := really_fresh_in nnrc_unshadow_sep xl (nnrc_free_vars el ++ nnrc_bound_vars el) ebody in
              (NNRCEither e1
                       xl' (NNRCFor x (nnrc_subst el xl (NNRCVar xl')) ebody)
                       xr ‵{||}))
       | _ => e
       end.

  Lemma tfor_over_either_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tfor_over_either_nil_fun e).
  Proof.
    tprove_correctness e.
    rewrite tfor_over_either_arrow; simpl.
    rewrite tfor_nil_arrow.
    rewrite tnnrceither_rename_r_arrow by intuition; simpl.
    reflexivity.
  Qed.

    Definition tfor_over_either_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "for/either/right nil" (* name *)
         "Push loop comprehension over an either statement through the either statement when the right clause just constructs an empty bag" (* description *)
         "tfor_over_either_nil_fun" (* lemma name *)
         tfor_over_either_nil_fun (* lemma *).

  Definition tfor_over_either_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tfor_over_either_nil_step tfor_over_either_nil_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tunop_over_either_const_fun  {fruntime:foreign_runtime}(e:nnrc)
    := match e with
       | NNRCUnop op (NNRCEither e1 xl el xr (NNRCConst d)) =>
         NNRCEither e1 xl (NNRCUnop op el) xr (NNRCUnop op (NNRCConst d))
       | _ => e
       end.

  Lemma tunop_over_either_const_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tunop_over_either_const_fun e).
  Proof.
    tprove_correctness e.
    apply tnnrcunop_over_either_arrow.
  Qed.

    Definition tunop_over_either_const_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "unary/either/right const" (* name *)
         "Push unary operators through either when the right branch is a constant" (* description *)
         "tunop_over_either_const_fun" (* lemma name *)
         tunop_over_either_const_fun (* lemma *).

  Definition tunop_over_either_const_step_correct {model:basic_model}
    := mkOptimizerStepModel tunop_over_either_const_step tunop_over_either_const_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tunop_over_if_const_fun  {fruntime:foreign_runtime}(e:nnrc)
    := match e with
       | NNRCUnop op (NNRCIf e1 e2 (NNRCConst d)) =>
         NNRCIf e1 (NNRCUnop op e2) (NNRCUnop op (NNRCConst d))
       | _ => e
       end.

  Lemma tunop_over_if_const_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tunop_over_if_const_fun e).
  Proof.
    tprove_correctness e.
    apply tnnrcunop_over_if_arrow.
  Qed.
  
  Definition tunop_over_if_const_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "unary/if/else const" (* name *)
         "Push unary operators through if when the else branch is a constant" (* description *)
         "tunop_over_if_const_fun" (* lemma name *)
         tunop_over_if_const_fun (* lemma *).

  Definition tunop_over_if_const_step_correct {model:basic_model}
    := mkOptimizerStepModel tunop_over_if_const_step tunop_over_if_const_fun_correctness.

    (* optimizations for rproject *)

  (* Java equivalent: NnrcOptimizer.[same] *)
   Definition tproject_nil_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (OpRecProject nil) e₁
        => NNRCConst (drec nil)
      | _ => e
    end.

  Definition tproject_nil_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tproject_nil_fun p.
  Proof.
    tprove_correctness p.
    apply tnnrcproject_nil.
  Qed.

  Hint Rewrite @tproject_nil_fun_correctness : toptim_correct.

    Definition tproject_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "project/nil" (* name *)
         "Simplify record projection over empty bags" (* description *)
         "tproject_nil_fun" (* lemma name *)
         tproject_nil_fun (* lemma *).

  Definition tproject_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tproject_nil_step tproject_nil_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tproject_over_const_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (OpRecProject sl)
          (NNRCConst (drec l))
        => NNRCConst (drec (rproject l sl))
      | _ => e
    end.

  Definition tproject_over_const_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tproject_over_const_fun p.
  Proof.
    tprove_correctness p.
    apply tnnrcproject_over_const.
  Qed.

  Hint Rewrite @tproject_over_const_fun_correctness : toptim_correct.
  
  Definition tproject_over_const_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "project/const rec" (* name *)
         "Simplify record projection over constant records" (* description *)
         "tproject_over_const_fun" (* lemma name *)
         tproject_over_const_fun (* lemma *).

  Definition tproject_over_const_step_correct {model:basic_model}
    := mkOptimizerStepModel tproject_over_const_step tproject_over_const_fun_correctness.
  
  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tproject_over_rec_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (OpRecProject sl)
          (NNRCUnop (OpRec s) p₁)
        => if in_dec string_dec s sl
           then NNRCUnop (OpRec s) p₁
           else ‵[||]
      | _ => e
    end.

  Definition tproject_over_rec_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tproject_over_rec_fun p.
  Proof.
    tprove_correctness p.
    - apply tnnrcproject_over_rec_in; trivial.
    - apply tnnrcproject_over_rec_nin; trivial. 
  Qed.

  Hint Rewrite @tproject_over_rec_fun_correctness : toptim_correct.

  Definition tproject_over_rec_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "project/rec" (* name *)
         "Simplify record projection over a record constructor" (* description *)
         "tproject_over_rec_fun" (* lemma name *)
         tproject_over_rec_fun (* lemma *).

  Definition tproject_over_rec_step_correct {model:basic_model}
    := mkOptimizerStepModel tproject_over_rec_step tproject_over_rec_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
   Definition tproject_over_concat_r_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (OpRecProject sl)
               (NNRCBinop OpRecConcat
                        p₁ (NNRCUnop (OpRec s) p₂))
        => if in_dec string_dec s sl
           then NNRCBinop OpRecConcat
                         (NNRCUnop (OpRecProject (remove string_dec s sl)) p₁)
                        (NNRCUnop (OpRec s) p₂)
           else (NNRCUnop (OpRecProject sl) p₁)
      | _ => e
    end.

  Definition tproject_over_concat_r_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tproject_over_concat_r_fun p.
  Proof.
    tprove_correctness p.
    - apply tnnrcproject_over_concat_rec_r_in; trivial.
    - apply tnnrcproject_over_concat_rec_r_nin; trivial.
  Qed.
                  
  Hint Rewrite @tproject_over_concat_r_fun_correctness : toptim_correct.

  Definition tproject_over_concat_r_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "project/concat/right rec" (* name *)
         "Simplify record projection over concatenation with a record constructor" (* description *)
         "tproject_over_concat_r_fun" (* lemma name *)
         tproject_over_concat_r_fun (* lemma *).

  Definition tproject_over_concat_r_step_correct {model:basic_model}
    := mkOptimizerStepModel tproject_over_concat_r_step tproject_over_concat_r_fun_correctness.
  
  (* Java equivalent: NnrcOptimizer.[same] *)
     Definition tproject_over_concat_l_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (OpRecProject sl)
               (NNRCBinop OpRecConcat
                        (NNRCUnop (OpRec s) p₁) p₂)
        => if in_dec string_dec s sl
                     (* this case would need shape/type inference to handle, since we don't know if s is in p₂ *)

           then e
           else (NNRCUnop (OpRecProject sl) p₂)
      | _ => e
    end.

  Definition tproject_over_concat_l_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tproject_over_concat_l_fun p.
  Proof.
    tprove_correctness p.
    apply tnnrcproject_over_concat_rec_l_nin; trivial.
  Qed.
                  
  Hint Rewrite @tproject_over_concat_l_fun_correctness : toptim_correct.

  Definition tproject_over_concat_l_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "project/concat/left rec" (* name *)
         "Simplify record projection over concatenation with a record constructor" (* description *)
         "tproject_over_concat_l_fun" (* lemma name *)
         tproject_over_concat_l_fun (* lemma *).

  Definition tproject_over_concat_l_step_correct {model:basic_model}
    := mkOptimizerStepModel tproject_over_concat_l_step tproject_over_concat_l_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tproject_over_project_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (OpRecProject sl1)
          (NNRCUnop (OpRecProject sl2) p1)
        => NNRCUnop (OpRecProject (set_inter string_dec sl2 sl1)) p1
      | _ => e
    end.

  Definition tproject_over_project_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tproject_over_project_fun p.
  Proof.
    tprove_correctness p.
    apply tnnrcproject_over_nnrcproject.
  Qed.

  Hint Rewrite @tproject_over_project_fun_correctness : toptim_correct.

  Definition tproject_over_project_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "project/project" (* name *)
         "Fuse nested record projections" (* description *)
         "tproject_over_project_fun" (* lemma name *)
         tproject_over_project_fun (* lemma *).

  Definition tproject_over_project_step_correct {model:basic_model}
    := mkOptimizerStepModel tproject_over_project_step tproject_over_project_fun_correctness.

  (* Java equivalent: NnrcOptimizer.[same] *)
   Definition tproject_over_either_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (OpRecProject sl)
          (NNRCEither p xl p₁ xr p₂)
        => NNRCEither p xl (NNRCUnop (OpRecProject sl) p₁) xr (NNRCUnop (OpRecProject sl) p₂)
      | _ => e
    end.

  Definition tproject_over_either_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tproject_over_either_fun p.
  Proof.
    tprove_correctness p.
    apply tnnrcproject_over_either.
  Qed.

  Hint Rewrite @tproject_over_either_fun_correctness : toptim_correct.

  Definition tproject_over_either_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "project/either/" (* name *)
         "Push record projection through either" (* description *)
         "tproject_over_either_fun" (* lemma name *)
         tproject_over_either_fun (* lemma *).

  Definition tproject_over_either_step_correct {model:basic_model}
    := mkOptimizerStepModel tproject_over_either_step tproject_over_either_fun_correctness.
  
  (* count optimizations *)
  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tcount_over_flat_for_either_if_nil_fun  {fruntime:foreign_runtime} (e:nnrc)
    := match e with
       | (♯count(♯flatten(NNRCFor v
                              ehead (NNRCEither e1 xl
                                               (NNRCIf e11(‵{| e12|}) ‵{||}) xr ‵{||}))))
         => (♯count(♯flatten(NNRCFor v
                              ehead (NNRCEither e1 xl
                                               (NNRCIf e11(‵{| ‵(dunit) |}) ‵{||}) xr ‵{||}))))
       | _ => e
       end.

  Lemma tcount_over_flat_for_either_if_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tcount_over_flat_for_either_if_nil_fun e).
  Proof.
    destruct e; simpl; try reflexivity.
    repeat (match_destr; try reflexivity).
    apply tcount_over_flat_for_either_if_nil_arrow.
  Qed.

  Definition tcount_over_flat_for_either_if_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "count/flatten/for/either/right if/else nil" (* name *)
         "Remove work that is not needed when only the bag count is needed" (* description *)
         "tcount_over_flat_for_either_if_nil_fun" (* lemma name *)
         tcount_over_flat_for_either_if_nil_fun (* lemma *).

  Definition tcount_over_flat_for_either_if_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tcount_over_flat_for_either_if_nil_step tcount_over_flat_for_either_if_nil_fun_correctness.
  
  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tcount_over_flat_for_either_either_nil_fun  {fruntime:foreign_runtime}(e:nnrc)
    := match e with
       | (♯count(♯flatten(NNRCFor v
                                 ehead (NNRCEither e1 xl
                                                  (NNRCEither e11 xll (‵{| e12|}) xrr ‵{||}) xr ‵{||}))))
         => (♯count(♯flatten(NNRCFor v
                                    ehead (NNRCEither e1 xl
                                                     (NNRCEither e11 xll (‵{| ‵(dunit) |}) xrr ‵{||}) xr ‵{||}))))

     | _ => e
       end.

  Lemma tcount_over_flat_for_either_either_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_rewrites_to e (tcount_over_flat_for_either_either_nil_fun e).
  Proof.
    destruct e; simpl; try reflexivity.
    repeat (match_destr; try reflexivity).
    apply tcount_over_flat_for_either_either_nil_arrow.
  Qed.

    Definition tcount_over_flat_for_either_either_nil_step {fruntime:foreign_runtime}
    := mkOptimizerStep
         "count/flatten/for/either/right either/right nil" (* name *)
         "Remove work that is not needed when only the bag count is needed" (* description *)
         "tcount_over_flat_for_either_either_nil_fun" (* lemma name *)
         tcount_over_flat_for_either_either_nil_fun (* lemma *).

  Definition tcount_over_flat_for_either_either_nil_step_correct {model:basic_model}
    := mkOptimizerStepModel tcount_over_flat_for_either_either_nil_step tcount_over_flat_for_either_either_nil_fun_correctness.  
                                                            
  (* list of all optimizations *)
    Definition tnnrc_optim_list {fruntime:foreign_runtime} : list (@OptimizerStep nnrc)
      := [
          tconcat_nil_step
          ; tmerge_nil_step
          ; tfor_nil_step
          ; tfor_singleton_to_let_step
          ; tflatten_singleton_step
          ; tflatten_nil_step
          ; tsigma_to_if_step
          ; tmap_sigma_fusion_samevar_step
          ; tdot_of_rec_step
          ; tmerge_concat_to_concat_step
          ; tdot_of_concat_rec_step
          ; tinline_let_step
          ; tfor_over_if_nil_step
          ; tfor_over_for_step
          ; tfor_over_either_nil_step
          ; tunop_over_either_const_step
          ; tunop_over_if_const_step
          ; tproject_nil_step
          ; tproject_over_const_step
          ; tproject_over_rec_step
          ; tproject_over_concat_r_step
          ; tproject_over_concat_l_step
          ; tproject_over_project_step
          ; tproject_over_either_step
          ; tcount_over_flat_for_either_if_nil_step
          ; tcount_over_flat_for_either_either_nil_step
        ].

    Definition tnnrc_optim_model_list {model:basic_model} : list (OptimizerStepModel tnnrc_rewrites_to)
      := [
          tconcat_nil_step_correct
          ; tmerge_nil_step_correct
          ; tfor_nil_step_correct
          ; tfor_singleton_to_let_step_correct
          ; tflatten_singleton_step_correct
          ; tflatten_nil_step_correct
          ; tsigma_to_if_step_correct
          ; tmap_sigma_fusion_samevar_step_correct
          ; tdot_of_rec_step_correct
          ; tmerge_concat_to_concat_step_correct
          ; tdot_of_concat_rec_step_correct
          ; tinline_let_step_correct
          ; tfor_over_if_nil_step_correct
          ; tfor_over_for_step_correct
          ; tfor_over_either_nil_step_correct
          ; tunop_over_either_const_step_correct
          ; tunop_over_if_const_step_correct
          ; tproject_nil_step_correct
          ; tproject_over_const_step_correct
          ; tproject_over_rec_step_correct
          ; tproject_over_concat_r_step_correct
          ; tproject_over_concat_l_step_correct
          ; tproject_over_project_step_correct
          ; tproject_over_either_step_correct
          ; tcount_over_flat_for_either_if_nil_step_correct
          ; tcount_over_flat_for_either_either_nil_step_correct
        ].

  Lemma tnnrc_optim_model_list_complete {model:basic_model}
    : optim_model_list_complete tnnrc_optim_list tnnrc_optim_model_list.
  Proof.
    optim_correct_list_complete_prover.
  Qed.

  Definition tnnrc_optim_list_correct {model:basic_model}
    : optim_list_correct tnnrc_rewrites_to tnnrc_optim_list
    := optim_list_correct_from_model tnnrc_optim_model_list_complete.

  Lemma tnnrc_optim_list_distinct {fruntime:foreign_runtime}:
    optim_list_distinct tnnrc_optim_list.
  Proof.
    apply optim_list_distinct_prover.
    vm_compute.
    apply eq_refl.
  Qed.

  (* *************************** *)
  Definition run_nnrc_optims 
             {fruntime:foreign_runtime}
             {logger:optimizer_logger string nnrc}
             (opc:optim_phases_config)
    : nnrc -> nnrc :=
    run_phases tnnrc_map_deep NNRCSize.nnrc_size tnnrc_optim_list opc.

  Lemma run_nnrc_optims_correctness
        {model:basic_model} {logger:optimizer_logger string nnrc}
        (opc:optim_phases_config)
        (p:nnrc) :
    tnnrc_rewrites_to p (run_nnrc_optims opc p).
  Proof.
    unfold run_nnrc_optims.
    apply run_phases_correctness.
    - intros. apply tnnrc_map_deep_correctness; auto.
    - apply tnnrc_optim_list_correct.
  Qed.

  Section default.
  
    (* Java equivalent: NnrcOptimizer.head_rew_list *)
    Definition nnrc_default_optim_list {fruntime:foreign_runtime} : list string
    := [
        optim_step_name tinline_let_step
        ; optim_step_name tcount_over_flat_for_either_either_nil_step
        ; optim_step_name tcount_over_flat_for_either_if_nil_step
        ; optim_step_name tmerge_concat_to_concat_step
        ; optim_step_name tdot_of_concat_rec_step
        ; optim_step_name tdot_of_rec_step
        ; optim_step_name tflatten_singleton_step
        ; optim_step_name tflatten_nil_step
        ; optim_step_name tfor_singleton_to_let_step
        ; optim_step_name tunop_over_either_const_step
        ; optim_step_name tunop_over_if_const_step
        ; optim_step_name tfor_over_either_nil_step
        ; optim_step_name tfor_over_for_step
        ; optim_step_name tfor_over_if_nil_step
        ; optim_step_name tfor_nil_step
        ; optim_step_name tmerge_nil_step
        ; optim_step_name tconcat_nil_step
        ; optim_step_name tmap_sigma_fusion_samevar_step
        ; optim_step_name tproject_nil_step
        ; optim_step_name tproject_over_const_step
        ; optim_step_name tproject_over_rec_step
        ; optim_step_name tproject_over_concat_r_step
        ; optim_step_name tproject_over_concat_l_step
        ; optim_step_name tproject_over_project_step
        ; optim_step_name tproject_over_either_step
      ].
    
    Remark nnrc_default_optim_list_all_valid {fruntime:foreign_runtime}
      : valid_optims tnnrc_optim_list nnrc_default_optim_list = (nnrc_default_optim_list,nil).
    Proof.
      vm_compute; trivial.
    Qed.
  
    Definition default_nnrc_optim_phases {fruntime:foreign_runtime} :=
      ("[nnrc] default"%string,nnrc_default_optim_list,10)::nil.

  End default.
  
  (* Java equivalent: NnrcOptimizer.trew *)
  Definition run_nnrc_optims_default
             {fruntime:foreign_runtime} {logger:optimizer_logger string nnrc}
    := run_nnrc_optims default_nnrc_optim_phases.

  Lemma run_nnrc_optims_default_correct
        {model:basic_model} {logger:optimizer_logger string nnrc} p:
    tnnrc_rewrites_to p (run_nnrc_optims_default p).
  Proof.
    unfold run_nnrc_optims_default.
    apply run_nnrc_optims_correctness.
  Qed.

End NNRCOptimizer.

