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

Section TNNRCOptimizer.
  Require Import String.
  Require Import List ListSet.
  Require Import Arith.
  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.

  Require Import Utils BasicSystem.
  Require Import NNRCSystem.
  Require Import NNRCOptimizer.
  Require Import OptimizerLogger.

  Local Open Scope nnrc_scope.
  (* *************************** *)

    Ltac tcorrectness_prover :=
          simpl; repeat progress (try match goal with
        | [|- context [match ?p with | _ => _ end] ] => destruct p
      end; try reflexivity; try unfold Equivalence.equiv in *; try subst).

  Ltac tprove_correctness p :=
    destruct p;
    tcorrectness_prover.

  Lemma tnnrc_ext_rewrites_to_trans {model:basic_model} e1 e2 e3:
    tnnrc_ext_rewrites_to e1 e2 -> tnnrc_ext_rewrites_to e2 e3 -> tnnrc_ext_rewrites_to e1 e3.
  Proof.
    apply transitivity.
  Qed.

  Lemma AUX {model:basic_model} f e e' :
    (forall e, tnnrc_ext_rewrites_to e (f e)) -> tnnrc_ext_rewrites_to e e' -> tnnrc_ext_rewrites_to e (f e').
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
      (forall p', tnnrc_ext_rewrites_to p' (f p')) -> tnnrc_ext_rewrites_to p (tnnrc_map f p).
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

  Definition tnnrc_map_deep {fruntime:foreign_runtime} := NNRCOptimizer.nnrc_map_deep.
  Lemma tnnrc_map_deep_correctness {model:basic_model}:
    forall f: nnrc -> nnrc,
    forall p: nnrc,
      (forall p', tnnrc_ext_rewrites_to p' (f p')) -> tnnrc_ext_rewrites_to p (tnnrc_map_deep f p).
  Proof.
    intros f p Hf.
    nnrc_cases (induction p) Case; try solve [simpl; apply Hf];
    try reflexivity; simpl;
    try (rewrite IHp1 at 1; rewrite IHp2 at 1; rewrite Hf at 1; reflexivity);
    try (rewrite IHp at 1; rewrite Hf at 1; reflexivity).
    rewrite IHp1 at 1; rewrite IHp2 at 1; rewrite IHp3 at 1; rewrite Hf at 1; reflexivity.
    rewrite IHp1 at 1; rewrite IHp2 at 1; rewrite IHp3 at 1; rewrite Hf at 1; reflexivity.
  Qed.

  Lemma rew_iter_correctness {model:basic_model} rew n p:
    (forall p', tnnrc_ext_rewrites_to p' (rew p')) -> tnnrc_ext_rewrites_to p (rew_iter rew n p).
  Proof.
    generalize p; clear p.
    induction n; try reflexivity.
    intros p Hrew.
    simpl.
    apply AUX.
    - clear p; intros p.
      apply IHn.
      assumption.
    - apply Hrew.
  Qed.
  Hint Rewrite @rew_iter_correctness : rew_correct.

  Lemma rew_cost_correctness {model:basic_model} rew cost p:
    (forall p', tnnrc_ext_rewrites_to p' (rew p')) -> tnnrc_ext_rewrites_to p (rew_cost rew cost p).
  Proof.
    intros Hrew.
    functional induction rew_cost rew cost p.
    - apply (tnnrc_ext_rewrites_to_trans p (rew p)).
      + apply Hrew.
      + apply IHn.
    - reflexivity.
  Qed.
  Hint Rewrite @rew_cost_correctness : rew_correct.

  Lemma rew_size_correctness {model:basic_model} rew p:
    (forall p', tnnrc_ext_rewrites_to p' (rew p')) -> tnnrc_ext_rewrites_to p (rew_size rew p).
  Proof.
    intros Hrew.
    unfold rew_size.
    apply rew_cost_correctness.
    assumption.
  Qed.
  Hint Rewrite @rew_size_correctness : rew_correct.

  (****************)

  (* Java equivalent: NnrcOptimizer.tunshadow_preserves_fun *)
  Definition tunshadow_preserves_fun {fruntime:foreign_runtime} (e:nnrc) :=
    unshadow_simpl nil e.

  Lemma tunshadow_preserves_fun_correctness {model:basic_model} (e:nnrc):
    tnnrc_ext_rewrites_to e (tunshadow_preserves_fun e).
  Proof.
    unfold tunshadow_preserves_fun, unshadow_simpl.
    apply tunshadow_preserves_arrow.
  Qed.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tfor_nil_fun  {fruntime:foreign_runtime}(e:nnrc) :=
    match e with
    | NNRCFor x ‵{||} e2 => ‵{||}
    | _ => e
    end.

  Lemma tfor_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tfor_nil_fun e).
  Proof.
    tprove_correctness e.
    apply tfor_nil_arrow.
  Qed.
    
  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tfor_singleton_to_let_fun  {fruntime:foreign_runtime}(e:nnrc) :=
    match e with
    | NNRCFor x (NNRCUnop AColl e1) e2
      => NNRCUnop AColl (NNRCLet x e1 e2)
    | _ => e
    end.
  
  Lemma tfor_singleton_to_let_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tfor_singleton_to_let_fun e).
  Proof.
    tprove_correctness e.
    apply tfor_singleton_to_let_arrow.
  Qed.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tflatten_singleton_nnrc_fun  {fruntime:foreign_runtime}e
    := match e with
       | ♯flatten(‵{| e1 |}) => e1
       | _ => e
       end.

  Lemma tflatten_singleton_nnrc_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tflatten_singleton_nnrc_fun e).
  Proof.
    tprove_correctness e.
    apply tflatten_singleton_nnrc_arrow.
  Qed.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tflatten_nil_nnrc_fun  {fruntime:foreign_runtime}e
    := match e with
       | ♯flatten(‵{||}) => ‵{||}
       | _ => e
       end.

  Lemma tflatten_nil_nnrc_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tflatten_nil_nnrc_fun e).
  Proof.
    tprove_correctness e.
    apply tflatten_nil_nnrc_arrow.
  Qed.

  Definition tsigma_to_if_fun  {fruntime:foreign_runtime}(e:nnrc) :=
    match e with
      | (NNRCUnop AFlatten
                 (NNRCFor v1 (NNRCUnop AColl e2)
                         (NNRCIf e1
                                (NNRCUnop AColl (NNRCVar v2))
                                (NNRCConst (dcoll nil))))) =>
        if (v1 == v2)
        then (NNRCLet v1 e2 (NNRCIf e1 (NNRCUnop AColl (NNRCVar v1)) (NNRCConst (dcoll nil))))
        else e
      | _ => e
    end.

  (* ♯flatten({ e1 ? { $t1 } : {} | $t1 ∈ { e2 } }) ≡ LET $t1 := e2 IN e1 ? { $t1 } : {} *)

  Lemma tsigma_to_if_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tsigma_to_if_fun e).
  Proof.
    tprove_correctness e.
    apply tsigma_to_if_arrow.
  Qed.
  
  (* {| e3 | $t2 ∈ ♯flatten({| e2 ? ‵{|$t1|} : ‵{||} | $t1 ∈ e1 |}) |}
       ⇒ ♯flatten({| e2 ? ‵{| LET $t2 := $t1 IN e3 ]|} : ‵{||} | $t1 ∈ e1 |}) *)

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tmap_sigma_fusion_samevar_fun  {fruntime:foreign_runtime}(e:nnrc) :=
    match e with
      | (NNRCFor v2 
                (NNRCUnop AFlatten
                         (NNRCFor v1 e1
                                 (NNRCIf e2 (NNRCUnop AColl (NNRCVar v1')) (NNRCConst (dcoll nil)))))
                e3) =>
        if (v1 == v1')
        then
          if (v1 == v2)
          then
            (NNRCUnop AFlatten
                     (NNRCFor v1 e1
                             (NNRCIf e2
                                    (NNRCUnop AColl e3)
                                    (NNRCConst (dcoll nil)))))
          else e
        else e
      | _ => e
    end.

  Lemma tmap_sigma_fusion_samevar_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tmap_sigma_fusion_samevar_fun e).
  Proof.
    tprove_correctness e.
    apply tmap_sigma_fusion_samevar_arrow.
  Qed.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tdot_of_rec_fun  {fruntime:foreign_runtime}(e:nnrc) :=
    match e with
      | (NNRCUnop (ADot s1)
                (NNRCUnop (ARec s2) e1)) =>
        if (s1 == s2)
        then e1
        else e
      | _ => e
    end.

  Lemma tdot_of_rec_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tdot_of_rec_fun e).
  Proof.
    tprove_correctness e.
    apply tdot_of_rec.
  Qed.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tnnrc_merge_concat_to_concat_fun  {fruntime:foreign_runtime}(e:nnrc)
    := match e with
       | (‵[| (s1, p1)|] ⊗ ‵[| (s2, p2)|])
         => if (equiv_decb s1 s2)
            then e
            else (‵{|‵[| (s1, p1)|] ⊕ ‵[| (s2, p2)|]|})
       | _ => e
       end.

  Lemma tnnrc_merge_concat_to_concat_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tnnrc_merge_concat_to_concat_fun e).
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

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tnnrc_dot_of_concat_rec_fun  {fruntime:foreign_runtime}(e:nnrc)
    := match e with
       | (NNRCUnop (ADot s) (NNRCBinop AConcat e1 (NNRCUnop (ARec s2) e2)))
         => if equiv_decb s s2
            then e2
            else (NNRCUnop (ADot s) e1)
       | _ => e
       end.

  Lemma tnnrc_dot_of_concat_rec_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tnnrc_dot_of_concat_rec_fun e).
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

  (** Inlining *)

  (* TODO: A better/less hacky cost function.  This will probably need many more real
     examples to tune with, as it will always contain some black-magic. *)
  (* Java equivalent: NnrcOptimizer.is_small_unop *)
  Definition is_small_unop {fruntime:foreign_runtime} (u:unaryOp) :=
    match u with
    | AIdOp
    | ANeg
    | AColl
    | ALeft
    | ARight
    | ABrand _
    | ARec _
      => true
    | _ => false
    end.
  
  (* Java equivalent: NnrcOptimizer.should_inline_small *)
  Fixpoint should_inline_small {fruntime:foreign_runtime} (from:nnrc)
    := match from with
       | NNRCVar _
       | NNRCConst _ => true
       | NNRCUnop u e => is_small_unop u && should_inline_small e
       | NNRCBinop AConcat (NNRCUnop (ARec _) e1) (NNRCUnop (ARec _) e2) => true
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
    tnnrc_ext_rewrites_to e (tinline_let_fun e).
  Proof.
    tprove_correctness e.
    apply tlet_inline_arrow.
  Qed.

  (* push map through either and if *)
  (* Java equivalent: NnrcOptimizer.[same] *)
    Definition tfor_over_if_nil_fun  {fruntime:foreign_runtime}(e:nnrc)
      := match e with
         | NNRCFor x (NNRCIf e1 e2 ‵{||}) ebody =>
                     (NNRCIf e1 (NNRCFor x e2 ebody) ‵{||})
       | _ => e
       end.

  Lemma tfor_over_if_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tfor_over_if_nil_fun e).
  Proof.
    tprove_correctness e.
    rewrite tfor_over_if_arrow; simpl.
    rewrite tfor_nil_arrow.
    reflexivity.
  Qed.
  
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
    tnnrc_ext_rewrites_to e (tfor_over_either_nil_fun e).
  Proof.
    tprove_correctness e.
    rewrite tfor_over_either_arrow; simpl.
    rewrite tfor_nil_arrow.
    rewrite tnnrceither_rename_r_arrow by intuition; simpl.
    reflexivity.
  Qed.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tnnrcunop_over_either_nil_fun  {fruntime:foreign_runtime}(e:nnrc)
    := match e with
       | NNRCUnop op (NNRCEither e1 xl el xr (NNRCConst d)) =>
         NNRCEither e1 xl (NNRCUnop op el) xr (NNRCUnop op (NNRCConst d))
       | _ => e
       end.

  Lemma tnnrcunop_over_either_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tnnrcunop_over_either_nil_fun e).
  Proof.
    tprove_correctness e.
    apply tnnrcunop_over_either_arrow.
  Qed.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tnnrcunop_over_if_nil_fun  {fruntime:foreign_runtime}(e:nnrc)
    := match e with
       | NNRCUnop op (NNRCIf e1 e2 (NNRCConst d)) =>
         NNRCIf e1 (NNRCUnop op e2) (NNRCUnop op (NNRCConst d))
       | _ => e
       end.

  Lemma tnnrcunop_over_if_nil_fun_correctness {model:basic_model} (e:nnrc) :
    tnnrc_ext_rewrites_to e (tnnrcunop_over_if_nil_fun e).
  Proof.
    tprove_correctness e.
    apply tnnrcunop_over_if_arrow.
  Qed.

    (* optimizations for rproject *)

  (* Java equivalent: NnrcOptimizer.[same] *)
   Definition tnnrcproject_nil_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (ARecProject nil) e₁
        => NNRCConst (drec nil)
      | _ => e
    end.

  Definition tnnrcproject_nil_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tnnrcproject_nil_fun p.
  Proof.
    tprove_correctness p.
    apply tnnrcproject_nil.
  Qed.

  Hint Rewrite @tnnrcproject_nil_fun_correctness : toptim_correct.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tnnrcproject_over_const_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (ARecProject sl)
          (NNRCConst (drec l))
        => NNRCConst (drec (rproject l sl))
      | _ => e
    end.

  Definition tnnrcproject_over_const_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tnnrcproject_over_const_fun p.
  Proof.
    tprove_correctness p.
    apply tnnrcproject_over_const.
  Qed.

  Hint Rewrite @tnnrcproject_over_const_fun_correctness : toptim_correct.
  
  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tnnrcproject_over_rec_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (ARecProject sl)
          (NNRCUnop (ARec s) p₁)
        => if in_dec string_dec s sl
           then NNRCUnop (ARec s) p₁
           else ‵[||]
      | _ => e
    end.

  Definition tnnrcproject_over_rec_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tnnrcproject_over_rec_fun p.
  Proof.
    tprove_correctness p.
    - apply tnnrcproject_over_rec_in; trivial.
    - apply tnnrcproject_over_rec_nin; trivial. 
  Qed.

  Hint Rewrite @tnnrcproject_over_rec_fun_correctness : toptim_correct.

  (* Java equivalent: NnrcOptimizer.[same] *)
   Definition tnnrcproject_over_concat_r_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (ARecProject sl)
               (NNRCBinop AConcat
                        p₁ (NNRCUnop (ARec s) p₂))
        => if in_dec string_dec s sl
           then NNRCBinop AConcat
                         (NNRCUnop (ARecProject (remove string_dec s sl)) p₁)
                        (NNRCUnop (ARec s) p₂)
           else (NNRCUnop (ARecProject sl) p₁)
      | _ => e
    end.

  Definition tnnrcproject_over_concat_r_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tnnrcproject_over_concat_r_fun p.
  Proof.
    tprove_correctness p.
    - apply tnnrcproject_over_concat_rec_r_in; trivial.
    - apply tnnrcproject_over_concat_rec_r_nin; trivial.
  Qed.
                  
  Hint Rewrite @tnnrcproject_over_concat_r_fun_correctness : toptim_correct.

  (* Java equivalent: NnrcOptimizer.[same] *)
     Definition tnnrcproject_over_concat_l_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (ARecProject sl)
               (NNRCBinop AConcat
                        (NNRCUnop (ARec s) p₁) p₂)
        => if in_dec string_dec s sl
                     (* this case would need shape/type inference to handle, since we don't know if s is in p₂ *)

           then e
           else (NNRCUnop (ARecProject sl) p₂)
      | _ => e
    end.

  Definition tnnrcproject_over_concat_l_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tnnrcproject_over_concat_l_fun p.
  Proof.
    tprove_correctness p.
    apply tnnrcproject_over_concat_rec_l_nin; trivial.
  Qed.
                  
  Hint Rewrite @tnnrcproject_over_concat_l_fun_correctness : toptim_correct.

  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tnnrcproject_over_nnrcproject_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (ARecProject sl1)
          (NNRCUnop (ARecProject sl2) p1)
        => NNRCUnop (ARecProject (set_inter string_dec sl2 sl1)) p1
      | _ => e
    end.

  Definition tnnrcproject_over_nnrcproject_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tnnrcproject_over_nnrcproject_fun p.
  Proof.
    tprove_correctness p.
    apply tnnrcproject_over_nnrcproject.
  Qed.

  Hint Rewrite @tnnrcproject_over_nnrcproject_fun_correctness : toptim_correct.

  (* Java equivalent: NnrcOptimizer.[same] *)
   Definition tnnrcproject_over_either_fun {fruntime:foreign_runtime} (e:nnrc) :=
    match e with
      | NNRCUnop (ARecProject sl)
          (NNRCEither p xl p₁ xr p₂)
        => NNRCEither p xl (NNRCUnop (ARecProject sl) p₁) xr (NNRCUnop (ARecProject sl) p₂)
      | _ => e
    end.

  Definition tnnrcproject_over_either_fun_correctness {model:basic_model} p :
    p ⇒ᶜ tnnrcproject_over_either_fun p.
  Proof.
    tprove_correctness p.
    apply tnnrcproject_over_either.
  Qed.

  Hint Rewrite @tnnrcproject_over_either_fun_correctness : toptim_correct.

  (* count optimizations *)
  (* Java equivalent: NnrcOptimizer.[same] *)
  Definition tcount_over_flat_for_either_if_nil_fun  {fruntime:foreign_runtime}(e:nnrc)
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
    tnnrc_ext_rewrites_to e (tcount_over_flat_for_either_if_nil_fun e).
  Proof.
    destruct e; simpl; try reflexivity.
    repeat (match_destr; try reflexivity).
    apply tcount_over_flat_for_either_if_nil_arrow.
  Qed.

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
    tnnrc_ext_rewrites_to e (tcount_over_flat_for_either_either_nil_fun e).
  Proof.
    destruct e; simpl; try reflexivity.
    repeat (match_destr; try reflexivity).
    apply tcount_over_flat_for_either_either_nil_arrow.
  Qed.


  (* *************************** *)

  Local Open Scope string.
  
  (* Java equivalent: NnrcOptimizer.head_rew_list *)
  Definition head_rew_list {fruntime:foreign_runtime} : list (string*(nnrc -> nnrc)) :=
    [   ("tinline_let_fun", tinline_let_fun)
        ; ("tcount_over_flat_for_either_either_nil_fun", tcount_over_flat_for_either_either_nil_fun)
        ; ("tcount_over_flat_for_either_if_nil_fun", tcount_over_flat_for_either_if_nil_fun)
        ; ("tnnrc_merge_concat_to_concat_fun", tnnrc_merge_concat_to_concat_fun)
        ; ("tnnrc_dot_of_concat_rec_fun", tnnrc_dot_of_concat_rec_fun)
        ; ("tdot_of_rec_fun", tdot_of_rec_fun)
        ; ("tflatten_singleton_nnrc_fun", tflatten_singleton_nnrc_fun)
        ; ("tflatten_nil_nnrc_fun", tflatten_nil_nnrc_fun)
        ; ("tfor_singleton_to_let_fun", tfor_singleton_to_let_fun)
        ; ("tnnrcunop_over_either_nil_fun", tnnrcunop_over_either_nil_fun)
        ; ("tnnrcunop_over_if_nil_fun", tnnrcunop_over_if_nil_fun)
        ; ("tfor_over_either_nil_fun", tfor_over_either_nil_fun)
        ; ("tfor_over_if_nil_fun", tfor_over_if_nil_fun)
        ; ("tfor_nil_fun", tfor_nil_fun)
        ; ("tmap_sigma_fusion_samevar_fun", tmap_sigma_fusion_samevar_fun)
        ; ("tnnrcproject_nil_fun", tnnrcproject_nil_fun)
        ; ("tnnrcproject_over_const_fun", tnnrcproject_over_const_fun)
        ; ("tnnrcproject_over_rec_fun", tnnrcproject_over_rec_fun)
        ; ("tnnrcproject_over_concat_r_fun", tnnrcproject_over_concat_r_fun)
        ; ("tnnrcproject_over_concat_l_fun", tnnrcproject_over_concat_l_fun)
        ; ("tnnrcproject_over_nnrcproject_fun", tnnrcproject_over_nnrcproject_fun)
        ; ("tnnrcproject_over_either_fun", tnnrcproject_over_either_fun)
    ].

  (* Java equivalent: NnrcOptimizer.head_rew *)
  Definition head_rew 
             {fruntime:foreign_runtime}
             {logger:optimizer_logger string nnrc} (name:string)
    : nnrc -> nnrc :=
    apply_steps ("nnrc_head" ++ name) head_rew_list.

  Lemma head_rew_correctness
        {model:basic_model} {logger:optimizer_logger string nnrc}
        (name:string) (p:nnrc) :
    tnnrc_ext_rewrites_to p (head_rew name p).
  Proof.
    unfold head_rew.
    rewrite tnnrcproject_over_either_fun_correctness at 1.
    rewrite tnnrcproject_over_nnrcproject_fun_correctness at 1.
    rewrite tnnrcproject_over_concat_l_fun_correctness at 1.
    rewrite tnnrcproject_over_concat_r_fun_correctness at 1.
    rewrite tnnrcproject_over_rec_fun_correctness at 1.
    rewrite tnnrcproject_over_const_fun_correctness at 1.
    rewrite tnnrcproject_nil_fun_correctness at 1.
    rewrite tmap_sigma_fusion_samevar_fun_correctness at 1.
    rewrite tfor_nil_fun_correctness at 1.
    rewrite tfor_over_if_nil_fun_correctness at 1.
    rewrite tfor_over_either_nil_fun_correctness at 1.
    rewrite tnnrcunop_over_if_nil_fun_correctness at 1.
    rewrite tnnrcunop_over_either_nil_fun_correctness at 1.
    rewrite tfor_singleton_to_let_fun_correctness at 1.
    rewrite tflatten_nil_nnrc_fun_correctness at 1.
    rewrite tflatten_singleton_nnrc_fun_correctness at 1.
    rewrite tdot_of_rec_fun_correctness at 1.
    rewrite tnnrc_dot_of_concat_rec_fun_correctness at 1.
    rewrite tnnrc_merge_concat_to_concat_fun_correctness at 1.
    rewrite tcount_over_flat_for_either_if_nil_fun_correctness at 1.
    rewrite tcount_over_flat_for_either_either_nil_fun_correctness at 1.
    rewrite tinline_let_fun_correctness at 1.
    red; intros; split; [apply H|idtac]; intros.
    unfold head_rew_list.
    unfold apply_steps.
    rewrite hide_use_eq.
    simpl fold_right.
    repeat rewrite optimizer_step_result.
    unfold snd.
    reflexivity.
  Qed.

  (* Java equivalent: NnrcOptimizer.trew (inlined) *)
  Definition rew1 {fruntime:foreign_runtime} (p: nnrc) :=
    tunshadow_preserves_fun p.
  
  Lemma rew1_correctness {model:basic_model} (p:nnrc) :
    tnnrc_ext_rewrites_to p (rew1 p).
  Proof.
    unfold rew1.
    apply tunshadow_preserves_fun_correctness.
  Qed.
    
  Definition rew2
             {fruntime:foreign_runtime} {logger:optimizer_logger string nnrc} (p: nnrc) :=
    tnnrc_map_deep (head_rew "2") p.

  Lemma rew2_correctness
        {model:basic_model} {logger:optimizer_logger string nnrc} (p:nnrc) :
    tnnrc_ext_rewrites_to p (rew2 p).
  Proof.
    unfold rew2.
    assert (tnnrc_ext_rewrites_to p (tnnrc_map_deep (head_rew "2") p)).
    apply tnnrc_map_deep_correctness.
    intro p'.
    rewrite head_rew_correctness at 1.
    reflexivity.
    assumption.
  Qed.

  Definition rew3
             {fruntime:foreign_runtime} {logger:optimizer_logger string nnrc} (p: nnrc) :=
    tnnrc_map_deep (head_rew "3") p.

  (* Java equivalent: NnrcOptimizer.trew *)
  Definition trew
             {fruntime:foreign_runtime} {logger:optimizer_logger string nnrc}  (p:nnrc) :=
    let pass1p := rew1 p in
    (rew_size (rew_iter rew2 10) pass1p).

  Lemma trew_correctness
        {model:basic_model} {logger:optimizer_logger string nnrc} p:
    tnnrc_ext_rewrites_to p (trew p).
  Proof.
    unfold trew.
    rewrite rew1_correctness at 1.
    rewrite rew_size_correctness at 1; try reflexivity.
    intros p1.
    rewrite rew_iter_correctness at 1; try reflexivity.
    intros p2.
    rewrite rew2_correctness at 1; try reflexivity.
  Qed.
  

  Require Import NNRCMR.
  Require Import ForeignReduceOps.
  Definition trew_nnrcmr
             {fruntime:foreign_runtime} {fredop:foreign_reduce_op} {logger:optimizer_logger string nnrc}
             (l: nnrcmr) :=
    let inputs_loc := l.(mr_inputs_loc) in
    let chain :=
        List.map
          (fun mr =>
             let map :=
                 match mr.(mr_map) with
                 | MapDist (x, n) => MapDist (x, trew n)
                 | MapDistFlatten (x, n) => MapDistFlatten (x, trew n)
                 | MapScalar (x, n) => MapScalar (x, trew n)
                 end
             in
             let reduce :=
                 match mr.(mr_reduce) with
                 | RedId => RedId
                 | RedCollect (x, n) => RedCollect (x, trew n)
                 | RedOp op => RedOp op
                 | RedSingleton => RedSingleton
                 end
             in
             mkMR mr.(mr_input) mr.(mr_output) map reduce)
          l.(mr_chain)
    in
    let last :=
        let '((params, n), args) := l.(mr_last) in
        ((params, trew n), args)
    in
    mkMRChain
      inputs_loc
      chain
      last.

End TNNRCOptimizer.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
