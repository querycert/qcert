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

Section NNRCOptimizer.
  Require Import String.
  Require Import List.
  Require Import Arith.
  
  Require Import Utils BasicRuntime.
  Require Import NNRCRuntime.

  Require Import Program.

  Context {fruntime:foreign_runtime}.

  (** Apply the function f to the direct child of p *)
  Definition nnrc_map (f: nnrc -> nnrc) (e:nnrc) :=
    match e with
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
      (forall e', nnrc_ext_eq (f e') e') -> nnrc_ext_eq (nnrc_map f e) e.
  Proof.
    intros f e Hf.
    nnrc_cases (induction e) Case;
      try solve [simpl; repeat rewrite Hf; reflexivity].
  Qed.

  (** Apply the function f to all subexpression of e. *)
  Fixpoint nnrc_map_deep (f: nnrc -> nnrc) (e: nnrc) :=
    match e with
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
      (forall e', nnrc_ext_eq (f e') e') -> nnrc_ext_eq (nnrc_map_deep f e) e.
  Proof.
    intros f e Hf.
    nnrc_cases (induction e) Case; simpl;
      try solve [repeat rewrite Hf; reflexivity];
      try solve [repeat rewrite Hf; rewrite IHe; reflexivity ];
      try solve [repeat rewrite Hf; rewrite IHe1; rewrite IHe2; reflexivity ];
      try solve [repeat rewrite Hf; rewrite IHe1; rewrite IHe2; rewrite IHe3; reflexivity ].
  Qed.

  (* Java equivalent: NnrcOptimizer.rew_iter *)
  Fixpoint rew_iter (rew: nnrc -> nnrc) (fuel: nat) (p: nnrc) :=
    match fuel with
      | 0 => p
      | S n => rew_iter rew n (rew p)
    end.

  Lemma rew_iter_correctness rew n p:
    (forall p', nnrc_ext_eq (rew p') p') -> nnrc_ext_eq (rew_iter rew n p) p.
  Proof.
    generalize p; clear p.
    induction n; try reflexivity.
    intros p Hrew.
    simpl.
    rewrite IHn; try assumption.
    apply Hrew.
  Qed.

  Require Import Recdef.
  Require Import Compare_dec.

  (* Java equivalent: NnrcOptimizer.rew_size (inlined) *)
  Function rew_cost (rew: nnrc -> nnrc) (cost: nnrc -> nat) (p: nnrc) { measure cost p } :=
    let p' := rew p in
    match nat_compare (cost p') (cost p) with
      | Lt => rew_cost rew cost p'
      | _ => p
    end.
  Proof.
    intros rew cost p Hcmp.
    apply nat_compare_lt in Hcmp.
    exact Hcmp.
  Defined.

  Lemma rew_cost_correctness rew cost p:
    (forall p', nnrc_ext_eq (rew p') p') -> nnrc_ext_eq (rew_cost rew cost p) p.
  Proof.
    intros Hrew.
    functional induction rew_cost rew cost p.
    - rewrite IHn.
      apply Hrew.
    - reflexivity.
  Qed.

  Hint Rewrite rew_cost_correctness : rew_correct.

  (* Java equivalent: NnrcOptimizer.rew_size *)
  Definition rew_size (rew: nnrc -> nnrc) (p: nnrc) :=
    rew_cost rew NNRCSize.nnrc_size p.

  Lemma rew_size_correctness rew p:
    (forall p', nnrc_ext_eq (rew p') p') -> nnrc_ext_eq (rew_size rew p) p.
  Proof.
    intros Hrew.
    unfold rew_size.
    apply rew_cost_correctness.
    assumption.
  Qed.

  Hint Rewrite rew_size_correctness : rew_correct.

  (* *************************** *)

  (* unshadowing *)

  Definition nunshadow := unshadow_simpl nil.
  
  (* *************************** *)
  Definition head_rew (e: nnrc) :=
    (nunshadow e).

  Lemma head_rew_correctness e:
    nnrc_ext_eq (head_rew e) e.
  Proof.
    unfold head_rew.
    apply unshadow_ext_preserves.
  Qed.

  Lemma rewriter_simpl_rew_no_free_var :
    forall (op : nnrc) (x : var),
      In x (nnrc_free_vars (head_rew op)) -> In x (nnrc_free_vars op).
  Proof.
    intros.
    unfold head_rew in H.
    eapply unshadow_free_vars; eapply H.
  Qed.

End NNRCOptimizer.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
