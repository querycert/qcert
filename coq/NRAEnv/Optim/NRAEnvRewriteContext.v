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

(*******************************
 * Algebra contexts *
 *******************************)

Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import Arith.
Require Import List.
Require Import Utils.
Require Import CommonRuntime.
Require Import NRARuntime.
Require Import cNRAEnvRuntime.
Require Import NRAContext.
Require Import NRARewriteContext.
Require Import cNRAEnvContext.
Require Import cNRAEnvContextLift.
Require Import NRAEnvRewrite.

Section NRAEnvRewriteContext.
  
  Local Open Scope nraenv_core_ctxt.

  Context {fruntime:foreign_runtime}.

  Ltac simpl_domain_eq_const
    := repeat
         match goal with
         | [H: domain ?x = nil |- _ ] =>
           apply domain_nil in H; subst x
         | [H: domain ?x = _::_ |- _ ] =>
           let n := fresh "n" in
           let a := fresh "a" in
           destruct x as [|[n a]]; simpl in H; inversion H; clear H;
           try subst n
         end.

  Ltac simpl_plugins
    := match goal with
         [H1:is_list_sorted lt_dec ?x = true,
             H2:equivlist ?x ?y |- _ ] =>
         apply insertion_sort_equivlist_nat in H2;
           rewrite (insertion_sort_sorted_is_id _ _ H1) in H2;
           simpl in H2; simpl_domain_eq_const; clear H1
       end.

  Ltac simpl_ctxt_equiv :=
    try apply <- nraenv_core_ctxt_equiv_strict_equiv;
    red; simpl; intros; simpl_plugins; simpl.

  Local Open Scope nraenv_core_ctxt_scope.
  Lemma envctxt_and_comm_ctxt :
    $2 ∧ $1 ≡ₑ $1 ∧ $2.
  Proof.
    generalize ctxt_and_comm_ctxt; intros pf.
    apply lift_nra_context_proper in pf.
    simpl in pf; trivial.
  Qed.
  
  Lemma ctxt_envunion_assoc :
    ($1 ⋃ $2) ⋃ $3 ≡ₑ $1 ⋃ ($2 ⋃ $3).
  Proof.
    simpl_ctxt_equiv.
    apply envunion_assoc.
  Qed.

  Lemma ctxt_app_over_merge :
    (ENV ⊗ $1) ◯ $2 ≡ₑ ENV ⊗ ($1 ◯ $2).
  Proof.
    simpl_ctxt_equiv.
    apply app_over_merge.
  Qed.

  Lemma envctxt_select_union_distr :
    σ⟨ $0 ⟩($1 ⋃ $2) ≡ₑ σ⟨ $0 ⟩($1) ⋃ σ⟨ $0 ⟩($2).
  Proof.
    generalize ctxt_select_union_distr; intros pf.
    apply lift_nra_context_proper in pf.
    simpl in pf; trivial.
  Qed.


End NRAEnvRewriteContext.
  
