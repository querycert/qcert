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

Section ROptimEnvContext.
  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.

  Require Import Arith List.
  
  Require Import Utils BasicRuntime.
  Require Import RAlg RAlgEnv RAlgEnvEq.
  
  Require Import RAlgContext ROptimEnv ROptimContext.
  Require Import RAlgEnvContext RAlgEnvContextLift.
  Local Open Scope algenv_ctxt.

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
    try apply <- algenv_ctxt_equiv_strict_equiv;
    red; simpl; intros; simpl_plugins; simpl.

  Local Open Scope algenv_ctxt_scope.
  Lemma envctxt_and_comm_ctxt :
    $2 ∧ $1 ≡ₑ $1 ∧ $2.
  Proof.
    generalize ctxt_and_comm_ctxt; intros pf.
    apply lift_alg_context_proper in pf.
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

End ROptimEnvContext.
  
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
