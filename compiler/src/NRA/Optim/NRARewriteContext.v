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
Require Import NPeano.
Require Import Omega.
Require Import List.
Require Import Utils.
Require Import CommonRuntime.
Require Import NRA.
Require Import NRAEq.
Require Import NRAContext.
Require Import NRARewrite.

Section NRARewriteContext.
  Local Open Scope nra_ctxt.

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
  
  Lemma lt_nat_compat (x y:nat) : ~ x < y -> ~ y < x -> x = y.
  Proof.
    omega.
  Qed.

  Lemma insertion_sort_equivlist_nat l l':
    equivlist l l' -> insertion_sort lt_dec l = insertion_sort lt_dec l'.
  Proof.
    apply (@insertion_sort_equivlist nat lt lt_dec eq_equivalence nat_eq_eqdec Nat.lt_strorder lt_nat_compat).
  Qed.

  Ltac simpl_plugins
    := match goal with
         [H1:is_list_sorted lt_dec ?x = true,
             H2:equivlist ?x ?y |- _ ] =>
         apply insertion_sort_equivlist_nat in H2;
           rewrite (insertion_sort_sorted_is_id _ _ H1) in H2;
           simpl in H2; simpl_domain_eq_const; clear H1
       end.

  Ltac simpl_ctxt_equiv :=
    try apply <- nra_ctxt_equiv_strict_equiv;
    red; simpl; intros; simpl_plugins; simpl.

  Lemma ctxt_and_comm_ctxt :
    $2 ∧ $1 ≡ₐ $1 ∧ $2.
  Proof.
    simpl_ctxt_equiv.
    apply and_comm.
  Qed.

  Lemma ctxt_unnest_singleton_ctxt s1 s2 s3  :
    s1 <> s2 /\ s2 <> s3 /\ s3 <> s1 ->
    χ⟨¬π[s1 ]( ID)
     ⟩( ⋈ᵈ⟨χ⟨‵[| (s2, ID)|] ⟩( (ID) · s1)
          ⟩( ‵{|‵[| (s3, $1)|] ⊕ ‵[| (s1, ‵{| $2|})|]|}))
     ≡ₐ ‵{|‵[| (s3, $1)|] ⊕ ‵[| (s2, $2)|]|}.
  Proof.
    intros.
    simpl_ctxt_equiv.
    apply unnest_singleton; trivial.
  Qed.

  Lemma ctxt_select_union_distr :
    σ⟨ $0 ⟩($1 ⋃ $2) ≡ₐ σ⟨ $0 ⟩($1) ⋃ σ⟨ $0 ⟩($2).
  Proof.
    intros.
    simpl_ctxt_equiv.
    apply union_select_distr.
  Qed.

End NRARewriteContext.
  
