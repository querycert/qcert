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

Require Import String.
Require Import List.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import CAMPSugar.
Require Export TCAMP.

Section TCAMPSugar.
  Local Open Scope camp_scope.

  Hint Constructors camp_type.

  Context {m:basic_model}.

  Lemma  PTCast τc Γ br bs :
    [τc&Γ] |= pcast br ; (Brand bs) ~> (Brand br).
  Proof.
    repeat econstructor.
  Qed.

  Lemma PTSingleton τc Γ τ :
    [τc&Γ] |= psingleton ; (Coll τ) ~> τ.
  Proof.
    repeat econstructor.
  Qed.

  Lemma PTmapall τc {Γ : tbindings} {τ₁ τ₂ : rtype} {p : camp} :
    NoDup (domain Γ) ->
    ([τc&Γ] |= p; τ₁ ~> τ₂) -> [τc&Γ] |= mapall p; Coll τ₁ ~> Coll τ₂.
  Proof.
    unfold mapall; intros.
    econstructor.
    + repeat econstructor; eauto.
    + rewrite merge_bindings_nil_r; eauto.
    + simpl. apply camp_type_tenv_rec; eauto.
      Grab Existential Variables.
      eauto.
  Qed.

  Lemma PTmapall_inv τc {Γ : tbindings} {τ₁ τ₂ : rtype} {p : camp} :
    is_list_sorted ODT_lt_dec (domain Γ) = true ->
    [τc&Γ] |= mapall p; τ₁ ~> τ₂ ->
                       exists τ₁' τ₂',
                         τ₁ = Coll τ₁' /\
                         τ₂ = Coll τ₂' /\
                         ([τc&Γ] |= p; τ₁' ~> τ₂').
  Proof.
    unfold mapall; intros.
    inversion H0; subst.
    inversion H3; subst.
    inversion H8; subst.
    symmetry in H4; apply map_eq_nil in H4.
    rtype_equalizer.
    subst.
    rewrite merge_bindings_nil_r in H5.
    inversion H5; subst.
    rewrite sort_sorted_is_id in H6; eauto.
  Qed.

End TCAMPSugar.

