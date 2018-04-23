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
Require Import Sumbool.
Require Import Arith.
Require Import Bool.
Require Import Morphisms.
Require Import Basics.
Require Import BrandRelation.
Require Import Utils.
Require Import Types.
Require Import ForeignData.
Require Import CommonData.
Require Import ForeignDataTyping.
Require Import TData.

Section TBindings.
  Context {ftype:foreign_type}.
  Context {m:brand_model}.

  Definition tbindings := list (string*rtype).

  Context {fdata:foreign_data}.
  Context {fdtyping:foreign_data_typing}.
  Definition bindings_type (b:list (string*data)) (t:tbindings)
    := Forall2 (fun xy1 xy2 =>
                      (fst xy1) = (fst xy2)
                  /\ data_type (snd xy1) (snd xy2)) b t.

  Lemma bindings_type_has_type {env Γ} pf :
      bindings_type  env Γ ->
      data_type (drec env) (Rec Closed Γ pf).
  Proof.
    intros.
    apply dtrec_full.
    assumption.
  Qed.

  Lemma bindings_type_sort c τc :
    bindings_type c τc ->
    bindings_type (rec_sort c) (rec_sort τc).
  Proof.
    unfold bindings_type.
    intros.
    apply rec_sort_Forall2; trivial.
    apply sorted_forall_same_domain; trivial.
  Qed.

  Lemma bindings_type_app l1 l2 r1 r2 :
    bindings_type l1 r1 -> bindings_type l2 r2 ->
    bindings_type (l1 ++ l2) (r1 ++ r2) .
  Proof.
    unfold bindings_type.
    apply Forall2_app; trivial; tauto.
  Qed.

  Lemma bindings_type_rec_concat_sort l1 l2 r1 r2 :
    bindings_type l1 r1 -> bindings_type l2 r2 ->
    bindings_type (rec_concat_sort l1 l2) (rec_concat_sort r1 r2) .
  Proof.
    intros.
    apply bindings_type_sort.
    apply bindings_type_app; trivial.
  Qed.
  
  Hint Resolve data_type_normalized.
  Lemma bindings_type_Forall_normalized c τc :
    bindings_type c τc ->
    Forall
      (fun d : string * data => data_normalized brand_relation_brands (snd d))
      c.
  Proof.
    induction 1; trivial.
    intuition.
    eauto.
  Qed.

End TBindings.

Hint Resolve bindings_type_Forall_normalized.

