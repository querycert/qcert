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
Require Import CommonSystem.
Require Import NRASystem.
Require Import NRAEnvSystem.
Require Import CAMPSystem.
Require Import CAMPtoNRAEnv.
Require Import TCAMPtoNRA.
Require Import TCAMPtocNRAEnv.

Section TCAMPtoNRAEnv.
  Local Open Scope string_scope.
  Local Open Scope list_scope.
  Local Open Scope camp_scope.

  Hint Constructors unary_op_type binary_op_type.

  Context {m:basic_model}.

  Lemma nraenv_of_camp_type_preserve τc Γ pf p τin τout :
    [τc&Γ] |= p ; τin ~> τout ->
    nraenv_of_camp p ▷ₓ τin >=> Coll τout ⊣ τc;(Rec Closed Γ pf).
  Proof.
    Hint Resolve data_type_drec_nil.
    unfold nraenv_type.
    rewrite nraenv_of_camp_nraenv_core_of_camp_ident.
    apply nraenv_core_of_camp_type_preserve.
  Qed.

  (** Some corollaries of the main Lemma *)

  Lemma nraenv_of_camp_nraenv_of_camp_top p τc τin τout :
    nraenv_of_camp p ▷ₓ τin >=> Coll τout ⊣ τc;(Rec Closed nil eq_refl) ->
    nraenv_of_camp_top p ▷ₓ τin >=> Coll τout ⊣ τc;(Rec Closed nil eq_refl).
  Proof.
    intros.
    repeat (econstructor; eauto).
  Qed.
    
  Theorem alg_of_camp_top_type_preserve p τc τin τout :
    [τc&nil] |= p ; τin ~> τout ->
    nraenv_of_camp_top p ▷ₓ τin >=> Coll τout ⊣ τc;(Rec Closed nil eq_refl).
  Proof.
    intros.
    apply nraenv_of_camp_nraenv_of_camp_top.
    apply nraenv_of_camp_type_preserve; eauto.
  Qed.

End TCAMPtoNRAEnv.

