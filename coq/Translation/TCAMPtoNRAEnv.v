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

Section TCAMPtoNRAEnv.

  Require Import String List.

  Require Import Utils BasicSystem.
  Require Import NRASystem NRAEnvSystem.
  Require Import CAMPSystem.
  Require Import CAMPtoNRAEnv TCAMPtoNRA TCAMPtocNRAEnv.

  Local Open Scope string_scope.
  Local Open Scope list_scope.
  Local Open Scope rule_scope.

  Hint Constructors unaryOp_type binOp_type.

  Context {m:basic_model}.

  Lemma nraenv_of_pat_type_preserve τc Γ pf p τin τout :
    [τc&Γ] |= p ; τin ~> τout ->
    nraenv_of_pat p ▷ₓ τin >=> Coll τout ⊣ τc;(Rec Closed Γ pf).
  Proof.
    Hint Resolve data_type_drec_nil.
    unfold nraenv_type.
    rewrite nraenv_of_pat_cnraenv_of_pat_ident.
    apply cnraenv_of_pat_type_preserve.
  Qed.

  (** Some corollaries of the main Lemma *)

  Lemma nraenv_of_pat_nraenv_of_pat_top p τc τin τout :
    nraenv_of_pat p ▷ₓ τin >=> Coll τout ⊣ τc;(Rec Closed nil eq_refl) ->
    nraenv_of_pat_top p ▷ₓ τin >=> Coll τout ⊣ τc;(Rec Closed nil eq_refl).
  Proof.
    intros.
    repeat (econstructor; eauto).
  Qed.
    
  Theorem alg_of_pat_top_type_preserve p τc τin τout :
    [τc&nil] |= p ; τin ~> τout ->
    nraenv_of_pat_top p ▷ₓ τin >=> Coll τout ⊣ τc;(Rec Closed nil eq_refl).
  Proof.
    intros.
    apply nraenv_of_pat_nraenv_of_pat_top.
    apply nraenv_of_pat_type_preserve; eauto.
  Qed.

  Require Import TRule RuletoNRAEnv.

  Theorem nraenv_of_rule_type_preserve τworld τout r :
    @rule_type m τworld τout r ->
    nraenv_of_rule r ▷ₓ Unit >=> Coll τout ⊣  (mkTWorld τworld);(Rec Closed nil eq_refl).
    Proof.
      unfold rule_type; intros.
      apply nraenv_of_pat_type_preserve; trivial.
    Qed.

End TCAMPtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
