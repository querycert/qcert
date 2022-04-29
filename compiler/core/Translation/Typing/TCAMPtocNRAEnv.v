(*
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
Require Import Utils.
Require Import DataSystem.
Require Import NRASystem.
Require Import cNRAEnvSystem.
Require Import CAMPSystem.
Require Import CAMPtocNRAEnv.
Require Import TCAMPtoNRA.

Section TCAMPtocNRAEnv.
  Local Open Scope string_scope.
  Local Open Scope list_scope.
  Local Open Scope camp_scope.

  Hint Constructors nraenv_core_type unary_op_type binary_op_type : qcert.

  Context {m:basic_model}.

  Lemma nraenv_core_of_camp_type_preserve τc Γ pf p τin τout :
    [τc&Γ] |= p ; τin ~> τout ->
    nraenv_core_of_camp p ▷ τin >=> Coll τout ⊣ τc;(Rec Closed Γ pf).
  Proof.
    Hint Resolve data_type_drec_nil : qcert.
    revert Γ pf τin τout.
    induction p; simpl; inversion 1; subst.
    (* PTconst *)
    - unfold nraenv_match.
      qeauto.
    (* PTunop *)
    - qeauto. 
    (* PTbinop *)
    - econstructor.
      + eapply (@type_cNRAEnvBinop m _ (Rec Closed Γ pf) (Rec Closed (("a1", τ₂₁)::("a2", τ₂₂)::nil) (eq_refl _))). qeauto.
        apply (@type_cNRAEnvUnop m _ (Rec Closed Γ pf) (Rec Closed (("a1", τ₂₁) :: ("a2", τ₂₂) :: nil) eq_refl) (Rec Closed (("a1", τ₂₁) :: ("a2", τ₂₂) :: nil) eq_refl)).
        econstructor; reflexivity.
        qeauto.
        apply (@type_cNRAEnvUnop m _ (Rec Closed Γ pf) (Rec Closed (("a1", τ₂₁) :: ("a2", τ₂₂) :: nil) eq_refl) (Rec Closed (("a1", τ₂₁) :: ("a2", τ₂₂) :: nil) eq_refl)).
        econstructor; reflexivity.
        econstructor; qeauto.
      + econstructor; qeauto.
    (* PTmap *)
    - econstructor; qeauto.
    (* PTassert *)
    - repeat econstructor; qeauto.
    (* PTorElse *)
    - qeauto.
    (* PTit *)
    - econstructor; qeauto.
    (* PTletIt *)
    - econstructor; qeauto.
    (* PTgetconstant *)
    - repeat (econstructor; qeauto).
    (* PTenv *)
    - rewrite (is_list_sorted_ext _ _ pf pf0).
      repeat (econstructor; qeauto).
    (* PTletEnv *)
    - econstructor; qeauto.
      econstructor; qeauto.
      assert (Γeq:Γ'' = rec_concat_sort Γ Γ')
        by (unfold merge_bindings in *; 
             destruct (Compat.compatible Γ Γ'); congruence).
      generalize (merge_bindings_sorted H4). subst. 
      intros.
      econstructor; qeauto.
    (* PTEither *)
    - repeat (econstructor; qeauto).
    (* PTEither *)
    - repeat (econstructor; qeauto).
    Unshelve.
    qeauto. qeauto. qeauto.
  Qed.

  (** Some corollaries of the main Lemma *)

  Lemma nraenv_core_of_camp_nraenv_core_of_camp_top p τc τin τout :
    nraenv_core_of_camp p ▷ τin >=> Coll τout ⊣ τc;(Rec Closed nil eq_refl) ->
    nraenv_core_of_camp_top p ▷ τin >=> Coll τout ⊣ τc;(Rec Closed nil eq_refl).
  Proof.
    intros.
    repeat (econstructor; qeauto).
  Qed.
    
  Theorem alg_of_camp_top_type_preserve p τc τin τout :
    [τc&nil] |= p ; τin ~> τout ->
    nraenv_core_of_camp_top p ▷ τin >=> Coll τout ⊣ τc;(Rec Closed nil eq_refl).
  Proof.
    intros.
    apply nraenv_core_of_camp_nraenv_core_of_camp_top.
    apply nraenv_core_of_camp_type_preserve; eauto.
  Qed.

End TCAMPtocNRAEnv.

