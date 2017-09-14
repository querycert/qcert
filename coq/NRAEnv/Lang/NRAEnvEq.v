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

Section NRAEnvEq.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import Utils.
  Require Import CommonRuntime.
  Require Import cNRAEnv.
  Require Import cNRAEnvEq.
  Require Import NRAEnv.

  (* Equivalence for extended algebra *)

  Local Open Scope nraenv_core_scope.
  Local Open Scope nraenv_scope.

  Context {fruntime:foreign_runtime}.

  Definition nraenv_eq (op1 op2:nraenv) : Prop :=
    forall (h:list(string*string))
           (c:list (string*data))
           (dn_c: Forall (fun d : string * data => data_normalized h (snd d)) c)
           (env:data)
           (dn_env:data_normalized h env)
           (x:data)
           (dn_x:data_normalized h x),
        nraenv_eval h c op1 env x = nraenv_eval h c op2 env x.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.

  Global Instance nraenv_equiv : Equivalence nraenv_eq.
  Proof.
    constructor.
    - unfold Reflexive, nraenv_eq.
      intros; reflexivity.
    - unfold Symmetric, nraenv_eq.
      intros. rewrite (H h c dn_c env dn_env x0) by trivial; reflexivity.
    - unfold Transitive, nraenv_eq.
      intros. rewrite (H h c dn_c env dn_env x0) by trivial; rewrite (H0 h c dn_c env dn_env x0) by trivial; reflexivity.
  Qed.

  Definition nraenv_eq_nraenv_core_eq (op1 op2:nraenv) : nraenv_eq op1 op2 <-> nraenv_core_eq (nraenv_core_of_nraenv op1) (nraenv_core_of_nraenv op2).
  Proof.
    split; intro; assumption.
  Qed.

  Notation "X ≡ₓ Y" := (nraenv_eq X Y) (at level 90) : nraenv_scope. (* ≡ = \equiv *)
  (** Thanks to shallow semantics, lifting between nraenv_core and nraenv is easy *)
  Section eq_lift.
    Require Import cNRAEnv cNRAEnvEq.
    Open Scope nraenv_core_scope.

    Lemma lift_nraenv_core_eq_to_nraenv_eq_r (q1 q2:nraenv_core) :
      q1 ≡ₑ q2 -> (nraenv_of_nraenv_core q1) ≡ₓ (nraenv_of_nraenv_core q2).
    Proof.
      unfold nraenv_eq.
      unfold nraenv_core_eq.
      intros.
      unfold nraenv_eval in *.
      rewrite nraenv_roundtrip.
      rewrite nraenv_roundtrip.
      auto.
    Qed.

    Lemma lift_nraenv_core_eq_to_nraenv_eq_l (q1 q2:nraenv_core) :
      (nraenv_of_nraenv_core q1) ≡ₓ (nraenv_of_nraenv_core q2) -> q1 ≡ₑ q2.
    Proof.
      unfold nraenv_eq.
      unfold nraenv_core_eq.
      intros.
      unfold nraenv_eval in *.
      rewrite nraenv_roundtrip in H.
      rewrite nraenv_roundtrip in H.
      specialize (H _ _ dn_c _ dn_env _ dn_x); intros.
      assumption.
    Qed.

    Lemma lift_nraenv_core_eq_to_nraenv_eq (q1 q2:nraenv_core) :
      q1 ≡ₑ q2 <-> (nraenv_of_nraenv_core q1) ≡ₓ (nraenv_of_nraenv_core q2).
    Proof.
      split.
      apply lift_nraenv_core_eq_to_nraenv_eq_r.
      apply lift_nraenv_core_eq_to_nraenv_eq_l.
    Qed.

    Lemma lift_nraenv_eq_to_nraenv_core_eq_r (q1 q2:nraenv) :
      q1 ≡ₓ q2 -> (nraenv_core_of_nraenv q1) ≡ₑ (nraenv_core_of_nraenv q2).
    Proof.
      unfold nraenv_eq.
      unfold nraenv_core_eq.
      intros.
      unfold nraenv_eval in *.
      specialize (H _ _ dn_c _ dn_env _ dn_x); intros.
      assumption.
    Qed.
  
    Lemma lift_nraenv_eq_to_nraenv_core_eq_l (q1 q2:nraenv) :
      (nraenv_core_of_nraenv q1) ≡ₑ (nraenv_core_of_nraenv q2) -> q1 ≡ₓ q2.
    Proof.
      unfold nraenv_eq.
      unfold nraenv_core_eq.
      intros.
      unfold nraenv_eval in *.
      specialize (H _ _ dn_c _ dn_env _ dn_x); intros.
      assumption.
    Qed.
  
    Lemma lift_nraenv_eq_to_nraenv_core_eq (q1 q2:nraenv) :
      q1 ≡ₓ q2 <-> (nraenv_core_of_nraenv q1) ≡ₑ (nraenv_core_of_nraenv q2).
    Proof.
      split.
      apply lift_nraenv_eq_to_nraenv_core_eq_r.
      apply lift_nraenv_eq_to_nraenv_core_eq_l.
    Qed.
  End eq_lift.
  
  (* all the extended algebraic constructors are proper wrt. equivalence *)

  (* NRAEnvID *)
  Global Instance nraenv_id_proper : Proper nraenv_eq NRAEnvID.
  Proof.
    unfold Proper, respectful, nraenv_eq.
    apply anid_proper; assumption.
  Qed.

  (* NRAEnvConst *)
  Global Instance nraenv_const_proper : Proper (eq ==> nraenv_eq) NRAEnvConst.
  Proof.
    unfold Proper, respectful, nraenv_eq; intros.
    apply anconst_proper; assumption.
  Qed.

  (* NRAEnvBinOp *)

  Global Instance nraenv_binary_op_proper : Proper (binary_op_eq ==> nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvBinop.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply anbinary_op_proper; assumption.
  Qed.

  (* NRAEnvUnop *)
  Global Instance nraenv_unary_op_proper : Proper (unary_op_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvUnop.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply anunary_op_proper; assumption.
  Qed.

  (* NRAEnvMap *)
  Global Instance nraenv_map_proper : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvMap.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply anmap_proper; assumption.
  Qed.

  (* NRAEnvMapProduct *)
  Global Instance nraenv_mapconcat_proper : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvMapProduct.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply anmapconcat_proper; assumption.
  Qed.

  (* NRAEnvProduct *)
  Global Instance nraenv_product_proper : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvProduct.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply anproduct_proper; assumption.
  Qed.

  (* NRAEnvSelect *)
  Global Instance nraenv_select_proper : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvSelect.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply anselect_proper; assumption.
  Qed.

  (* NRAEnvEither *)
  Global Instance nraenv_either_proper : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvEither.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros; simpl.
    destruct x1; simpl; trivial; inversion dn_x; subst; eauto.
  Qed.

  (* NRAEnvEitherConcat *)
  Global Instance nraenv_eitherconcat_proper : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvEitherConcat.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros; simpl.
    rewrite (H0 h c dn_c env dn_env x1) by trivial; rewrite (H h c dn_c env dn_env x1) by trivial.
    case_eq (h ⊢ₑ nraenv_core_of_nraenv y0 @ₑ x1 ⊣ c;env); case_eq (h ⊢ₑ nraenv_core_of_nraenv y @ₑ x1 ⊣ c;env); intros; simpl; trivial.
  Qed.
  
  (* NRAEnvDefault *)
  Global Instance nraenv_default_proper : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvDefault.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply andefault_proper; assumption.
  Qed.

  (* NRAEnvApp *)
  Global Instance nraenv_app_proper : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvApp.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply anapp_proper; assumption.
  Qed.

  (* NRAEnvENV *)
  Global Instance nraenv_getconstant_proper s : Proper nraenv_eq (NRAEnvGetConstant s).
  Proof.
    unfold Proper, respectful, nraenv_eq.
    apply angetconstant_proper; assumption.
  Qed.
  
  (* NRAEnvENV *)
  Global Instance nraenv_env_proper : Proper nraenv_eq NRAEnvEnv.
  Proof.
    unfold Proper, respectful, nraenv_eq.
    apply anenv_proper; assumption.
  Qed.

  (* NRAEnvApp *)
  Global Instance nraenv_appenv_proper : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvAppEnv.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply anappenv_proper; assumption.
  Qed.

  (* NRAEnvMapEnv *)
  Global Instance nraenv_mapenv_proper : Proper (nraenv_eq ==> nraenv_eq) NRAEnvMapEnv.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply anmapenv_proper; assumption.
  Qed.

  (* NRAEnvFlatMap *)
  Global Instance nraenv_flatmap_proper : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvFlatMap.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply anunary_op_proper; try assumption; try reflexivity.
    apply anmap_proper; assumption.
  Qed.

  (* NRAEnvJoin *)
  Global Instance nraenv_join_proper : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvJoin.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply anselect_proper; try assumption.
    apply anproduct_proper; assumption.
  Qed.

  (* NRAEnvProject *)
  Global Instance nraenv_project_proper : Proper (eq ==> nraenv_eq ==> nraenv_eq) NRAEnvProject.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraenv_eq_nraenv_core_eq in *.
    simpl.
    unfold project.
    rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* NRAEnvGroupBy *)
  Global Instance nraenv_group_by_proper : Proper (eq ==> eq ==> nraenv_eq ==> nraenv_eq) NRAEnvGroupBy.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraenv_eq_nraenv_core_eq in *.
    simpl. unfold group_by_with_env.
    rewrite H1 by trivial.
    reflexivity.
  Qed.

  (* NRAEnvUnnest *)
  Global Instance nraenv_unnest_proper : Proper (eq ==> eq ==> nraenv_eq ==> nraenv_eq) NRAEnvUnnest.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraenv_eq_nraenv_core_eq in *.
    simpl. unfold unnest.
    rewrite H1 by trivial.
    reflexivity.
  Qed.

End NRAEnvEq.

Notation "X ≡ₓ Y" := (nraenv_eq X Y) (at level 90) : nraenv_scope. (* ≡ = \equiv *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
