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
Require Import Compare_dec.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNRAEnv.
Require Import cNRAEnvEq.
Require Import NRAEnv.

Section NRAEnvEq.
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

  Definition nraenv_eq_nraenv_core_eq (op1 op2:nraenv) : nraenv_eq op1 op2 <-> nraenv_core_eq (nraenv_to_nraenv_core op1) (nraenv_to_nraenv_core op2).
  Proof.
    split; intro; assumption.
  Qed.

  Notation "X ≡ₓ Y" := (nraenv_eq X Y) (at level 90) : nraenv_scope. (* ≡ = \equiv *)
  (** Thanks to shallow semantics, lifting between nraenv_core and nraenv is easy *)
  Section eq_lift.
    Open Scope nraenv_core_scope.

    Lemma lift_nraenv_core_eq_to_nraenv_eq_r (q1 q2:nraenv_core) :
      q1 ≡ₑ q2 -> (nraenv_core_to_nraenv q1) ≡ₓ (nraenv_core_to_nraenv q2).
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
      (nraenv_core_to_nraenv q1) ≡ₓ (nraenv_core_to_nraenv q2) -> q1 ≡ₑ q2.
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
      q1 ≡ₑ q2 <-> (nraenv_core_to_nraenv q1) ≡ₓ (nraenv_core_to_nraenv q2).
    Proof.
      split.
      apply lift_nraenv_core_eq_to_nraenv_eq_r.
      apply lift_nraenv_core_eq_to_nraenv_eq_l.
    Qed.

    Lemma lift_nraenv_eq_to_nraenv_core_eq_r (q1 q2:nraenv) :
      q1 ≡ₓ q2 -> (nraenv_to_nraenv_core q1) ≡ₑ (nraenv_to_nraenv_core q2).
    Proof.
      unfold nraenv_eq.
      unfold nraenv_core_eq.
      intros.
      unfold nraenv_eval in *.
      specialize (H _ _ dn_c _ dn_env _ dn_x); intros.
      assumption.
    Qed.
  
    Lemma lift_nraenv_eq_to_nraenv_core_eq_l (q1 q2:nraenv) :
      (nraenv_to_nraenv_core q1) ≡ₑ (nraenv_to_nraenv_core q2) -> q1 ≡ₓ q2.
    Proof.
      unfold nraenv_eq.
      unfold nraenv_core_eq.
      intros.
      unfold nraenv_eval in *.
      specialize (H _ _ dn_c _ dn_env _ dn_x); intros.
      assumption.
    Qed.
  
    Lemma lift_nraenv_eq_to_nraenv_core_eq (q1 q2:nraenv) :
      q1 ≡ₓ q2 <-> (nraenv_to_nraenv_core q1) ≡ₑ (nraenv_to_nraenv_core q2).
    Proof.
      split.
      apply lift_nraenv_eq_to_nraenv_core_eq_r.
      apply lift_nraenv_eq_to_nraenv_core_eq_l.
    Qed.
  End eq_lift.
  
  (* all the extended algebraic constructors are proper wrt. equivalence *)

  (* NRAEnvGetConstant *)
  Global Instance proper_NRAEnvGetConstant s : Proper nraenv_eq (NRAEnvGetConstant s).
  Proof.
    unfold Proper, respectful, nraenv_eq.
    apply proper_cNRAEnvGetConstant; assumption.
  Qed.
  
  (* NRAEnvID *)
  Global Instance proper_NRAEnvID : Proper nraenv_eq NRAEnvID.
  Proof.
    unfold Proper, respectful, nraenv_eq.
    apply proper_cNRAEnvID; assumption.
  Qed.

  (* NRAEnvConst *)
  Global Instance proper_NRAEnvConst : Proper (eq ==> nraenv_eq) NRAEnvConst.
  Proof.
    unfold Proper, respectful, nraenv_eq; intros.
    apply proper_cNRAEnvConst; assumption.
  Qed.

  (* NRAEnvBinop *)
  Global Instance proper_NRAEnvBinop : Proper (binary_op_eq ==> nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvBinop.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvBinop; assumption.
  Qed.

  (* NRAEnvUnop *)
  Global Instance proper_NRAEnvUnop : Proper (unary_op_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvUnop.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvUnop; assumption.
  Qed.

  (* NRAEnvMap *)
  Global Instance proper_NRAEnvMap : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvMap.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvMap; assumption.
  Qed.

  (* NRAEnvMapProduct *)
  Global Instance proper_NRAEnvMapProduct : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvMapProduct.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvMapProduct; assumption.
  Qed.

  (* NRAEnvProduct *)
  Global Instance proper_NRAEnvProduct : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvProduct.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvProduct; assumption.
  Qed.

  (* NRAEnvSelect *)
  Global Instance proper_NRAEnvSelect : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvSelect.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvSelect; assumption.
  Qed.

  (* NRAEnvEither *)
  Global Instance proper_NRAEnvEither : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvEither.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros; simpl.
    destruct x1; simpl; trivial; inversion dn_x; subst; eauto.
  Qed.

  (* NRAEnvEitherConcat *)
  Global Instance proper_NRAEnvEitherConcat : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvEitherConcat.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros; simpl.
    rewrite (H0 h c dn_c env dn_env x1) by trivial; rewrite (H h c dn_c env dn_env x1) by trivial.
    case_eq (h ⊢ₑ nraenv_to_nraenv_core y0 @ₑ x1 ⊣ c;env); case_eq (h ⊢ₑ nraenv_to_nraenv_core y @ₑ x1 ⊣ c;env); intros; simpl; trivial.
  Qed.
  
  (* NRAEnvDefault *)
  Global Instance proper_NRAEnvDefault : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvDefault.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvDefault; assumption.
  Qed.

  (* NRAEnvApp *)
  Global Instance proper_NRAEnvApp : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvApp.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvApp; assumption.
  Qed.

  (* NRAEnvEnv *)
  Global Instance proper_NRAEnvEnv : Proper nraenv_eq NRAEnvEnv.
  Proof.
    unfold Proper, respectful, nraenv_eq.
    apply proper_cNRAEnvEnv; assumption.
  Qed.

  (* NRAEnvAppEnv *)
  Global Instance proper_NRAEnvAppEnv : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvAppEnv.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvAppEnv; assumption.
  Qed.

  (* NRAEnvMapEnv *)
  Global Instance proper_NRAEnvMapEnv : Proper (nraenv_eq ==> nraenv_eq) NRAEnvMapEnv.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvMapEnv; assumption.
  Qed.

  (* NRAEnvFlatMap *)
  Global Instance proper_NRAEnvFlatMap : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvFlatMap.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvUnop; try assumption; try reflexivity.
    apply proper_cNRAEnvMap; assumption.
  Qed.

  (* NRAEnvJoin *)
  Global Instance proper_NRAEnvJoin : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvJoin.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvSelect; try assumption.
    apply proper_cNRAEnvProduct; assumption.
  Qed.

  (* NRAEnvNaturalJoin *)
  Global Instance proper_NRAEnvNaturalJoin : Proper (nraenv_eq ==> nraenv_eq ==> nraenv_eq) NRAEnvNaturalJoin.
  Proof.
    unfold Proper, respectful, nraenv_eq, nraenv_eval; intros.
    apply proper_cNRAEnvUnop; try assumption; try reflexivity.
    apply proper_cNRAEnvMap; try assumption; try reflexivity.
    apply proper_cNRAEnvProduct; try assumption.
    apply proper_cNRAEnvMap; try assumption; reflexivity.
    apply proper_cNRAEnvMap; try assumption; reflexivity.
  Qed.

  (* NRAEnvProject *)
  Global Instance proper_NRAEnvProject : Proper (eq ==> nraenv_eq ==> nraenv_eq) NRAEnvProject.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraenv_eq_nraenv_core_eq in *.
    simpl.
    unfold macro_cNRAEnvProject.
    rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* NRAEnvGroupBy *)
  Global Instance proper_NRAEnvGroupBy : Proper (eq ==> eq ==> nraenv_eq ==> nraenv_eq) NRAEnvGroupBy.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraenv_eq_nraenv_core_eq in *.
    simpl. unfold macro_cNRAEnvGroupBy.
    rewrite H1 by trivial.
    reflexivity.
  Qed.

  (* NRAEnvUnnest *)
  Global Instance proper_NRAEnvUnnest : Proper (eq ==> eq ==> nraenv_eq ==> nraenv_eq) NRAEnvUnnest.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraenv_eq_nraenv_core_eq in *.
    simpl. unfold macro_cNRAEnvUnnest.
    rewrite H1 by trivial.
    reflexivity.
  Qed.

End NRAEnvEq.

Notation "X ≡ₓ Y" := (nraenv_eq X Y) (at level 90) : nraenv_scope. (* ≡ = \equiv *)

