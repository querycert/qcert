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
Require Import NRARuntime.
Require Import cNRAEnv.
Require Import cNRAEnvIgnore.

Section cNRAEnvEq.
  Local Open Scope string.
  Local Open Scope nraenv_core_scope.

  Context {fruntime:foreign_runtime}.

  (* Equivalence for environment-enabled algebra *)
  
  Hint Resolve dnrec_sort_content.

  Definition nraenv_core_eq (op1 op2:nraenv_core) : Prop :=
    forall
      (h:list(string*string))
      (c:list (string*data))
      (dn_c:Forall (fun d => data_normalized h (snd d)) c)
      (env:data)
      (dn_env:data_normalized h env)
      (x:data)
      (dn_x:data_normalized h x),
      h ⊢ₑ op1 @ₑ x ⊣ c;env = h ⊢ₑ op2 @ₑ x ⊣ c;env.

  Global Instance nraenv_core_equiv : Equivalence nraenv_core_eq.
  Proof.
    constructor.
    - unfold Reflexive, nraenv_core_eq.
      intros; reflexivity.
    - unfold Symmetric, nraenv_core_eq.
      intros. rewrite (H h c dn_c env dn_env x0) by trivial; reflexivity.
    - unfold Transitive, nraenv_core_eq.
      intros. rewrite (H h c dn_c env dn_env x0) by trivial; rewrite (H0 h c dn_c env dn_env x0) by trivial; reflexivity.
  Qed.

  Hint Resolve dnrec_sort.
    
  (* all the extended nraebraic constructors are proper wrt. equivalence *)

  (* cNRAEnvID *)
  Global Instance proper_cNRAEnvID : Proper nraenv_core_eq cNRAEnvID.
  Proof.
    unfold Proper, respectful, nraenv_core_eq.
    reflexivity.
  Qed.

  (* cNRAEnvConst *)
  Global Instance proper_cNRAEnvConst : Proper (eq ==> nraenv_core_eq) cNRAEnvConst.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; intros.
    rewrite H; reflexivity.
  Qed.

  (* cNRAEnvBinOp *)
  Global Instance proper_cNRAEnvBinop : Proper (binary_op_eq ==> nraenv_core_eq ==> nraenv_core_eq ==> nraenv_core_eq) cNRAEnvBinop.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; intros; simpl.
    generalize proper_NRABinop.
    unfold Proper, respectful, nraenv_core_eq, nra_eq; intros; simpl.
    specialize (H2 x y H).
    rewrite H0 by trivial; rewrite H1 by trivial.
    rewrite unfold_env_nra_sort by trivial; simpl.
    rewrite unfold_env_nra_sort by trivial; simpl.
    specialize (H2 (nra_of_nraenv_core y0) (nra_of_nraenv_core y0)).
    assert ((forall (h0 : list (string * string)) (c : list (string * data)),
                Forall (fun d : string * data => data_normalized h0 (snd d)) c ->
                forall x3 : data,
                  data_normalized h0 x3 ->
                  h0 ⊢ nra_of_nraenv_core y0 @ₐ x3 ⊣ c = h0 ⊢ nra_of_nraenv_core y0 @ₐ x3 ⊣ c)).
    intros; reflexivity.
    specialize (H2 H3).
    specialize (H2 (nra_of_nraenv_core y1) (nra_of_nraenv_core y1)).
    assert ((forall (h0 : list (string * string)) (c : list (string * data)),
                Forall (fun d : string * data => data_normalized h0 (snd d)) c ->
                forall x3 : data,
               data_normalized h0 x3 ->
               h0 ⊢ nra_of_nraenv_core y1 @ₐ x3 ⊣ c = h0 ⊢ nra_of_nraenv_core y1 @ₐ x3 ⊣ c)).
    intros; reflexivity.
    specialize (H2 H4).
    simpl in H2.
    apply (H2 h (rec_sort c)).
    eauto.
    eauto.
  Qed.

  (* cNRAEnvUnop *)
  Global Instance proper_cNRAEnvUnop : Proper (unary_op_eq ==> nraenv_core_eq ==> nraenv_core_eq) cNRAEnvUnop.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; simpl; intros.
    rewrite H0 by trivial.
    rewrite unfold_env_nra_sort by trivial; simpl.
    generalize (proper_NRAUnop).
    unfold Proper, respectful, nraenv_core_eq, nra_eq; simpl; intros.
    specialize (H1 x y H).
    specialize (H1 (nra_of_nraenv_core y0) (nra_of_nraenv_core y0)).
    assert ((forall (h0 : list (string * string)) (c : list (string * data)),
        Forall (fun d : string * data => data_normalized h0 (snd d)) c ->
        forall x3 : data,
                   data_normalized h0 x3 ->
               h0 ⊢ nra_of_nraenv_core y0 @ₐ x3 ⊣ c = h0 ⊢ nra_of_nraenv_core y0 @ₐ x3 ⊣ c)).
    intros; reflexivity.
    specialize (H1 H2).
    apply (H1 h).
    eauto.
    eauto.
  Qed.

  Hint Resolve data_normalized_dcoll_in.

  (* cNRAEnvMap *)
  Global Instance proper_cNRAEnvMap : Proper (nraenv_core_eq ==> nraenv_core_eq ==> nraenv_core_eq) cNRAEnvMap.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; simpl; intros.
    rewrite H0 by trivial.
    rewrite unfold_env_nra_sort by trivial; simpl.
    case_eq (nra_eval h (rec_sort c) (nra_of_nraenv_core y0) (nra_context_data env x1)); simpl; trivial.
    destruct d; try reflexivity; simpl; intros.
    f_equal. apply lift_map_ext; intros.
    apply H; eauto.
  Qed.

  (* cNRAEnvMapProduct *)
  Global Instance proper_cNRAEnvMapProduct : Proper (nraenv_core_eq ==> nraenv_core_eq ==> nraenv_core_eq) cNRAEnvMapProduct.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; simpl; intros.
    rewrite H0 by trivial.
    case_eq (h ⊢ₑ y0 @ₑ x1 ⊣ c;env); try reflexivity; simpl.
    destruct d; try reflexivity; simpl; intros.
    f_equal.
    apply omap_product_ext; intros.
    apply H; eauto.
  Qed.

  (* cNRAEnvProduct *)
  Global Instance proper_cNRAEnvProduct : Proper (nraenv_core_eq ==> nraenv_core_eq ==> nraenv_core_eq) cNRAEnvProduct.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; simpl; intros.
    rewrite H by trivial; rewrite H0 by trivial.
    rewrite unfold_env_nra_sort by trivial; simpl.
    rewrite unfold_env_nra_sort by trivial; simpl.
    generalize proper_NRAProduct.
    unfold Proper, respectful, nra_eq; simpl; intros.
    specialize (H1 (nra_of_nraenv_core y) (nra_of_nraenv_core y)).
    assert ((forall (h0 : list (string * string)) (c : list (string * data)),
        Forall (fun d : string * data => data_normalized h0 (snd d)) c ->
        forall x3 : data,
               data_normalized h0 x3 ->
               h0 ⊢ nra_of_nraenv_core y @ₐ x3 ⊣ c = h0 ⊢ nra_of_nraenv_core y @ₐ x3 ⊣ c))
      by (intros; reflexivity).
    assert ((forall (h0 : list (string * string)) (c : list (string * data)),
        Forall (fun d : string * data => data_normalized h0 (snd d)) c ->
        forall x3 : data,
               data_normalized h0 x3 ->
               h0 ⊢ nra_of_nraenv_core y0 @ₐ x3 ⊣ c = h0 ⊢ nra_of_nraenv_core y0 @ₐ x3 ⊣ c))
      by (intros; reflexivity).
    specialize (H1 H2 (nra_of_nraenv_core y0) (nra_of_nraenv_core y0) H3).
    apply (H1 h); eauto.      
  Qed.

  (* cNRAEnvSelect *)
  Global Instance proper_cNRAEnvSelect : Proper (nraenv_core_eq ==> nraenv_core_eq ==> nraenv_core_eq) cNRAEnvSelect.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; intros; simpl.
    rewrite H0 by trivial.
    case_eq (h ⊢ₑ y0 @ₑ x1 ⊣ c;env); intros; trivial.
    destruct d; try reflexivity; simpl.
    f_equal.
    apply lift_filter_ext; intros.
    rewrite H; eauto.
  Qed.

  (* cNRAEnvDefault *)
  Global Instance proper_cNRAEnvDefault : Proper (nraenv_core_eq ==> nraenv_core_eq ==> nraenv_core_eq) cNRAEnvDefault.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; simpl; intros.
    rewrite H by trivial; rewrite H0 by trivial.
    rewrite unfold_env_nra_sort by trivial; simpl.
    rewrite unfold_env_nra_sort by trivial; simpl.
    generalize proper_NRADefault.
    unfold Proper, respectful, nraenv_core_eq, nra_eq; simpl; intros.
    specialize (H1 (nra_of_nraenv_core y) (nra_of_nraenv_core y)).
    assert ((forall (h0 : list (string * string)) (c : list (string * data)),
        Forall (fun d : string * data => data_normalized h0 (snd d)) c ->
        forall x3 : data,
               data_normalized h0 x3 ->
               h0 ⊢ nra_of_nraenv_core y @ₐ x3 ⊣ c = h0 ⊢ nra_of_nraenv_core y @ₐ x3 ⊣ c)).
    intros; reflexivity.
    specialize (H1 H2).
    specialize (H1 (nra_of_nraenv_core y0) (nra_of_nraenv_core y0)).
    assert ((forall (h0 : list (string * string)) (c : list (string * data)),
        Forall (fun d : string * data => data_normalized h0 (snd d)) c ->
        forall x3 : data,
               data_normalized h0 x3 ->
               h0 ⊢ nra_of_nraenv_core y0 @ₐ x3 ⊣ c = h0 ⊢ nra_of_nraenv_core y0 @ₐ x3 ⊣ c)).
    intros; reflexivity.
    specialize (H1 H3).
    apply (H1 h); eauto.
  Qed.

  (* cNRAEnvEither *)
  Global Instance proper_cNRAEnvEither : Proper (nraenv_core_eq ==> nraenv_core_eq ==> nraenv_core_eq) cNRAEnvEither.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; intros; simpl.
    destruct x1; trivial; inversion dn_x; subst; eauto.
  Qed.

  (* cNRAEnvEitherConcat *)
  Global Instance proper_cNRAEnvEitherConcat : Proper (nraenv_core_eq ==> nraenv_core_eq ==> nraenv_core_eq) cNRAEnvEitherConcat.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; intros; simpl.
    rewrite H,H0 by trivial. repeat match_destr.
  Qed.

  (* cNRAEnvApp *)
  Global Instance proper_cNRAEnvApp : Proper (nraenv_core_eq ==> nraenv_core_eq ==> nraenv_core_eq) cNRAEnvApp.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; intros; simpl.
    rewrite H0 by trivial.
    case_eq (h ⊢ₑ y0 @ₑ x1 ⊣ c;env); intros; trivial; simpl.
    eauto.
  Qed.

  (* cNRAEnvGetConstant *)
  Global Instance proper_cNRAEnvGetConstant s : Proper (nraenv_core_eq) (cNRAEnvGetConstant s).
  Proof.
    unfold Proper, respectful, nraenv_core_eq; intros; simpl.
    reflexivity.
  Qed.

  (* cNRAEnvEnv *)
  Global Instance proper_cNRAEnvEnv : Proper (nraenv_core_eq) cNRAEnvEnv.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; intros; simpl.
    reflexivity.
  Qed.

  (* cNRAEnvAppEnv *)
  Global Instance proper_cNRAEnvAppEnv : Proper (nraenv_core_eq ==> nraenv_core_eq ==> nraenv_core_eq) cNRAEnvAppEnv.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; intros; simpl.
    rewrite H0 by trivial.
    case_eq (h ⊢ₑ y0 @ₑ x1 ⊣ c;env); intros; simpl; trivial.
    apply H; eauto.
  Qed.

  (* cNRAEnvMapEnv *)
  Global Instance proper_cNRAEnvMapEnv : Proper (nraenv_core_eq ==> nraenv_core_eq) cNRAEnvMapEnv.
  Proof.
    unfold Proper, respectful, nraenv_core_eq; intros; simpl.
    destruct env; try reflexivity; simpl.
    f_equal.
    apply lift_map_ext; intros.
    eauto.
  Qed.

  Lemma nraenv_core_of_nra_proper : Proper (nra_eq ==> nraenv_core_eq) nraenv_core_of_nra.
  Proof.
    unfold Proper, respectful, nra_eq, nraenv_core_eq.
    intros.
    repeat rewrite <- nraenv_core_eval_of_nra.
    auto.
  Qed.
  
  Notation "X ≡ₑ Y" := (nraenv_core_eq X Y) (at level 90).

  
  
  Lemma nraenv_core_of_nra_proper_inv x y :
    (nraenv_core_of_nra x ≡ₑ nraenv_core_of_nra y)%nraenv_core ->
    (x ≡ₐ y)%nra.
  Proof.
    unfold nra_eq, nraenv_core_eq.
    intros.
    assert (eq1:forall (h : list (string * string))
                       (c:list (string *data)),
                  Forall (fun d : string * data => data_normalized h (snd d)) c ->
                  forall (env:data),
                  data_normalized h env ->
                  forall (x0 : data),
                  data_normalized h x0 ->
                  (h ⊢ (nra_of_nraenv_core (nraenv_core_of_nra x)) @ₐ (nra_context_data env x0) ⊣ c)%nra =
                  (h ⊢ (nra_of_nraenv_core (nraenv_core_of_nra y)) @ₐ (nra_context_data env x0) ⊣ c)%nra ).
    { intros. repeat rewrite <- unfold_env_nra; trivial. auto. }
    assert (eq2:forall (h : list (string * string))
                       (x0 : data),
                  Forall (fun d : string * data => data_normalized h (snd d)) c ->
                  data_normalized h x0 ->
                  h ⊢ nraenv_core_deenv_nra (nraenv_core_of_nra x) @ₐ x0 ⊣ c =
                  h ⊢ nraenv_core_deenv_nra (nraenv_core_of_nra y) @ₐ x0 ⊣ c).
    { intros.
      assert (Forall (fun d : string * data => data_normalized h0 (snd d)) c).
      eauto.
      specialize (eq1 h0 c H2 dunit (dnunit _) x1 H1 ).
      do 2 rewrite nraenv_core_is_nra_deenv in eq1 by
          apply nraenv_core_of_nra_is_nra; trivial.
    }
    specialize (eq2 h x0).
    repeat rewrite nraenv_core_deenv_nra_of_nra in eq2.
    auto.
  Qed.

  Lemma nra_of_nraenv_core_proper_inv x y :
    (nra_of_nraenv_core x ≡ₐ nra_of_nraenv_core y)%nra ->
    (x ≡ₑ y)%nraenv_core.
  Proof.
    unfold Proper, respectful; intros.
    (* apply nraenv_core_of_nra_proper in H. *)
    unfold nra_eq, nraenv_core_eq in *.
    intros.
    specialize (H h c dn_c (nra_context_data env x0)).
    repeat rewrite <- unfold_env_nra in H by trivial.
    auto.
  Qed.

  Definition nraenv_core_always_ensures (P:data->Prop) (q:nraenv_core) :=
    forall
      (h:list(string*string))
      (c:list (string*data))
      (dn_c:Forall (fun d => data_normalized h (snd d)) c)
      (env:data)
      (dn_env:data_normalized h env)
      (x:data)
      (dn_x:data_normalized h x)
      (d:data),
      h ⊢ₑ q @ₑ x ⊣ c;env = Some d -> P d.

End cNRAEnvEq.

Notation "X ≡ₑ Y" := (nraenv_core_eq X Y) (at level 90) : nraenv_core_scope.                             (* ≡ = \equiv *)

