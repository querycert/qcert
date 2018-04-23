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

Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import List.
Require Import String.
Require Import Utils.
Require Import CommonSystem.
Require Import cNRAEnv.
Require Import TcNRAEnvEq.
Require Import NRAEnv.
Require Import NRAEnvEq.
Require Import TNRAEnv.

Section TNRAEnvEq.
  Local Open Scope nraenv_scope.
  
  (* Equivalence relation between *typed* algebraic plans.  Two
     well-typed plans are equivalent iff they return the same value
     for every well-typed input.  *)

  Definition typed_nraenv {m:basic_model} τc τenv τin τout := {op:nraenv|op ▷ₓ τin >=> τout ⊣ τc;τenv}.

  Definition tnraenv_eq {m:basic_model} {τc τenv τin τout} (op1 op2:typed_nraenv τc τenv τin τout) : Prop :=
    forall (x:data) c (env: data)
           (dt_x:x ▹ τin)
           (dt_c:bindings_type c τc)
           (dt_env:env ▹ τenv),
        brand_relation_brands ⊢ (proj1_sig op1) @ₓ x ⊣ c;env
        = brand_relation_brands ⊢ (proj1_sig op2) @ₓ x ⊣ c;env.

  Global Instance tnraenv_equiv {m:basic_model} {τc} {τenv τin τout:rtype} : Equivalence (@tnraenv_eq m τc τenv τin τout).
  Proof.
    constructor.
    - unfold Reflexive, tnraenv_eq; intros.
      reflexivity.
    - unfold Symmetric, tnraenv_eq; intros.
      rewrite (H x0 c env dt_x dt_c dt_env); reflexivity.
    - unfold Transitive, tnraenv_eq; intros.
      intros; rewrite (H x0 c env dt_x dt_c dt_env); rewrite (H0 x0 c env dt_x dt_c dt_env); reflexivity.
  Qed.

  Notation "t1 ⇝ₓ t2 ⊣ τc ; tenv" := (typed_nraenv τc tenv t1 t2) (at level 80).
  Notation "X ≡τₓ Y" := (tnraenv_eq X Y) (at level 80).               (* ≡ = \equiv *)

  Hint Resolve data_type_normalized.
  Hint Resolve bindings_type_Forall_normalized.

  Lemma nraenv_eq_impl_tnraenv_eq {m:basic_model} {τc τenv τin τout} (op1 op2: τin ⇝ₓ τout ⊣ τc;τenv) :
    `op1 ≡ₓ `op2 -> op1 ≡τₓ op2.
  Proof.
    unfold tnraenv_eq, nraenv_eq; intros.
    eapply H; eauto.
  Qed.

  Lemma nraenv_eq_pf_irrel {m:basic_model} {op} {τin τout τc τenv} (pf1 pf2: op ▷ₓ τin >=> τout ⊣ τc;τenv) :
    tnraenv_eq (exist _ op pf1) (exist _ op pf2).
  Proof.
    red; intros; simpl.
    reflexivity.
  Qed.

  (* A different kind of equivalence for rewrites *)
  Context {m:basic_model}.

  Definition tnraenv_rewrites_to (op1 op2:nraenv) : Prop :=
    forall τc (τenv τin τout:rtype),
      op1 ▷ₓ τin >=> τout ⊣ τc;τenv ->
                              (op2 ▷ₓ τin >=> τout ⊣ τc;τenv)
                              /\ (forall (x:data) c
                                         env
                                         (dt_x:x ▹ τin)
                                         (dt_c:bindings_type c τc)
                                         (dt_env:env ▹ τenv),
                                    brand_relation_brands ⊢ op1 @ₓ x ⊣ c;env
                                 = brand_relation_brands ⊢ op2 @ₓ x ⊣ c;env).
  
  Notation "op1 ⇒ₓ op2" := (@tnraenv_rewrites_to op1 op2) (at level 80).
  
  Lemma rewrites_typed_with_untyped (op1 op2:nraenv) :
    op1 ≡ₓ op2 ->
    (forall {τc} {τenv τin τout:rtype}, op1 ▷ₓ τin >=> τout ⊣ τc;τenv -> op2 ▷ₓ τin >=> τout ⊣ τc;τenv)
    -> op1 ⇒ₓ op2.
  Proof.
    intros.
    unfold tnraenv_rewrites_to; simpl; intros.
    split; eauto.
  Qed.

  (* Rewrite implies type-based equivalence! *)
  Lemma talg_rewrites_eq_is_typed_eq {τc} {τenv τin τout:rtype} (op1 op2:typed_nraenv τc τenv τin τout):
    (`op1 ⇒ₓ `op2) -> @tnraenv_eq m τc τenv τin τout op1 op2.
  Proof.
    unfold tnraenv_rewrites_to, tnraenv_eq; intros.
    dependent induction op1.
    dependent induction op2; simpl in *.
    elim (H τc τenv τin τout); clear H; intros.
    apply (H0 x1 c env dt_x dt_c dt_env).
    assumption.
  Qed.

  (** Thanks to shallow semantics, lifting between nraenv_core and nraenv is easy *)
  Section eq_lift.
    Open Scope nraenv_core_scope.

    Lemma lift_tnraenv_core_eq_to_tnraenv_eq_r (q1 q2:nraenv_core) :
      q1 ⇒ q2 -> (nraenv_core_to_nraenv q1) ⇒ₓ (nraenv_core_to_nraenv q2).
    Proof.
      unfold tnraenv_rewrites_to.
      unfold tnraenv_core_rewrites_to.
      intros.
      unfold nraenv_type in *.
      unfold nraenv_eval in *.
      rewrite nraenv_roundtrip.
      rewrite nraenv_roundtrip.
      rewrite nraenv_roundtrip in H0.
      auto.
    Qed.

    Lemma lift_tnraenv_core_eq_to_tnraenv_eq_l (q1 q2:nraenv_core) :
      (nraenv_core_to_nraenv q1) ⇒ₓ (nraenv_core_to_nraenv q2) -> q1 ⇒ q2.
    Proof.
      unfold tnraenv_rewrites_to.
      unfold tnraenv_core_rewrites_to.
      intros.
      unfold nraenv_type in *.
      unfold nraenv_eval in *.
      rewrite nraenv_roundtrip in H.
      rewrite nraenv_roundtrip in H.
      specialize (H _ _ _ _ H0); intros.
      assumption.
    Qed.

    Lemma lift_tnraenv_core_eq_to_tnraenv_eq (q1 q2:nraenv_core) :
      q1 ⇒ q2 <-> (nraenv_core_to_nraenv q1) ⇒ₓ (nraenv_core_to_nraenv q2).
    Proof.
      split.
      apply lift_tnraenv_core_eq_to_tnraenv_eq_r.
      apply lift_tnraenv_core_eq_to_tnraenv_eq_l.
    Qed.

    Lemma lift_tnraenv_eq_to_tnraenv_core_eq_r (q1 q2:nraenv) :
      q1 ⇒ₓ q2 -> (nraenv_to_nraenv_core q1) ⇒ (nraenv_to_nraenv_core q2).
    Proof.
      unfold tnraenv_rewrites_to.
      unfold tnraenv_core_rewrites_to.
      intros.
      unfold nraenv_eval in *.
      unfold nraenv_type in *.
      elim (H _ _ _ _ H0); intros; clear H.
      split; assumption.
    Qed.
  
    Lemma lift_tnraenv_eq_to_tnraenv_core_eq_l (q1 q2:nraenv) :
      (nraenv_to_nraenv_core q1) ⇒ (nraenv_to_nraenv_core q2) -> q1 ⇒ₓ q2.
    Proof.
      unfold tnraenv_rewrites_to.
      unfold tnraenv_core_rewrites_to.
      intros.
      unfold nraenv_eval in *.
      unfold nraenv_type in *.
      elim (H _ _ _ _ H0); intros; clear H.
      split; assumption.
    Qed.
  
    Lemma lift_tnraenv_eq_to_tnraenv_core_eq (q1 q2:nraenv) :
      q1 ⇒ₓ q2 <-> (nraenv_to_nraenv_core q1) ⇒ (nraenv_to_nraenv_core q2).
    Proof.
      split.
      apply lift_tnraenv_eq_to_tnraenv_core_eq_r.
      apply lift_tnraenv_eq_to_tnraenv_core_eq_l.
    Qed.
  End eq_lift.

  (****************
   * Proper stuff *
   ****************)

  Global Instance  tnraenv_rewrites_to_pre : PreOrder tnraenv_rewrites_to.
  Proof.
    constructor; red; intros.
    - unfold tnraenv_rewrites_to; intros.
      split; try assumption; intros.
      reflexivity.
    - unfold tnraenv_rewrites_to in *; intros.
      specialize (H τc τenv τin τout H1).
      elim H; clear H; intros.
      specialize (H0 τc τenv τin τout H).
      elim H0; clear H0; intros.
      split; try assumption; intros.
      rewrite (H2 x0 c env); try assumption.
      rewrite (H3 x0 c env); try assumption.
      reflexivity.
  Qed.

  (* NRAEnvID *)

  Global Instance nraenv_id_tproper:
    Proper tnraenv_rewrites_to NRAEnvID.
  Proof.
    unfold Proper, respectful; intros.
    reflexivity.
  Qed.

  (* NRAEnvConst *)

  Global Instance nraenv_const_tproper:
    Proper (eq ==> tnraenv_rewrites_to) NRAEnvConst.
  Proof.
    unfold Proper, respectful; intros.
    rewrite H; reflexivity.
  Qed.

  (* NRAEnvBinop *)

  Global Instance nraenv_binop_tproper:
    Proper (eq ==> tnraenv_rewrites_to
               ==> tnraenv_rewrites_to
               ==> tnraenv_rewrites_to) NRAEnvBinop.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H1.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H; rewrite H0; rewrite H1.
    reflexivity.
  Qed.
  
  (* NRAEnvUnop *)

  Global Instance nraenv_unop_tproper :
    Proper (eq ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvUnop.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H; rewrite H0.
    reflexivity.
  Qed.

  (* NRAEnvMap *)

  Global Instance nraenv_map_tproper :
    Proper (tnraenv_rewrites_to ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvMap.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H; rewrite H0.
    reflexivity.
  Qed.

  (* NRAEnvMapProduct *)
  
  Global Instance nraenv_mapconcat_tproper :
    Proper (tnraenv_rewrites_to ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvMapProduct.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H; rewrite H0.
    reflexivity.
  Qed.

  (* NRAEnvProduct *)
  
  Global Instance nraenv_product_tproper :
    Proper (tnraenv_rewrites_to ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvProduct.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H; rewrite H0.
    reflexivity.
  Qed.
  
  (* NRAEnvSelect *)
  
  Global Instance nraenv_select_tproper :
    Proper (tnraenv_rewrites_to ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvSelect.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H; rewrite H0.
    reflexivity.
  Qed.

  (* NRAEnvDefault *)

  Global Instance nraenv_default_tproper :
    Proper (tnraenv_rewrites_to ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvDefault.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H; rewrite H0.
    reflexivity.
  Qed.

  (* NRAEnvEither *)
  Global Instance nraenv_either_tproper :
    Proper (tnraenv_rewrites_to ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvEither.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H; rewrite H0.
    reflexivity.
  Qed.

  (* NRAEnvEitherConcat *)
  Global Instance nraenv_eitherconcat_tproper :
    Proper (tnraenv_rewrites_to ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvEitherConcat.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H; rewrite H0.
    reflexivity.
  Qed.
  
  (* NRAEnvApp *)

  Global Instance nraenv_app_tproper :
    Proper (tnraenv_rewrites_to ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvApp.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H; rewrite H0.
    reflexivity.
  Qed.

  (* NRAEnvEnv *)

  Global Instance nraenv_env_tproper:
    Proper tnraenv_rewrites_to NRAEnvEnv.
  Proof.
    unfold Proper, respectful; intros.
    reflexivity.
  Qed.

  (* NRAEnvAppEnv *)

  Global Instance nraenv_appenv_tproper :
    Proper (tnraenv_rewrites_to ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvAppEnv.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H; rewrite H0.
    reflexivity.
  Qed.

  (* NRAEnvMapEnv *)

  Global Instance nraenv_mapenv_tproper :
    Proper (tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvMapEnv.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    simpl.
    rewrite H.
    reflexivity.
  Qed.

  (* NRAEnvFlatMap *)

  Global Instance nraenv_flatmap_tproper :
    Proper (tnraenv_rewrites_to ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvFlatMap.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    simpl.
    unfold macro_cNRAEnvFlatMap.
    rewrite H; rewrite H0; reflexivity.
  Qed.
    
  (* NRAEnvJoin *)

  Global Instance nraenv_join_tproper :
    Proper (tnraenv_rewrites_to
              ==> tnraenv_rewrites_to
              ==> tnraenv_rewrites_to
              ==> tnraenv_rewrites_to) NRAEnvJoin.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H1.
    simpl.
    unfold macro_cNRAEnvJoin.
    rewrite H; rewrite H0; rewrite H1; reflexivity.
  Qed.
    
  (* NRAEnvNaturalJoin *)

  Global Instance nraenv_natural_join_tproper :
    Proper (tnraenv_rewrites_to
              ==> tnraenv_rewrites_to
              ==> tnraenv_rewrites_to) NRAEnvNaturalJoin.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    simpl.
    unfold macro_cNRAEnvNaturalJoin.
    rewrite H; rewrite H0; reflexivity.
  Qed.
    
  (* NRAEnvProject *)

  Global Instance nraenv_project_tproper :
    Proper (eq ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvProject.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H0.
    simpl.
    unfold macro_cNRAEnvProject.
    rewrite H; rewrite H0; reflexivity.
  Qed.
    
  (* NRAEnvGroupBy *)

  Global Instance nraenv_group_by_tproper :
    Proper (eq ==> eq ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvGroupBy.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H1.
    simpl.
    unfold macro_cNRAEnvGroupBy.
    rewrite H; rewrite H0; rewrite H1; reflexivity.
  Qed.

  (* NRAEnvUnnest *)

  Global Instance nraenv_unnest_tproper :
    Proper (eq ==> eq ==> tnraenv_rewrites_to ==> tnraenv_rewrites_to) NRAEnvUnnest.
  Proof.
    unfold Proper, respectful; intros.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq.
    rewrite lift_tnraenv_eq_to_tnraenv_core_eq in H1.
    simpl.
    unfold macro_cNRAEnvUnnest.
    rewrite H; rewrite H0; rewrite H1; reflexivity.
  Qed.

End TNRAEnvEq.

Notation "op1 ⇒ₓ op2" := (tnraenv_rewrites_to op1 op2) (at level 80) : nraenv_scope.
Notation "h ⊧ t1 ⇝ₓ t2 ⊣ c ; tenv" := (@typed_nraenv h c tenv t1 t2) (at level 80) : nraenv_scope.
Notation "X ≡τₓ Y" := (tnraenv_eq X Y) (at level 80) : nraenv_scope.               (* ≡ = \equiv *)
Notation "X ≡τ'ₓ Y" := (tnraenv_eq (exist _ _ X) (exist _ _ Y)) (at level 80) : nraenv_scope.               (* ≡ = \equiv *)

