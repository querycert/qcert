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
Require Import String.
Require Import List.
Require Import Arith.
Require Import Utils.
Require Import CommonSystem.
Require Import cNNRCSystem.
Require Import NNRC.
Require Import NNRCEq.
Require Import TNNRC.

Section TNNRCEq.
  (* A type-safe equivalence for rewrites *)

  Context {m:basic_model}.

  Definition tnnrc_rewrites_to (e1 e2:nnrc) : Prop :=
    forall (τcenv τenv : tbindings) (τout:rtype),
      nnrc_type τcenv τenv e1 τout ->
      (nnrc_type τcenv τenv e2 τout)
      /\ (forall (cenv:bindings),
          forall (env:bindings),
             bindings_type cenv τcenv ->
             bindings_type env τenv ->
             @nnrc_eval _ brand_relation_brands cenv env e1
             = @nnrc_eval _ brand_relation_brands cenv env e2).

  Notation "e1 ⇒ᶜ e2" := (tnnrc_rewrites_to e1 e2) (at level 80).

  Open Scope nnrc_scope.

  Lemma data_normalized_bindings_type_map env τenv :
    bindings_type env τenv ->
    Forall (data_normalized brand_relation_brands) (map snd env).
  Proof.
    rewrite Forall_map.
    apply bindings_type_Forall_normalized.
  Qed.

  Hint Resolve data_normalized_bindings_type_map.
  
  Lemma nnrc_rewrites_typed_with_untyped (e1 e2:nnrc) :
    e1 ≡ᶜ e2 ->
    (forall {τcenv: tbindings}
            {τenv: tbindings}
            {τout:rtype}, nnrc_type τcenv τenv e1 τout -> nnrc_type τcenv τenv e2 τout)
    -> e1 ⇒ᶜ e2.
  Proof.
    intros.
    unfold tnnrc_rewrites_to; simpl; intros.
    split; auto 2; intros.
    apply H; eauto.
  Qed.

  (****************
   * Proper stuff *
   ****************)

  Hint Constructors nnrc_core_type.
  Hint Constructors unary_op_type.
  Hint Constructors binary_op_type.

  Global Instance tnnrc_rewrites_to_pre : PreOrder tnnrc_rewrites_to.
  Proof.
    constructor; red; intros.
    - unfold tnnrc_rewrites_to; intros.
      split; try assumption; intros.
      reflexivity.
    - unfold tnnrc_rewrites_to in *; intros.
      specialize (H τcenv τenv τout H1).
      elim H; clear H; intros.
      specialize (H0 τcenv τenv τout H).
      elim H0; clear H0; intros.
      split; try assumption; intros.
      rewrite (H2 cenv env); try assumption.
      rewrite (H3 cenv env); try assumption.
      reflexivity.
  Qed.
  (* NNRCGetConstant *)

  Global Instance tproper_NNRCGetConstant:
    Proper (eq ==> tnnrc_rewrites_to) NNRCGetConstant.
  Proof.
    unfold Proper, respectful, tnnrc_rewrites_to; intros.
    rewrite <- H.
    split; try assumption.
    intros; reflexivity.
  Qed.

  (* NNRCVar *)

  Global Instance tproper_NNRCVar:
    Proper (eq ==> tnnrc_rewrites_to) NNRCVar.
  Proof.
    unfold Proper, respectful, tnnrc_rewrites_to; intros.
    rewrite <- H.
    split; try assumption.
    intros; reflexivity.
  Qed.
  
  (* NNRCConst *)

  Global Instance tproper_NNRCConst:
    Proper (eq ==> tnnrc_rewrites_to) NNRCConst.
  Proof.
    unfold Proper, respectful, tnnrc_rewrites_to; intros.
    rewrite <- H.
    split; try assumption.
    intros; reflexivity.
  Qed.

  (* NNRCBinop *)

  Global Instance tproper_NNRCBinop:
    Proper (eq ==> tnnrc_rewrites_to
               ==> tnnrc_rewrites_to
               ==> tnnrc_rewrites_to) NNRCBinop.
  Proof.
    unfold Proper, respectful, tnnrc_rewrites_to; intros.
    rewrite H in *; clear H.
    inversion H2; clear H2; subst.
    econstructor; eauto.
    specialize (H0 τcenv τenv τ₁ H8); elim H0; clear H0 H8; intros.
    specialize (H1 τcenv τenv τ₂ H9); elim H1; clear H1 H9; intros.
    econstructor; eauto; intros.
    intros.
    specialize (H0 τcenv τenv τ₁ H8); elim H0; clear H0 H8; intros.
    specialize (H1 τcenv τenv τ₂ H9); elim H1; clear H1 H9; intros.
    unfold nnrc_eval in *.
    simpl.
    rewrite (H3 cenv env H H2); rewrite (H4 cenv env H H2); reflexivity.
  Qed.
  
  (* NNRCUnop *)

  Global Instance tproper_NNRCUnop :
    Proper (eq ==> tnnrc_rewrites_to ==> tnnrc_rewrites_to) NNRCUnop.
  Proof.
    unfold Proper, respectful, tnnrc_rewrites_to; intros.
    rewrite H in *; clear H.
    inversion H1; clear H1; subst.
    econstructor; eauto.
    econstructor; eauto.
    specialize (H0 τcenv τenv τ₁ H6); elim H0; clear H0 H6; intros; assumption.
    intros.
    specialize (H0 τcenv τenv τ₁ H6); elim H0; clear H0 H6; intros.
    unfold nnrc_eval in *.
    simpl. rewrite (H2 cenv env H H1); reflexivity.
  Qed.

  (* NNRCLet *)

  Global Instance tproper_NNRCLet :
    Proper (eq ==> tnnrc_rewrites_to ==> tnnrc_rewrites_to ==> tnnrc_rewrites_to) NNRCLet.
  Proof.
    unfold Proper, respectful, tnnrc_rewrites_to; intros.
    unfold nnrc_eval,nnrc_type in *.
    inversion H2; clear H2; subst.
    specialize (H0 τcenv τenv τ₁ H8); elim H0; clear H0 H8; intros.
    specialize (H1 τcenv ((y, τ₁) :: τenv) τout H9); elim H1; clear H1 H9; intros.
    econstructor; eauto.
    econstructor; eauto.
    intros; simpl.
    rewrite (H0 cenv env H3 H4).
    case_eq (nnrc_core_eval brand_relation_brands cenv env (nnrc_to_nnrc_base y0));
      intros; try reflexivity.
    rewrite (H2 cenv ((y, d) :: env) H3); try reflexivity.
    unfold bindings_type.
    apply Forall2_cons; try assumption.
    simpl; split; try reflexivity.
    generalize (@typed_nnrc_yields_typed_data _ τcenv τ₁ cenv env τenv y0 H3 H4 H); intros.
    elim H6; intros.
    elim H7; clear H7; intros.
    unfold nnrc_eval,nnrc_type in *.
    rewrite H5 in H7.
    inversion H7; assumption.
  Qed.

  (* NNRCFor *)

  Lemma dcoll_wt (l:list data) (τ:rtype) (τcenv τenv:tbindings) (cenv env:bindings) (e:nnrc):
    bindings_type cenv τcenv ->
    bindings_type env τenv ->
    nnrc_core_type τcenv τenv e (Coll τ) ->
    nnrc_core_eval brand_relation_brands cenv env e = Some (dcoll l) ->
    forall x:data, In x l -> (data_type x τ).
  Proof.
    intros.
    generalize (@typed_nnrc_core_yields_typed_data _ τcenv (Coll τ) cenv env τenv e H H0 H1); intros.
    elim H4; clear H4; intros.
    elim H4; clear H4; intros.
    rewrite H4 in H2.
    inversion H2; clear H2.
    subst.
    dependent induction H5.
    rtype_equalizer.
    subst.
    rewrite Forall_forall in H2.
    apply (H2 x0 H3).
  Qed.

  Global Instance tproper_NNRCFor :
    Proper (eq ==> tnnrc_rewrites_to ==> tnnrc_rewrites_to ==> tnnrc_rewrites_to) NNRCFor.
  Proof.
    unfold Proper, respectful, tnnrc_rewrites_to; intros.
    inversion H2; clear H2; subst.
    specialize (H0 τcenv τenv (Coll τ₁) H8); elim H0; clear H0 H8; intros.
    specialize (H1 τcenv ((y, τ₁) :: τenv) τ₂ H9); elim H1; clear H1 H9; intros.
    econstructor; eauto.
    econstructor; eauto.
    intros; simpl.
    unfold nnrc_eval,nnrc_type in *; simpl.
    rewrite (H0 cenv env H3 H4).
    case_eq (nnrc_core_eval brand_relation_brands cenv env (nnrc_to_nnrc_base y0));
      intros; try reflexivity.
    destruct d; try reflexivity.
    assert (forall x, In x l -> (data_type x τ₁))
      by
        (apply (dcoll_wt l τ₁ τcenv τenv cenv env (nnrc_to_nnrc_base y0)); assumption).
    clear H5 H.
    induction l; try reflexivity.
    simpl in *.
    assert (forall x : data, In x l -> data_type x τ₁)
      by (intros; apply (H6 x); right; assumption).
    specialize (IHl H); clear H.
    rewrite (H2 cenv ((y, a) :: env) H3).
    destruct (nnrc_core_eval brand_relation_brands cenv ((y, a) :: env) (nnrc_to_nnrc_base y1)); try reflexivity.
    - destruct ((lift_map (fun d1 : data => nnrc_core_eval brand_relation_brands cenv ((y, d1) :: env) (nnrc_to_nnrc_base x1)) l));
      destruct ((lift_map (fun d1 : data => nnrc_core_eval brand_relation_brands cenv ((y, d1) :: env) (nnrc_to_nnrc_base y1)) l));
      simpl in *; try congruence.
    - unfold bindings_type.
      apply Forall2_cons; try assumption.
      simpl; split; try reflexivity.
      apply (H6 a); left; reflexivity.
  Qed.
    
  (* NNRCIf *)
  Global Instance tproper_NNRCIf :
    Proper (tnnrc_rewrites_to ==> tnnrc_rewrites_to
                              ==> tnnrc_rewrites_to
                              ==> tnnrc_rewrites_to) NNRCIf.
  Proof.
    unfold Proper, respectful, tnnrc_rewrites_to; intros.
    inversion H2; clear H2; subst.
    specialize (H τcenv τenv Bool H7); elim H; clear H H7; intros.
    specialize (H0 τcenv τenv τout H9); elim H0; clear H0 H9; intros.
    specialize (H1 τcenv τenv τout H10); elim H1; clear H1 H10; intros.
    econstructor; eauto.
    econstructor; eauto.
    intros; simpl.
    unfold nnrc_eval,nnrc_type in *; simpl.
    rewrite (H2 cenv env H5 H6). rewrite (H3 cenv env H5 H6). rewrite (H4 cenv env H5 H6).
    reflexivity.
  Qed.

  (* NNRCEither *)
  Global Instance tproper_NNRCEither :
    Proper (tnnrc_rewrites_to ==> eq ==> tnnrc_rewrites_to
                              ==> eq ==> tnnrc_rewrites_to
                              ==> tnnrc_rewrites_to) NNRCEither.
  Proof.
    unfold Proper, respectful, tnnrc_rewrites_to; intros.
    unfold nnrc_eval,nnrc_type in *; simpl.
    subst.
    simpl in H4.
    inversion H4; clear H4; subst.
    destruct (H _ _ _ H10).
    destruct (H1 _ _ _ H11).
    destruct (H3 _ _ _ H12).
    clear H H1 H3.
    simpl.
    split; [eauto | ]; intros.
    rewrite H2; trivial.
    destruct (@typed_nnrc_core_yields_typed_data _ _ _ _ _ _ _ H H1 H0) as [?[??]].
    rewrite H3.
    apply data_type_Either_inv in H8.
    destruct H8 as [[?[??]]|[?[??]]]; subst.
    - apply (H5 _ _ H). constructor; simpl; intuition; eauto.
    - eapply (H7 _ _ H). constructor; simpl; intuition; eauto.
  Qed.

  (* NNRCGroupBy *)
  Lemma group_by_macro_eq g sl n1 n2 :
    NNRCGroupBy g sl n1 ⇒ᶜ NNRCGroupBy g sl n2
    <-> nnrc_group_by g sl n1 ⇒ᶜ nnrc_group_by g sl n2.
  Proof.
    Opaque nnrc_group_by.
    unfold tnnrc_rewrites_to; intros.
    unfold nnrc_type in *.
    unfold nnrc_eval in *.
    split.
    - simpl. auto.
    - simpl. auto.
    Transparent nnrc_group_by.
  Qed.

  Global Instance tproper_NNRCGroupBy :
    Proper (eq ==> eq ==> tnnrc_rewrites_to ==> tnnrc_rewrites_to) NNRCGroupBy.
  Proof.
    unfold Proper, respectful; intros.
    subst.
    rewrite group_by_macro_eq.
    unfold nnrc_group_by.
    rewrite H1.
    reflexivity.
  Qed.

End TNNRCEq.

Notation "e1 ⇒ᶜ e2" := (tnnrc_rewrites_to e1 e2) (at level 80).

