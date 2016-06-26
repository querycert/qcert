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

Section TNRCEq.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.
  Require Import String.
  Require Import List.
  Require Import Arith.

  Require Import Utils BasicSystem.
  Require Import NNRC TNRC.

  (* Named Nested Relational Calculus *)

  (* A different kind of equivalence for rewrites *)

  Context {m:basic_model}.

  Definition tnrc_rewrites_to (e1 e2:nrc) : Prop :=
    forall (τenv : tbindings) (τout:rtype),
      nrc_type τenv e1 τout ->
      (nrc_type τenv e2 τout) /\ (forall (env:bindings),
                                     bindings_type env τenv -> nrc_eval brand_relation_brands env e1 = nrc_eval brand_relation_brands env e2).

  Notation "e1 ⇒ᶜ e2" := (tnrc_rewrites_to e1 e2) (at level 80).

  Require Import NNRCEq.
  Open Scope nrc_scope.

  Lemma data_normalized_bindings_type_map env τenv :
    bindings_type env τenv ->
    Forall (data_normalized brand_relation_brands) (map snd env).
  Proof.
    rewrite Forall_map.
    apply bindings_type_Forall_normalized.
  Qed.

  Hint Resolve data_normalized_bindings_type_map.
  
  Lemma nrc_rewrites_typed_with_untyped (e1 e2:nrc) :
    e1 ≡ᶜ e2 ->
    (forall  {τenv: tbindings} {τout:rtype}, nrc_type τenv e1 τout -> nrc_type τenv e2 τout)
    -> e1 ⇒ᶜ e2.
  Proof.
    intros.
    unfold tnrc_rewrites_to; simpl; intros.
    split; auto 2; intros.
    apply H; eauto.
  Qed.

  (****************
   * Proper stuff *
   ****************)

  Require Import TOps.
  
  Hint Constructors nrc_type.
  Hint Constructors unaryOp_type.
  Hint Constructors binOp_type.

  Require Import ROpsEq NNRCEq.
  
  Global Instance  tnrc_rewrites_to_pre : PreOrder tnrc_rewrites_to.
  Proof.
    constructor; red; intros.
    - unfold tnrc_rewrites_to; intros.
      split; try assumption; intros.
      reflexivity.
    - unfold tnrc_rewrites_to in *; intros.
      specialize (H τenv τout H1).
      elim H; clear H; intros.
      specialize (H0 τenv τout H).
      elim H0; clear H0; intros.
      split; try assumption; intros.
      rewrite (H2 env); try assumption.
      rewrite (H3 env); try assumption.
      reflexivity.
  Qed.
  
  (* NRCVar *)

  Global Instance nrcvar_tproper:
    Proper (eq ==> tnrc_rewrites_to) NRCVar.
  Proof.
    unfold Proper, respectful, tnrc_rewrites_to; intros.
    rewrite <- H.
    split; try assumption.
    intros; reflexivity.
  Qed.
  
  (* NRCConst *)

  Global Instance nrcconst_tproper:
    Proper (eq ==> tnrc_rewrites_to) NRCConst.
  Proof.
    unfold Proper, respectful, tnrc_rewrites_to; intros.
    rewrite <- H.
    split; try assumption.
    intros; reflexivity.
  Qed.

  (* NRCBinop *)

  Global Instance nrcbinop_tproper:
    Proper (eq ==> tnrc_rewrites_to
               ==> tnrc_rewrites_to
               ==> tnrc_rewrites_to) NRCBinop.
  Proof.
    unfold Proper, respectful, tnrc_rewrites_to; intros.
    rewrite H in *; clear H.
    inversion H2; clear H2; subst.
    econstructor; eauto.
    specialize (H0  τenv τ₁ H8); elim H0; clear H0 H8; intros.
    specialize (H1  τenv τ₂ H9); elim H1; clear H1 H9; intros.
    econstructor; eauto; intros.
    intros.
    specialize (H0  τenv τ₁ H8); elim H0; clear H0 H8; intros.
    specialize (H1  τenv τ₂ H9); elim H1; clear H1 H9; intros.
    simpl.
    rewrite (H2 env H); rewrite (H3 env H); reflexivity.
  Qed.
  
  (* NRCUnop *)

  Global Instance nrcunop_tproper :
    Proper (eq ==> tnrc_rewrites_to ==> tnrc_rewrites_to) NRCUnop.
  Proof.
    unfold Proper, respectful, tnrc_rewrites_to; intros.
    rewrite H in *; clear H.
    inversion H1; clear H1; subst.
    econstructor; eauto.
    econstructor; eauto.
    specialize (H0  τenv τ₁ H6); elim H0; clear H0 H6; intros; assumption.
    intros.
    specialize (H0  τenv τ₁ H6); elim H0; clear H0 H6; intros.
    simpl. rewrite (H1 env H); reflexivity.
  Qed.

  (* NRCLet *)

  Global Instance nrclet_tproper :
    Proper (eq ==> tnrc_rewrites_to ==> tnrc_rewrites_to ==> tnrc_rewrites_to) NRCLet.
  Proof.
    unfold Proper, respectful, tnrc_rewrites_to; intros.
    inversion H2; clear H2; subst.
    specialize (H0  τenv τ₁ H8); elim H0; clear H0 H8; intros.
    specialize (H1  ((y, τ₁) :: τenv) τout H9); elim H1; clear H1 H9; intros.
    econstructor; eauto.
    intros; simpl.
    rewrite (H0 env H3).
    case_eq (nrc_eval brand_relation_brands env y0); intros; try reflexivity.
    rewrite (H2 ((y, d) :: env)); try reflexivity.
    unfold bindings_type.
    apply Forall2_cons; try assumption.
    simpl; split; try reflexivity.
    generalize (@typed_nrc_yields_typed_data _ τ₁ env τenv y0 H3 H); intros.
    elim H5; intros.
    rewrite H4 in H6.
    elim H6; clear H6; intros.
    inversion H6; assumption.
  Qed.
    
  (* NRCFor *)

  Require Import TData.
  
  Lemma dcoll_wt (l:list data) (τ:rtype) (τenv:tbindings) (env:bindings) (e:nrc):
    bindings_type env τenv ->
    nrc_type τenv e (Coll τ) ->
    nrc_eval brand_relation_brands env e = Some (dcoll l) ->
    forall x:data, In x l -> (data_type x τ).
  Proof.
    intros.
    generalize (@typed_nrc_yields_typed_data _ (Coll τ) env τenv e H H0); intros.
    elim H3; clear H3; intros.
    elim H3; clear H3; intros.
    rewrite H3 in H1.
    inversion H1; clear H1.
    subst.
    dependent induction H4.
    rtype_equalizer.
    subst.
    rewrite Forall_forall in H1.
    apply (H1 x0 H2).
  Qed.

  Global Instance nrcfor_tproper :
    Proper (eq ==> tnrc_rewrites_to ==> tnrc_rewrites_to ==> tnrc_rewrites_to) NRCFor.
  Proof.
    unfold Proper, respectful, tnrc_rewrites_to; intros.
    inversion H2; clear H2; subst.
    specialize (H0  τenv (Coll τ₁) H8); elim H0; clear H0 H8; intros.
    specialize (H1  ((y, τ₁) :: τenv) τ₂ H9); elim H1; clear H1 H9; intros.
    econstructor; eauto.
    intros; simpl.
    rewrite (H0 env H3).
    case_eq (nrc_eval brand_relation_brands env y0); intros; try reflexivity.
    destruct d; try reflexivity.
    assert (forall x, In x l -> (data_type x τ₁)) by
        (apply (dcoll_wt l τ₁ τenv env y0); assumption).
    clear H4 H.
    induction l; try reflexivity.
    simpl in *.
    assert (forall x : data, In x l -> data_type x τ₁)
      by (intros; apply (H5 x); right; assumption).
    specialize (IHl H); clear H.
    rewrite (H2 ((y, a) :: env)).
    destruct (nrc_eval brand_relation_brands ((y, a) :: env) y1); try reflexivity.
    destruct ((rmap (fun d1 : data => nrc_eval brand_relation_brands ((y, d1) :: env) x1) l)); destruct ((rmap (fun d1 : data => nrc_eval brand_relation_brands ((y, d1) :: env) y1) l)); simpl in *; try congruence.
    unfold bindings_type.
    apply Forall2_cons; try assumption.
    simpl; split; try reflexivity.
    apply (H5 a); left; reflexivity.
  Qed.
    
  (* NRCIf *)

  Global Instance nrcif_tproper :
    Proper (tnrc_rewrites_to ==> tnrc_rewrites_to
                             ==> tnrc_rewrites_to
                             ==> tnrc_rewrites_to) NRCIf.
  Proof.
    unfold Proper, respectful, tnrc_rewrites_to; intros.
    inversion H2; clear H2; subst.
    specialize (H  τenv Bool H7); elim H; clear H H7; intros.
    specialize (H0  τenv τout H9); elim H0; clear H0 H9; intros.
    specialize (H1  τenv τout H10); elim H1; clear H1 H10; intros.
    econstructor; eauto.
    intros; simpl.
    rewrite (H2 env H5). rewrite (H3 env H5). rewrite (H4 env H5).
    reflexivity.
  Qed.

  Global Instance nrceither_tproper :
    Proper (tnrc_rewrites_to ==> eq ==> tnrc_rewrites_to ==> eq ==> tnrc_rewrites_to ==> tnrc_rewrites_to) NRCEither.
  Proof.
    unfold Proper, respectful, tnrc_rewrites_to; intros.
    subst.
    inversion H4; clear H4; subst.
    destruct (H _ _ H10).
    destruct (H1 _ _ H11).
    destruct (H3 _ _ H12).
    clear H H1 H3.
    simpl.
    split; [eauto | ]; intros.
    rewrite H2; trivial.
    destruct (@typed_nrc_yields_typed_data _ _ _ _ _  H H0) as [?[??]].
    rewrite H1.
    apply data_type_Either_inv in H3.
    destruct H3 as [[?[??]]|[?[??]]]; subst.
    - apply H5. constructor; simpl; intuition; eauto.
    - eapply H7. constructor; simpl; intuition; eauto.
  Qed.

End TNRCEq.

Notation "e1 ⇒ᶜ e2" := (tnrc_rewrites_to e1 e2) (at level 80).

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
