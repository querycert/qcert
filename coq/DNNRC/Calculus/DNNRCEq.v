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

Section DNNRCEq.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.
  Require Import String.
  Require Import List.
  Require Import Arith.
  
  Require Import Utils BasicRuntime.
  Require Import DData DDataNorm DNNRC.

  Context {fruntime:foreign_runtime}.
  Context {A plug_type:Set}.
  Context {eqdec:EqDec A eq}.
  Context {plug:AlgPlug plug_type}.

  (** Equivalence between expressions in the 
      Distributed Nested Relational Calculus *)

  Definition dnnrc_eq (e1 e2:dnrc A plug_type) : Prop :=
    forall (h:brand_relation_t) (denv:dbindings),
      Forall (ddata_normalized h) (map snd denv) ->
      dnrc_eval h denv e1 = dnrc_eval h denv e2.

  Global Instance dnnrc_equiv : Equivalence dnnrc_eq.
  Proof.
    constructor.
    - unfold Reflexive, dnnrc_eq.
      intros; reflexivity.
    - unfold Symmetric, dnnrc_eq.
      intros; rewrite (H _ denv) by trivial; reflexivity.
    - unfold Transitive, dnnrc_eq.
      intros; rewrite (H _ denv) by trivial;
      rewrite (H0 _ denv) by trivial; reflexivity.
  Qed.

  (* all the dnnrc constructors are proper wrt. equivalence *)

  (* DNRCVar *)
  Global Instance dvar_proper : Proper (eq ==> eq ==> dnnrc_eq) DNRCVar.
  Proof.
    unfold Proper, respectful, dnnrc_eq.
    intros; subst; reflexivity.
  Qed.

  (* DNRCConst *)
  
  Global Instance dconst_proper : Proper (eq ==> eq ==> dnnrc_eq) DNRCConst.
  Proof.
    unfold Proper, respectful, dnnrc_eq.
    intros; subst; reflexivity.
  Qed.

  (* DNRCBinop *)
  
  Global Instance dbinop_proper : Proper (eq ==> binop_eq ==> dnnrc_eq ==> dnnrc_eq ==> dnnrc_eq) DNRCBinop.
  Proof.
    unfold Proper, respectful, dnnrc_eq.
    intros; simpl. subst.
    rewrite H1 by trivial.
    rewrite H2 by trivial.
    case_eq (dnrc_eval h denv y1);
      case_eq (dnrc_eval h denv y2); intros; simpl; trivial.
    destruct d0; destruct d; try reflexivity; simpl.
    rewrite H0; [reflexivity| | ].
    apply (dnrc_eval_normalized_local h denv y1); try assumption.
    apply (dnrc_eval_normalized_local h denv y1); try assumption.
  Qed.

  (* DNRCUnnop *)
  
  Global Instance dunop_proper : Proper (eq ==> unaryop_eq ==> dnnrc_eq ==> dnnrc_eq) DNRCUnop.
  Proof.
    unfold Proper, respectful, dnnrc_eq.
    intros; simpl. subst.
    rewrite H1 by trivial.
    case_eq (dnrc_eval h denv y1); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    rewrite H0; [reflexivity| ].
    apply (dnrc_eval_normalized_local h denv y1); try assumption.
  Qed.
    
  (* DNRCLet *)
  
  Global Instance dlet_proper : Proper (eq ==> eq ==> dnnrc_eq ==> dnnrc_eq ==> dnnrc_eq) DNRCLet.
  Proof.
    unfold Proper, respectful, dnnrc_eq.
    intros; simpl. rewrite H0; clear H0; rewrite H1 by trivial; clear H1.
    case_eq (dnrc_eval h denv y1); simpl; trivial; intros.
    rewrite H2; eauto.
    constructor; eauto.
    simpl.
    eapply dnrc_eval_normalized; eauto.
  Qed.

  (* DNRCFor *)

  Hint Resolve data_normalized_dcoll_in.

  Global Instance dfor_proper : Proper (eq ==> eq ==> dnnrc_eq ==> dnnrc_eq ==> dnnrc_eq) DNRCFor.
  Proof.
    unfold Proper, respectful, dnnrc_eq.
    intros; simpl. rewrite H1 by trivial; clear H1. subst.
    case_eq (dnrc_eval h denv y1); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    f_equal.
    apply rmap_ext; intros.
    rewrite H2; simpl; eauto.
    constructor; [|assumption].
    assert (ddata_normalized h (Dlocal (dcoll l))).
    - eapply dnrc_eval_normalized; eauto.
    - inversion H1; subst; clear H1.
      constructor.
      inversion H5; subst; clear H5.
      rewrite Forall_forall in H4.
      auto.
  Qed.

  (* DNRCIf *)
  
  Global Instance dif_proper : Proper (eq ==> dnnrc_eq ==> dnnrc_eq ==> dnnrc_eq ==> dnnrc_eq) DNRCIf.
  Proof.
    unfold Proper, respectful, dnnrc_eq.
    intros; simpl. subst. rewrite H0 by trivial; clear H0.
    case_eq (dnrc_eval h denv y0); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    destruct b; eauto.
  Qed.

  (* DNRCEither *)
  Global Instance deither_proper : Proper (eq ==> dnnrc_eq ==> eq ==> dnnrc_eq ==> eq ==> dnnrc_eq ==> dnnrc_eq) DNRCEither.
  Proof.
    unfold Proper, respectful, dnnrc_eq.
    intros; simpl. subst.
    rewrite H0 by trivial.
    match_case; intros ? eqq1. match_destr.
    - apply H2; simpl; eauto.
      rewrite Forall_forall; intros.
      inversion H; subst.
      unfold olift, checkLocal in eqq1.
      case_eq (dnrc_eval h denv y0); intros; rewrite H1 in eqq1; try congruence;
      destruct d0; try congruence; inversion eqq1; subst.
      assert (ddata_normalized h (Dlocal (dleft d))).
      apply (@dnrc_eval_normalized _ _ _ _ plug denv y0); assumption.
      inversion H3; subst; clear H3.
      inversion H7; subst; clear H7.
      constructor; assumption.
      rewrite Forall_forall in H5. auto.
    - apply H4; simpl; eauto.
      rewrite Forall_forall; intros.
      inversion H; subst.
      unfold olift, checkLocal in eqq1.
      case_eq (dnrc_eval h denv y0); intros; rewrite H1 in eqq1; try congruence;
      destruct d0; try congruence; inversion eqq1; subst.
      assert (ddata_normalized h (Dlocal (dright d))).
      apply (@dnrc_eval_normalized _ _ _ _ plug denv y0); assumption.
      inversion H3; subst; clear H3.
      inversion H7; subst; clear H7.
      constructor; assumption.
      rewrite Forall_forall in H5. auto.
  Qed.

  (* DNRCCollect *)
  Global Instance dcollect_proper : Proper (eq ==> dnnrc_eq ==> dnnrc_eq) DNRCCollect.
  Proof.
    unfold Proper, respectful, dnnrc_eq.
    intros; simpl. subst.
    rewrite H0 by trivial.
    reflexivity.
  Qed.
    
  (* DNRCDispatch *)
  Global Instance ddispatch_proper : Proper (eq ==> dnnrc_eq ==> dnnrc_eq) DNRCDispatch.
  Proof.
    unfold Proper, respectful, dnnrc_eq.
    intros; simpl. subst.
    rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* DNRCAlg *)
  (* Here we would need a notion of equality on AlgPlug --
     something worth discussing with Stefan *)
  (*
  Global Instance dalg : Proper (eq ==> eq ==> dnnrc_eq ==> dnnrc_eq) DNRCDispatch.
  Proof.
    unfold Proper, respectful, dnnrc_eq.
    intros; simpl. subst.
    ...
  Qed.
  *)

End DNNRCEq.

Notation "X ≡ᵈ Y" := (dnnrc_eq X Y) (at level 90) : dnrc_scope.                             (* ≡ = \equiv *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
