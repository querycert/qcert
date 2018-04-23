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
Require Import CommonRuntime.
Require Import DData.
Require Import DDataNorm.
Require Import DNNRCBase.

Section DNNRCBaseEq.
  Context {fruntime:foreign_runtime}.
  Context {A plug_type:Set}.
  Context {eqdec:EqDec A eq}.
  Context {plug:AlgPlug plug_type}.

  (** Equivalence between expressions in the 
      Distributed Nested Relational Calculus *)

  Definition dnnrc_base_eq (e1 e2:@dnnrc_base _ A plug_type) : Prop :=
    forall (h:brand_relation_t) (dcenv denv:dbindings),
      Forall (ddata_normalized h) (map snd dcenv) ->
      Forall (ddata_normalized h) (map snd denv) ->
      dnnrc_base_eval h dcenv denv e1 = dnnrc_base_eval h dcenv denv e2.

  Global Instance dnnrc_base_equiv : Equivalence dnnrc_base_eq.
  Proof.
    constructor.
    - unfold Reflexive, dnnrc_base_eq.
      intros; reflexivity.
    - unfold Symmetric, dnnrc_base_eq.
      intros; rewrite (H _ dcenv denv) by trivial; reflexivity.
    - unfold Transitive, dnnrc_base_eq.
      intros; rewrite (H _ dcenv denv) by trivial;
      rewrite (H0 _ dcenv denv) by trivial; reflexivity.
  Qed.

  (* all the dnnrc_base constructors are proper wrt. equivalence *)

  (* DNNRCGetConstant *)
  Global Instance dgetconstant_proper : Proper (eq ==> eq ==> dnnrc_base_eq) DNNRCGetConstant.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; subst; reflexivity.
  Qed.

  (* DNNRCVar *)
  Global Instance dvar_proper : Proper (eq ==> eq ==> dnnrc_base_eq) DNNRCVar.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; subst; reflexivity.
  Qed.

  (* DNNRCConst *)
  
  Global Instance dconst_proper : Proper (eq ==> eq ==> dnnrc_base_eq) DNNRCConst.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; subst; reflexivity.
  Qed.

  (* DNNRCBinop *)
  
  Global Instance dbinary_op_proper : Proper (eq ==> binary_op_eq ==> dnnrc_base_eq ==> dnnrc_base_eq ==> dnnrc_base_eq) DNNRCBinop.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; simpl. subst.
    rewrite H1 by trivial.
    rewrite H2 by trivial.
    case_eq (dnnrc_base_eval h dcenv denv y1);
      case_eq (dnnrc_base_eval h dcenv denv y2); intros; simpl; trivial.
    destruct d0; destruct d; try reflexivity; simpl.
    rewrite H0; [reflexivity| | ].
    apply (dnnrc_base_eval_normalized_local h dcenv denv y1); try assumption.
    apply (dnnrc_base_eval_normalized_local h dcenv denv y1); try assumption.
  Qed.

  (* DNNRCUnnop *)
  
  Global Instance dunary_op_proper : Proper (eq ==> unary_op_eq ==> dnnrc_base_eq ==> dnnrc_base_eq) DNNRCUnop.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; simpl. subst.
    rewrite H1 by trivial.
    case_eq (dnnrc_base_eval h dcenv denv y1); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    rewrite H0; [reflexivity| ].
    apply (dnnrc_base_eval_normalized_local h dcenv denv y1); try assumption.
  Qed.
    
  (* DNNRCLet *)
  
  Global Instance dlet_proper : Proper (eq ==> eq ==> dnnrc_base_eq ==> dnnrc_base_eq ==> dnnrc_base_eq) DNNRCLet.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; simpl. rewrite H0; clear H0; rewrite H1 by trivial; clear H1.
    case_eq (dnnrc_base_eval h dcenv denv y1); simpl; trivial; intros.
    rewrite H2; eauto.
    constructor; eauto.
    simpl.
    eapply (dnnrc_base_eval_normalized h dcenv denv y1); eauto.
  Qed.

  (* DNNRCFor *)

  Hint Resolve data_normalized_dcoll_in.

  Global Instance dfor_proper : Proper (eq ==> eq ==> dnnrc_base_eq ==> dnnrc_base_eq ==> dnnrc_base_eq) DNNRCFor.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; simpl. rewrite H1 by trivial; clear H1. subst.
    case_eq (dnnrc_base_eval h dcenv denv y1); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    { destruct d; try reflexivity; simpl.
      f_equal.
      apply lift_map_ext; intros.
      rewrite H2; simpl; eauto.
      constructor; [|assumption].
      assert (ddata_normalized h (Dlocal (dcoll l))).
      - eapply (dnnrc_base_eval_normalized _ dcenv denv); eauto.
      - inversion H1; subst; clear H1.
        econstructor.
        inversion H6; subst; clear H6.
        rewrite Forall_forall in H5.
        auto. }
    { f_equal.
      apply lift_map_ext; intros.
      rewrite H2; simpl; eauto.
      constructor; [|assumption].
      assert (ddata_normalized h (Ddistr l)).
      - eapply (dnnrc_base_eval_normalized _ dcenv denv); eauto.
      - inversion H1; subst; clear H1.
        constructor.
        rewrite Forall_forall in H6.
        auto. }
  Qed.

  (* DNNRCIf *)
  
  Global Instance dif_proper : Proper (eq ==> dnnrc_base_eq ==> dnnrc_base_eq ==> dnnrc_base_eq ==> dnnrc_base_eq) DNNRCIf.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; simpl. subst. rewrite H0 by trivial; clear H0.
    case_eq (dnnrc_base_eval h dcenv denv y0); simpl; trivial; intros.
    destruct d; try reflexivity; simpl.
    destruct d; try reflexivity; simpl.
    destruct b; eauto.
  Qed.

  (* DNNRCEither *)
  Global Instance deither_proper : Proper (eq ==> dnnrc_base_eq ==> eq ==> dnnrc_base_eq ==> eq ==> dnnrc_base_eq ==> dnnrc_base_eq) DNNRCEither.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; simpl. subst.
    rewrite H0 by trivial.
    match_case; intros ? eqq1. match_destr.
    - apply H2; simpl; eauto.
      rewrite Forall_forall; intros.
      inversion H; subst.
      unfold olift, checkLocal in eqq1.
      case_eq (dnnrc_base_eval h dcenv denv y0); intros; rewrite H1 in eqq1; try congruence;
      destruct d0; try congruence; inversion eqq1; subst.
      assert (ddata_normalized h (Dlocal (dleft d))).
      apply (@dnnrc_base_eval_normalized _ _ _ h dcenv _ denv y0); assumption.
      inversion H3; subst; clear H3.
      inversion H8; subst; clear H8.
      constructor; assumption.
      rewrite Forall_forall in H6. auto.
    - apply H4; simpl; eauto.
      rewrite Forall_forall; intros.
      inversion H; subst.
      unfold olift, checkLocal in eqq1.
      case_eq (dnnrc_base_eval h dcenv denv y0); intros; rewrite H1 in eqq1; try congruence;
      destruct d0; try congruence; inversion eqq1; subst.
      assert (ddata_normalized h (Dlocal (dright d))).
      apply (@dnnrc_base_eval_normalized _ _ _ h dcenv plug denv y0); assumption.
      inversion H3; subst; clear H3.
      inversion H8; subst; clear H8.
      constructor; assumption.
      rewrite Forall_forall in H6. auto.
  Qed.

  (* DNNRCGroupBy *)
  Global Instance dgroupby_proper : Proper (eq ==> eq ==> eq ==> dnnrc_base_eq ==>dnnrc_base_eq) DNNRCGroupBy.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; simpl; subst.
    trivial.
  Qed.

  (* DNNRCCollect *)
  Global Instance dcollect_proper : Proper (eq ==> dnnrc_base_eq ==> dnnrc_base_eq) DNNRCCollect.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; simpl. subst.
    rewrite H0 by trivial.
    reflexivity.
  Qed.
    
  (* DNNRCDispatch *)
  Global Instance ddispatch_proper : Proper (eq ==> dnnrc_base_eq ==> dnnrc_base_eq) DNNRCDispatch.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; simpl. subst.
    rewrite H0 by trivial.
    reflexivity.
  Qed.

  Global Instance dalg_proper : Proper (eq ==> eq ==> Forall2 (fun n1 n2  => fst n1 = fst n2 /\ dnnrc_base_eq (snd n1) (snd n2)) ==> dnnrc_base_eq) DNNRCAlg.
  Proof.
    unfold Proper, respectful, dnnrc_base_eq.
    intros; simpl; subst.
    cut ((map
         (fun x : string * @dnnrc_base _ A plug_type =>
          match dnnrc_base_eval h dcenv denv (snd x) with
          | Some (Dlocal _) => None
          | Some (Ddistr coll) => Some (fst x, coll)
          | None => None
          end) x1) = (map
         (fun x : string * @dnnrc_base _ A plug_type =>
          match dnnrc_base_eval h dcenv denv (snd x) with
          | Some (Dlocal _) => None
          | Some (Ddistr coll) => Some (fst x, coll)
          | None => None
          end) y1)); [intros eqq; rewrite eqq; trivial | ].
    dependent induction H1; simpl; trivial.
    rewrite IHForall2 by trivial.
    destruct H as [eqq1 eqq2].
    rewrite eqq1, eqq2 by trivial.
    trivial.
  Qed.

End DNNRCBaseEq.

Notation "X ≡ᵈ Y" := (dnnrc_base_eq X Y) (at level 90) : dnnrc_scope.                             (* ≡ = \equiv *)

