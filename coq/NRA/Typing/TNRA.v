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

Section TNRA.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import Program.
  Require Import CommonSystem.
  Require Import NRA.

  (** Typing for NRA *)
  Section typ.
    Context {m:basic_model}.
    Context (τconstants:tbindings).

  Inductive nra_type : nra -> rtype -> rtype -> Prop :=
  | ATID {τ} :
      nra_type AID τ τ
  | ATConst {τin τout} c :
      data_type (normalize_data brand_relation_brands c) τout -> nra_type (AConst c) τin τout
  | ATBinop {τin τ₁ τ₂ τout} b op1 op2 :
      (* b : (τ₁,τ₂) -> τout
         op₁ : τin -> τ₁
         op₂ : τin -> τ₂
         ==========================
         b (op₁,op₂) : τin -> τout *)
      binOp_type b τ₁ τ₂ τout ->
      nra_type op1 τin τ₁ ->
      nra_type op2 τin τ₂ ->
      nra_type (ABinop b op1 op2) τin τout
  | ATUnop {τin τ τout} u op :
      unaryOp_type u τ τout ->
      nra_type op τin τ ->
      nra_type (AUnop u op) τin τout
  | ATMap {τin τ₁ τ₂} op1 op2 :
      nra_type op1 τ₁ τ₂ ->
      nra_type op2 τin (Coll τ₁) ->
      nra_type (AMap op1 op2) τin (Coll τ₂)
  | ATMapConcat {τin τ₁ τ₂ τ₃} op1 op2 pf1 pf2 pf3 :
      nra_type op1 (Rec Closed τ₁ pf1) (Coll (Rec Closed τ₂ pf2)) ->
      nra_type op2 τin (Coll (Rec Closed τ₁ pf1)) ->
      rec_concat_sort τ₁ τ₂ = τ₃ ->
      nra_type (AMapConcat op1 op2) τin (Coll (Rec Closed τ₃ pf3))
  | ATProduct {τin τ₁ τ₂ τ₃} op1 op2 pf1 pf2 pf3 :
      nra_type op1 τin (Coll (Rec Closed τ₁ pf1)) ->
      nra_type op2 τin (Coll (Rec Closed τ₂ pf2)) ->
      rec_concat_sort τ₁ τ₂ = τ₃ ->
      nra_type (AProduct op1 op2) τin (Coll (Rec Closed τ₃ pf3))
  | ATSelect {τin τ} op1 op2 :
      nra_type op1 τ Bool ->
      nra_type op2 τin (Coll τ) ->
      nra_type (ASelect op1 op2) τin (Coll τ)
  | ATDefault {τin τ} op1 op2 :
      nra_type op1 τin (Coll τ) ->
      nra_type op2 τin (Coll τ) ->
      nra_type (ADefault op1 op2) τin (Coll τ)
  | ATEither {τl τr τout} opl opr :
      nra_type opl τl τout ->
      nra_type opr τr τout ->
      nra_type (AEither opl opr) (Either τl τr) τout
  | ATEitherConcat {τin rll pfl rlr pfr rlo pfo lo ro} op1 op2 pflo pfro :
      nra_type op1 τin (Either (Rec Closed rll pfl) (Rec Closed rlr pfr)) ->
      nra_type op2 τin (Rec Closed rlo pfo) ->
      rec_concat_sort rll rlo = lo ->
      rec_concat_sort rlr rlo = ro ->
      nra_type (AEitherConcat op1 op2) τin (Either (Rec Closed lo pflo) (Rec Closed ro pfro))
  | ATApp {τin τ1 τ2} op1 op2 :
      nra_type op2 τin τ1 ->
      nra_type op1 τ1 τ2 ->
      nra_type (AApp op1 op2) τin τ2
  | ATGetConstant {τin τout} s :
      tdot τconstants s = Some τout ->
      nra_type (AGetConstant s) τin τout.
  End typ.
  
  Notation "Op ▷ A >=> B ⊣ C" := (nra_type C Op A B) (at level 70) (* \Vdash *).

  (** Type lemmas for individual algebraic expressions *)
  Context {m:basic_model}.
  
  Lemma rmap_typed {τc} {τ₁ τ₂ : rtype} c (op1 : nra) (dl : list data) :
    (bindings_type c τc) ->
    (Forall (fun d : data => data_type d τ₁) dl) ->
    (op1 ▷ τ₁ >=> τ₂ ⊣ τc) ->
    (forall d : data,
       data_type d τ₁ -> exists x : data, brand_relation_brands ⊢ op1 @ₐ d ⊣ c = Some x /\ data_type x τ₂) ->
    exists x : list data, (rmap (nra_eval brand_relation_brands c op1) dl = Some x) /\ data_type (dcoll x) (Coll τ₂).
  Proof.
    intros Hcenv.
    intros.
    induction dl; simpl; intros.
    - exists (@nil data); split; [reflexivity|apply dtcoll;apply Forall_nil].
    - inversion H; clear H.
      elim (H1 a H4); intros.
      elim H; intros; clear H.
      rewrite H6; clear H6.
      specialize (IHdl H5); clear H5.
      elim IHdl; intros; clear IHdl.
      elim H; intros; clear H.
      dependent induction H6.
      rewrite H5.
      exists (x0 :: x1).
      split; try reflexivity.
      apply dtcoll.
      apply Forall_cons; try assumption.
      assert (r = τ₂) by (apply rtype_fequal; assumption).
      rewrite <- H2; assumption.
  Qed.

  Lemma recover_rec k d r τ pf:
    data_type d r ->
    ` r =
    Rec₀ k
      (map
         (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
            (fst x, ` (snd x))) τ) ->
    data_type d (Rec k τ pf).
  Proof.
    intros.
    assert (Rec k τ pf = r).
    unfold Rec.
    apply rtype_fequal.
    rewrite H0.
    reflexivity.
    rewrite H1; assumption.
  Qed.

  Lemma recover_rec_forall k l r τ pf:
    Forall (fun d : data => data_type d r) l ->
    ` r =
    Rec₀ k
      (map
         (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
            (fst x, ` (snd x))) τ) ->
    Forall (fun d : data => data_type d (Rec k τ pf)) l.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    specialize (H x H1).
    apply (recover_rec k x r τ pf); assumption.
  Qed.

  Lemma omap_concat_typed
        (τ₁ τ₂ τ₃: list (string * rtype)) (dl2: list data)
        (x : list (string * data)) pf1 pf2 pf3:
    (forall x : data, In x dl2 -> data_type x (Rec Closed τ₂ pf2)) ->
    rec_concat_sort τ₁ τ₂ = τ₃ ->
    data_type (drec x) (Rec Closed τ₁ pf1) ->
    (exists y : list data,
       rmap (fun x1 : data => orecconcat (drec x) x1) dl2
       = Some y /\ data_type (dcoll y) (Coll (Rec Closed τ₃ pf3))).
  Proof.
    intros; induction dl2; simpl.
    exists (@nil data); split; [reflexivity|apply dtcoll; apply Forall_nil].
    simpl in H.
    assert (data_type a (Rec Closed τ₂ pf2))
      by (apply (H a); left; reflexivity).
    destruct (data_type_Rec_inv H2); subst.
    apply dtrec_closed_inv in H2.
    assert (H':forall x : data, In x dl2 -> data_type x (Rec Closed τ₂ pf2)) by
        (eapply forall_in_weaken; eassumption).
    specialize (IHdl2 H'); clear H'.
    destruct IHdl2 as [? [??]].
    revert H0; elim (rmap (fun x2 : data => orecconcat (drec x) x2) dl2); intros; try discriminate.
    inversion H0; subst; clear H0.
    unfold lift.
    induction dl2.
    - simpl.
      exists (drec (rec_concat_sort x x0) :: nil); split; try reflexivity.
      apply dtcoll. rewrite Forall_forall in *; intros.
      simpl in H0. intuition.
      destruct x2; try congruence. inversion H4; subst; clear H4.
      apply dtrec_full.
      apply rec_concat_with_drec_concat_well_typed; try assumption.
      apply dtrec_closed_inv in H1. trivial.
    - simpl in *.
      generalize (H a). intuition.
      destruct (data_type_Rec_inv H5); subst.
      apply dtrec_closed_inv in H5.
      destruct IHdl2; [intuition | ].
      unfold lift.
      destruct H0 as [eq1 dt1].
      case_option_in eq1; try discriminate.
      eexists; split; [reflexivity | ].
      constructor.
      inversion eq1; subst; clear eq1.
      inversion dt1; subst.
      generalize (recover_rec_forall _ _ _ _ pf3 H8 H7).
      inversion 1; simpl; subst.
      constructor; simpl; trivial.
      constructor; trivial.
      apply dtrec_full.
      apply dtrec_closed_inv in H1.
      apply rec_sort_Forall2.
      + repeat rewrite domain_app.
        rewrite (sorted_forall_same_domain H1).
        rewrite (sorted_forall_same_domain H5). trivial.
      + apply Forall2_app; trivial.
  Qed.
      
  Lemma rproduct_typed {τ₁ τ₂ τ₃: list (string * rtype)} (dl dl0: list data) pf1 pf2 pf3:
    Forall (fun d : data => data_type d (Rec Closed τ₂ pf2)) dl0 ->
    Forall (fun d : data => data_type d (Rec Closed τ₁ pf1)) dl ->
    rec_concat_sort τ₁ τ₂ = τ₃ ->
    exists x : list data, (rproduct dl dl0 = Some x) /\ data_type (dcoll x) (Coll (Rec Closed τ₃ pf3)).
  Proof.
    intros; rewrite Forall_forall in *.
    induction dl; simpl in *.
    - exists (@nil data); split; [reflexivity| apply dtcoll; apply Forall_nil].
    - assert (exists r, a = drec r /\ data_type (drec r) (Rec Closed τ₁ pf1)).
      + clear IHdl H; assert (data_type a (Rec Closed τ₁ pf1))
                    by (specialize (H0 a); apply H0; left; reflexivity).
         destruct (data_type_Rec_inv H); subst.
         apply dtrec_closed_inv in H.
         eexists; split; [reflexivity | ].
         apply dtrec_full; trivial.
      + destruct H2 as [? [??]]; subst.
      assert (forall x : data, In x dl -> data_type x (Rec Closed τ₁ pf1))
        by (apply forall_in_weaken with (P := (fun x0 => (drec x) = x0)); assumption).
      specialize (IHdl H1).
      destruct IHdl as [? [??]].
      unfold rproduct.
      simpl.
      assert (exists y, (omap_concat (drec x) dl0) = Some y /\ (data_type  (dcoll y) (Coll (Rec Closed  (rec_concat_sort τ₁ τ₂) pf3))))
        by (eapply omap_concat_typed; eauto).
      destruct H5 as [? [??]].
      generalize (rproduct_cons _ _ _ _ _ H2 H5).
      unfold rproduct; simpl.
      rewrite H5. intros eqq.
      exists (x1 ++ x0).
      split; trivial.
      inversion H6; subst.
      inversion H4; subst.
      generalize (recover_rec_forall _ _ _ _ pf3 H9 H8); intros.
      generalize (recover_rec_forall _ _ _ _ pf3 H11 H10); intros.
      constructor. apply Forall_app; trivial.
  Qed.
  
  Lemma data_type_concat l1 l2 τ:
    data_type (dcoll l1) (Coll τ) ->
    data_type (dcoll l2) (Coll τ) ->
    data_type (dcoll (l1 ++ l2)) (Coll τ).
  Proof.
    intros.
    dependent induction H.
    dependent induction H0.
    apply dtcoll.
    apply Forall_app; rewrite Forall_forall in *;
    assert (r = τ) by (apply rtype_fequal; assumption);
    assert (r0 = τ) by (apply rtype_fequal; assumption);
    rewrite H1 in H; rewrite H2 in H0; assumption.
  Qed.

  Lemma rmap_concat_typed {τc} {τ₁ τ₂ τ₃ : list (string * rtype)} (op1 : nra) c (dl: list data) pf1 pf2 pf3:
    bindings_type c τc ->
    rec_concat_sort τ₁ τ₂ = τ₃ ->
    Forall (fun d : data => data_type d (Rec Closed τ₁ pf1)) dl ->
    (op1 ▷ Rec Closed τ₁ pf1 >=> Coll (Rec Closed τ₂ pf2) ⊣ τc) ->
    (forall d : data,
                data_type d (Rec Closed τ₁ pf1) ->
                exists x : data,
                   brand_relation_brands ⊢ op1 @ₐ d ⊣ c = Some x /\ data_type x (Coll (Rec Closed τ₂ pf2))) ->
    exists x : list data, (rmap_concat (nra_eval brand_relation_brands c op1) dl = Some x) /\ data_type (dcoll x) (Coll (Rec Closed τ₃ pf3)).
  Proof.
    intros Hcenv.
    intros; rewrite Forall_forall in *.
    induction dl; simpl in *; unfold rmap_concat in *; simpl.
    exists (@nil data); split; [reflexivity|apply dtcoll; apply Forall_nil].
    assert (forall x : data, In x dl -> data_type x (Rec Closed τ₁ pf1))
      by (apply forall_in_weaken with (P := (fun x => a = x)); assumption).
    elim (IHdl H3); intros; elim H4; intros; clear IHdl H4.
    assert (data_type a (Rec Closed τ₁ pf1))
      by (apply (H0 a); left; reflexivity).
    rewrite H5; clear H5.
    destruct (data_type_Rec_inv H4); subst.
    apply dtrec_closed_inv in H4.
    assert (data_type (drec x0) (Rec Closed τ₁ pf1))
      by (apply (H0 (drec x0)); left; reflexivity).
    unfold oomap_concat.
    elim (H2 (drec x0) H); intros; clear H2.
    elim H5; intros; clear H5.
    rewrite H2; clear H2.
    dtype_inverter.
    rename x1 into dl0.
    apply Col_inv in H7.
    assert (exists y, (omap_concat (drec x0) dl0) = Some y /\ (data_type (dcoll y) (Coll (Rec Closed (rec_concat_sort τ₁ τ₂) pf3)))).
    unfold omap_concat.
    eapply (omap_concat_typed τ₁ τ₂ (rec_concat_sort τ₁ τ₂)); eauto.
    apply Forall_forall; eauto.

    destruct H2 as [?[??]].
    rewrite H2; clear H2.
    simpl.
    exists (x1++x).
    split. reflexivity.
    apply data_type_concat; assumption.
  Qed.

  Lemma rmap_concat_typed2 {τc} {τ₁ τ₂ τ₃ : list (string * rtype)} τin (op1 : nra) c y (dl: list data) pf1 pf2 pf3:
    bindings_type c τc ->
    rec_concat_sort τ₁ τ₂ = τ₃ ->
    Forall (fun d : data => data_type d (Rec Closed τ₁ pf1)) dl ->
    (op1 ▷ τin >=> Coll (Rec Closed τ₂ pf2) ⊣ τc) ->
    (forall d : data,
                data_type d (Rec Closed τ₁ pf1) ->
                exists x : data,
                   brand_relation_brands ⊢ op1 @ₐ y  ⊣ c = Some x /\ data_type x (Coll (Rec Closed τ₂ pf2))) ->
    exists x : list data, (rmap_concat (fun z =>  brand_relation_brands ⊢ op1@ₐ y ⊣ c) dl = Some x) /\ data_type (dcoll x) (Coll (Rec Closed τ₃ pf3)).
  Proof.
    intros Hcenv.
    intros; rewrite Forall_forall in *.
    induction dl; simpl in *; unfold rmap_concat in *; simpl.
    exists (@nil data); split; [reflexivity|apply dtcoll; apply Forall_nil].
    assert (forall x : data, In x dl -> data_type x (Rec Closed τ₁ pf1))
      by (apply forall_in_weaken with (P := (fun x => a = x)); assumption).
    elim (IHdl H3); intros; elim H4; intros; clear IHdl H4.
    assert (data_type a (Rec Closed τ₁ pf1))
      by (apply (H0 a); left; reflexivity).
    rewrite H5; clear H5.
    destruct (data_type_Rec_inv H4); subst.
    apply dtrec_closed_inv in H4.
    rename x0 into dl0.
    assert (data_type (drec dl0) (Rec Closed τ₁ pf1))
      by (apply (H0 (drec dl0)); left; reflexivity).
    unfold oomap_concat.
    elim (H2 (drec dl0) H); intros; clear H2.
    elim H5; intros; clear H5.
    rewrite H2; clear H2.
    dtype_inverter.
    rename x0 into dl1.
    apply Col_inv in H7.

    assert (exists y, (omap_concat (drec dl0) dl1) = Some y /\ (data_type  (dcoll y) (Coll (Rec Closed (rec_concat_sort τ₁ τ₂) pf3)))).
    unfold omap_concat.
    apply (omap_concat_typed τ₁ τ₂ (rec_concat_sort τ₁ τ₂) dl1 dl0 pf1 pf2 pf3); trivial.
    intros.
    rewrite Forall_forall in H7; specialize (H7 _ H2); trivial.

    destruct H2 as [?[eqq ?]].
    rewrite eqq; clear eqq. simpl.
    exists (x0++x).
    split. reflexivity.
    apply data_type_concat; assumption.
  Qed.
  
  (** Main typing soundness theorem for the NRA *)

  Theorem typed_nra_yields_typed_data {τc} {τin τout} cenv (d:data) (op:nra):
    bindings_type cenv τc ->
    (data_type d τin) -> (op ▷ τin >=> τout ⊣ τc) ->
    (exists x, brand_relation_brands ⊢ op @ₐ d ⊣ cenv = Some x /\ (data_type x τout)).
  Proof.
    intros Hcenv.
    intros.
    revert d H.
    nra_cases (dependent induction H0) Case; simpl; intros.
    - Case "AID"%string.
      exists d; split; [reflexivity|assumption].
    - Case "AConst"%string.
      exists (RDataNorm.normalize_data brand_relation_brands c); split; try reflexivity.
      assumption.
    - Case "ABinop"%string.
      elim (IHnra_type1 d H0); elim (IHnra_type2 d H0); intros.
      elim H1; elim H2; intros; clear H1 H2.
      rewrite H3; simpl.
      rewrite H5; simpl.
      apply (typed_binop_yields_typed_data x0 x b H4 H6); assumption.
    - Case "AUnop"%string.
      elim (IHnra_type d H1); intros.
      elim H2; intros; clear H2.
      rewrite H3.
      apply (typed_unop_yields_typed_data x u H4); assumption.
    - Case "AMap"%string.
      elim (IHnra_type2 d H); intros; clear H IHnra_type2.
      elim H0; intros; clear H0.
      rewrite H; clear H.
      invcs H1; rtype_equalizer.
      subst.
      assert (exists x : list data, (rmap (nra_eval brand_relation_brands cenv op1) dl = Some x)
                                    /\ data_type (dcoll x) (Coll τ₂)).
      apply (rmap_typed cenv op1 dl Hcenv H2); assumption.
      destruct H as [? [eqq dt]].
      autorewrite with alg; rewrite eqq.
      exists (dcoll x); split; [reflexivity|assumption].
    - Case "AMapConcat"%string.
      elim (IHnra_type2 d H0); intros; clear IHnra_type2 H0.
      elim H1; intros; clear H1.
      destruct (data_type_Col_inv H2); subst.
      inversion H2; subst.
      generalize (recover_rec_forall _ _ _ _ pf1 H3 H1); intros.

      rewrite H0; clear H0. simpl.
      
      assert (exists x : list data, (rmap_concat (nra_eval brand_relation_brands cenv op1) x0 = Some x) /\ data_type (dcoll x) (Coll (Rec Closed (rec_concat_sort τ₁ τ₂) pf3))).
      apply (rmap_concat_typed op1 cenv x0 pf1 pf2 pf3 Hcenv); try assumption; try reflexivity.
      elim H0; intros; clear H0.
      elim H4; intros; clear H4.
      autorewrite with alg; rewrite H0. simpl.
      exists (dcoll x); split; [reflexivity|assumption].
    - Case "AProduct"%string.
      elim (IHnra_type1 d H0); intros; clear IHnra_type1.
      elim H1; intros; clear H1.
      rewrite H2; clear H2.
      invcs H3.
      assert (exists x : list data, (rmap_concat (fun _ : data =>  brand_relation_brands ⊢ op2 @ₐ d ⊣ cenv) dl = Some x) /\ data_type (dcoll x) (Coll (Rec Closed (rec_concat_sort τ₁ τ₂) pf3))).
      apply (rmap_concat_typed2 τin op2 cenv d dl pf1 pf2 pf3 Hcenv); try assumption; try reflexivity.
      apply (recover_rec_forall _ _ _ _ pf1 H4); trivial.
      destruct (IHnra_type2 d H0) as [? [eqq dt]]; intros.
      rewrite eqq; clear eqq.
      exists x; split; [reflexivity|assumption].
      destruct H as [? [eqq dt]].
      simpl; rewrite eqq; exists (dcoll x); simpl.
      split; [reflexivity|assumption].
    - Case "ASelect"%string.
      elim (IHnra_type2 d H); intros; clear IHnra_type2.
      elim H0; intros; clear H0.
      rewrite H1; clear H1 H0_0.
      invcs H2; rtype_equalizer.
      subst.
      assert (exists c2, 
          (lift_filter
             (fun x' : data =>
              match brand_relation_brands  ⊢ op1 @ₐ x' ⊣ cenv with
              | Some (dbool b) => Some b
              | _ => None
              end) dl) = Some c2 /\ Forall (fun d : data => data_type d τ) c2).
      + induction dl.
        * exists (@nil data). split. reflexivity. apply Forall_nil.
        * rewrite Forall_forall in *; intros.
          simpl in H3.
          assert (forall x : data, In x dl -> data_type x τ)
                 by intuition.
          assert (data_type a τ)
            by (apply (H3 a); left; reflexivity).
          destruct (IHnra_type1 a H1) as [? [eqq dt]]; intros.
          simpl.
          rewrite eqq.
          dtype_inverter.
          destruct (IHdl H0) as [? [eqq2 dt2]].
          rewrite eqq2.
          { destruct x0.
            - eexists; split; try reflexivity.
              eauto.
            - eexists; split; try reflexivity.
              eauto.
          }
      + simpl.
        destruct H0 as [? [eqq dt]].
        rewrite eqq.
        simpl.
        eexists; split; try reflexivity.
        constructor; trivial.
    - Case "ADefault"%string.
      elim (IHnra_type1 d H); elim (IHnra_type2 d H); intros.
      elim H0; elim H1; intros; clear H0 H1 H.
      rewrite H2. rewrite H4. clear H2 H4.
      simpl.
      invcs H3.
      invcs H5.
      rtype_equalizer.
      subst.
      destruct dl.
      + eexists; split; try reflexivity.
        constructor; trivial.
      + eexists; split; try reflexivity.
        constructor; trivial.
    - Case "AEither"%string.
      inversion H; rtype_equalizer.
      + subst; eauto.
      + subst; eauto.
    - Case "AEitherConcat"%string.
      destruct (IHnra_type1 _ H1) as [x[xeval xtyp]].
      destruct (IHnra_type2 _ H1) as [y[yeval ytyp]].
      rewrite xeval, yeval.
      destruct (data_type_Rec_inv ytyp); subst.
      destruct (data_type_Either_inv xtyp) as [[dd[? ddtyp]]|[dd[? ddtyp]]]; subst.
      + destruct (data_type_Rec_inv ddtyp); subst.
         eexists; split; try reflexivity.
         econstructor.
         eapply dtrec_rec_concat_sort; eauto.
      + destruct (data_type_Rec_inv ddtyp); subst.
         eexists; split; try reflexivity.
         econstructor.
         eapply dtrec_rec_concat_sort; eauto.
    - Case "AApp"%string.
      elim (IHnra_type1 d H); intros.
      elim H0; intros; clear H0 H.
      rewrite H1; simpl.
      elim (IHnra_type2 x H2); intros.
      elim H; intros; clear H.
      rewrite H0; simpl.
      exists x0;split;[reflexivity|assumption].
    - Case "AGetConstant"%string.
      unfold tdot in *.
      unfold edot in *.
      destruct (Forall2_lookupr_some _ _ _ _ Hcenv H) as [? [eqq1 eqq2]].
      rewrite eqq1.
      eauto.
  Qed.

  (* Evaluation into single value for typed algebra *)

  (** Corrolaries of the main type soudness theorem *)

  Definition typed_nra_total {τc} {τin τout} (op:nra) (HOpT: op ▷ τin >=> τout ⊣ τc) c (d:data)
    (dt_c: bindings_type c τc) :
    (data_type d τin) -> { x:data | data_type x τout }.
  Proof.
    intros HdT.
    generalize (typed_nra_yields_typed_data c d op dt_c HdT HOpT).
    intros.
    destruct (brand_relation_brands ⊢ op@ₐd ⊣ c).
    assert (data_type d0 τout).
    - inversion H. inversion H0. inversion H1. trivial.
    - exists d0. trivial.
    - cut False. intuition. inversion H.
      destruct H0. inversion H0.
  Defined.

  Lemma typed_nra_total_eq_matches_eval {τc} {τin τout} (op:nra) (HOpT: op ▷ τin >=> τout ⊣ τc) c (d:data)
    (dt_c: bindings_type c τc)
        (pf: data_type d τin) :
    (brand_relation_brands ⊢ op @ₐd ⊣ c) = Some (proj1_sig (typed_nra_total op HOpT c d dt_c pf)).
  Proof.
    unfold typed_nra_total.
    generalize (typed_nra_yields_typed_data c d op dt_c pf HOpT); intros.
    destruct e; simpl.
    destruct a; simpl.
    rewrite e.
    reflexivity.
  Qed.
  
  Definition tnra_eval {τc} {τin τout} (op:nra) (HOpT: op ▷ τin >=> τout ⊣ τc) c (d:data) (dt_c: bindings_type c τc):
    (data_type d τin) -> data.
  Proof.
    intros HdT.
    destruct (typed_nra_total op HOpT c d dt_c HdT).
    exact x.
  Defined.

End TNRA.

(* Typed algebraic plan *)
Notation "Op ▷ A >=> B ⊣ C" := (nra_type C Op A B) (at level 70).

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
