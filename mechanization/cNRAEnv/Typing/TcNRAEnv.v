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

Require Import Bool.
Require Import String.
Require Import List.
Require Import Compare_dec.
Require Import Eqdep_dec.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import cNRAEnv.
Require Import cNRAEnvEq.
Require Import NRASystem.

Section TcNRAEnv.
  Local Open Scope nraenv_core_scope.
  
  (** Typing for NRA *)
  Section typ.
    Context {m:basic_model}.
    Context (τconstants:tbindings).
  
  Inductive nraenv_core_type : nraenv_core -> rtype -> rtype -> rtype -> Prop :=
  | type_cNRAEnvGetConstant {τenv τin τout} s :
      tdot τconstants s = Some τout ->
      nraenv_core_type (cNRAEnvGetConstant s) τenv τin τout
  | type_cNRAEnvID {τenv τ} :
      nraenv_core_type cNRAEnvID τenv τ τ
  | type_cNRAEnvConst {τenv τin τout} c :
      data_type (normalize_data brand_relation_brands c) τout -> nraenv_core_type (cNRAEnvConst c) τenv τin τout
  | type_cNRAEnvBinop {τenv τin τ₁ τ₂ τout} b op1 op2 :
      binary_op_type b τ₁ τ₂ τout ->
      nraenv_core_type op1 τenv τin τ₁ ->
      nraenv_core_type op2 τenv τin τ₂ ->
      nraenv_core_type (cNRAEnvBinop b op1 op2) τenv τin τout
  | type_cNRAEnvUnop {τenv τin τ τout} u op :
      unary_op_type u τ τout ->
      nraenv_core_type op τenv τin τ ->
      nraenv_core_type (cNRAEnvUnop u op) τenv τin τout
  | type_cNRAEnvMap {τenv τin τ₁ τ₂} op1 op2 :
      nraenv_core_type op1 τenv τ₁ τ₂ ->
      nraenv_core_type op2 τenv τin (Coll τ₁) ->
      nraenv_core_type (cNRAEnvMap op1 op2) τenv τin (Coll τ₂)
  | type_cNRAEnvMapProduct {τenv τin τ₁ τ₂ τ₃} op1 op2 pf1 pf2 pf3 :
      nraenv_core_type op1 τenv (Rec Closed τ₁ pf1) (Coll (Rec Closed τ₂ pf2)) ->
      nraenv_core_type op2 τenv τin (Coll (Rec Closed τ₁ pf1)) ->
      rec_concat_sort τ₁ τ₂ = τ₃ ->
      nraenv_core_type (cNRAEnvMapProduct op1 op2) τenv τin (Coll (Rec Closed τ₃ pf3))
  | type_cNRAEnvProduct {τenv τin τ₁ τ₂ τ₃} op1 op2 pf1 pf2 pf3 :
      nraenv_core_type op1 τenv τin (Coll (Rec Closed τ₁ pf1)) ->
      nraenv_core_type op2 τenv τin (Coll (Rec Closed τ₂ pf2)) ->
      rec_concat_sort τ₁ τ₂ = τ₃ ->
      nraenv_core_type (cNRAEnvProduct op1 op2) τenv τin (Coll (Rec Closed τ₃ pf3))
  | type_cNRAEnvSelect {τenv τin τ} op1 op2 :
      nraenv_core_type op1 τenv τ Bool ->
      nraenv_core_type op2 τenv τin (Coll τ) ->
      nraenv_core_type (cNRAEnvSelect op1 op2) τenv τin (Coll τ)
  | type_cNRAEnvDefault {τenv τin τ} op1 op2 :
      nraenv_core_type op1 τenv τin (Coll τ) ->
      nraenv_core_type op2 τenv τin (Coll τ) ->
      nraenv_core_type (cNRAEnvDefault op1 op2) τenv τin (Coll τ)
  | type_cNRAEnvEither {τenv τl τr τout} opl opr :
      nraenv_core_type opl τenv τl τout ->
      nraenv_core_type opr τenv τr τout ->
      nraenv_core_type (cNRAEnvEither opl opr) τenv (Either τl τr) τout
  | type_cNRAEnvEitherConcat {τenv τin rll pfl rlr pfr rlo pfo lo ro} op1 op2 pflo pfro :
      nraenv_core_type op1 τenv τin (Either (Rec Closed rll pfl) (Rec Closed rlr pfr)) ->
      nraenv_core_type op2 τenv τin (Rec Closed rlo pfo) ->
      rec_concat_sort rll rlo = lo ->
      rec_concat_sort rlr rlo = ro ->
      nraenv_core_type (cNRAEnvEitherConcat op1 op2) τenv  τin (Either (Rec Closed lo pflo) (Rec Closed ro pfro))                  
  | type_cNRAEnvApp {τenv τin τ1 τ2} op2 op1 :
      nraenv_core_type op1 τenv τin τ1 ->
      nraenv_core_type op2 τenv τ1 τ2 ->
      nraenv_core_type (cNRAEnvApp op2 op1) τenv τin τ2
  | type_cNRAEnvEnv {τenv τin} :
      nraenv_core_type cNRAEnvEnv τenv τin τenv
  | type_cNRAEnvAppEnv {τenv τenv' τin τ2} op2 op1 :
      nraenv_core_type op1 τenv τin τenv' ->
      nraenv_core_type op2 τenv' τin τ2 ->
      nraenv_core_type (cNRAEnvAppEnv op2 op1) τenv τin τ2
  | type_cNRAEnvMapEnv {τenv τin τ₂} op1 :
      nraenv_core_type op1 τenv τin τ₂ ->
      nraenv_core_type (cNRAEnvMapEnv op1) (Coll τenv) τin (Coll τ₂).
  End typ.

  Notation "Op ▷ A >=> B ⊣ C ; E" := (nraenv_core_type C Op E A B) (at level 70).

  (** Type lemmas for individual algebraic expressions *)

  Context {m:basic_model}.
  
  Lemma lift_map_typed {τc} {τenv τ₁ τ₂ : rtype} c (op1 : nraenv_core) (env:data) (dl : list data) :
    (bindings_type c τc) ->
    (env ▹ τenv) ->
    (Forall (fun d : data => data_type d τ₁) dl) ->
    (op1 ▷ τ₁ >=> τ₂ ⊣ τc; τenv) ->
    (forall d : data,
       data_type d τ₁ -> exists x : data, brand_relation_brands ⊢ₑ op1 @ₑ d ⊣ c; env = Some x /\ x ▹ τ₂) ->
    exists x : list data, (lift_map (nraenv_core_eval brand_relation_brands c op1 env) dl = Some x) /\ data_type (dcoll x) (Coll τ₂).
  Proof.
    intros dt_c; intros.
    induction dl; simpl; intros.
    - exists (@nil data); split; [reflexivity|apply dtcoll;apply Forall_nil].
    - inversion H0; clear H0.
      elim (H2 a); intros; try assumption.
      elim H0; intros; clear H0.
      rewrite H7; clear H7.
      specialize (IHdl H6); clear H6.
      elim IHdl; intros; clear IHdl.
      elim H0; intros; clear H0.
      dependent induction H7.
      rewrite H6.
      exists (x0 :: x1).
      split; try reflexivity.
      apply dtcoll.
      apply Forall_cons; try assumption.
      assert (r = τ₂) by (apply rtype_fequal; assumption).
      rewrite <- H3; assumption.
  Qed.

  Lemma lift_map_env_typed {τc} {τenv τ₁ τ₂ : rtype} c (op1 : nraenv_core) (x0:data) (dl : list data) :
    bindings_type c τc ->
    (x0 ▹ τ₁) ->
    (Forall (fun d : data => data_type d τenv) dl) ->
    (op1 ▷ τ₁ >=> τ₂ ⊣ τc;τenv) ->
    (forall env : data,
       data_type env τenv ->
       forall d : data,
         data_type d τ₁ ->
         exists x : data, brand_relation_brands ⊢ₑ op1 @ₑ d ⊣ c;env = Some x /\ data_type x τ₂) ->
    exists x : list data, (lift_map (fun env' => (nraenv_core_eval brand_relation_brands c op1 env' x0)) dl = Some x) /\ data_type (dcoll x) (Coll τ₂).
  Proof.
    intros dt_c.
    induction dl; simpl; intros.
    - exists (@nil data); split; [reflexivity|apply dtcoll;apply Forall_nil].
    - inversion H0; clear H0 H4 l H3 x.
      elim (H2 a H5 x0); intros; try assumption.
      elim H0; intros; clear H0.
      rewrite H3; clear H3; simpl in *.
      specialize (IHdl H H6); clear H6.
      elim IHdl; intros; clear IHdl; trivial.
      elim H0; intros; clear H0.
      dependent induction H6.
      rewrite H3; clear H3; simpl.
      exists (x2 :: x1).
      split; try reflexivity.
      apply dtcoll.
      apply Forall_cons; try assumption.
      assert (r = τ₂) by (apply rtype_fequal; assumption).
      rewrite <- H3; assumption.
      eauto.
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

  Lemma omap_concat_typed_env
        (τenv:rtype) (τ₁ τ₂ τ₃: list (string * rtype)) (env:data) (dl2: list data)
        (x : list (string * data)) pf1 pf2 pf3:
    (data_type env τenv) ->
    (forall x : data, In x dl2 -> data_type x (Rec Closed τ₂ pf2)) ->
    rec_concat_sort τ₁ τ₂ = τ₃ ->
    data_type (drec x) (Rec Closed τ₁ pf1) ->
    (exists y : list data,
       lift_map (fun x1 : data => orecconcat (drec x) x1) dl2
       = Some y /\ data_type (dcoll y) (Coll (Rec Closed τ₃ pf3))).
  Proof.
    intro Henv.
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
    revert H0; elim (lift_map (fun x2 : data => orecconcat (drec x) x2) dl2); intros; try discriminate.
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

  Lemma oproduct_typed_env {τ₁ τ₂ τ₃: list (string * rtype)} (dl dl0: list data) pf1 pf2 pf3:
    Forall (fun d : data => data_type d (Rec Closed τ₂ pf2)) dl0 ->
    Forall (fun d : data => data_type d (Rec Closed τ₁ pf1)) dl ->
    rec_concat_sort τ₁ τ₂ = τ₃ ->
    exists x : list data, (oproduct dl dl0 = Some x) /\ data_type (dcoll x) (Coll (Rec Closed τ₃ pf3)).
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
      unfold oproduct.
      simpl.
      assert (exists y, (omap_concat (drec x) dl0) = Some y /\ (data_type  (dcoll y) (Coll (Rec Closed  (rec_concat_sort τ₁ τ₂) pf3))))
        by (eapply omap_concat_typed_env; eauto).
      destruct H5 as [? [??]].
      generalize (oproduct_cons _ _ _ _ _ H2 H5).
      unfold oproduct; simpl.
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

  Lemma omap_product_typed_env {τc} {τenv:rtype} {τ₁ τ₂ τ₃ : list (string * rtype)} (op1 : nraenv_core) c (env:data) (dl: list data) pf1 pf2 pf3:
    bindings_type c τc ->
    env ▹ τenv ->
    rec_concat_sort τ₁ τ₂ = τ₃ ->
    Forall (fun d : data => data_type d (Rec Closed τ₁ pf1)) dl ->
    (op1 ▷ Rec Closed τ₁ pf1 >=> Coll (Rec Closed τ₂ pf2) ⊣ τc;τenv) ->
    (forall d : data,
                data_type d (Rec Closed τ₁ pf1) ->
                exists x : data,
                   brand_relation_brands ⊢ₑ op1 @ₑ d ⊣ c;env = Some x /\ data_type x (Coll (Rec Closed τ₂ pf2))) ->
    exists x : list data, (omap_product (nraenv_core_eval brand_relation_brands c op1 env) dl = Some x) /\ data_type (dcoll x) (Coll (Rec Closed τ₃ pf3)).
  Proof.
    intros dt_c Henv.
    intros; rewrite Forall_forall in *.
    induction dl; simpl in *; unfold omap_product in *; simpl.
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
    unfold oncoll_map_concat.
    elim (H2 (drec x0) H); intros; clear H2.
    elim H5; intros; clear H5.
    rewrite H2; clear H2.
    dtype_inverter.
    apply Col_inv in H7.
    rename x1 into dl0.
    assert (exists y, (omap_concat (drec x0) dl0) = Some y /\ (data_type (dcoll y) (Coll (Rec Closed (rec_concat_sort τ₁ τ₂) pf3)))).
    unfold omap_concat.
    eapply (omap_concat_typed_env τenv τ₁ τ₂ (rec_concat_sort τ₁ τ₂)); eauto.
    apply Forall_forall; eauto.
    destruct H2 as [?[eqq ?]].
    rewrite eqq; clear eqq.
    simpl.
    exists (x1++x).
    split. reflexivity.
    apply data_type_concat; assumption.
  Qed.

  Lemma omap_product_typed2_env {τc} {τenv:rtype} {τ₁ τ₂ τ₃ : list (string * rtype)} τin c (op1 : nraenv_core) (env:data) y (dl: list data) pf1 pf2 pf3:
    bindings_type c τc ->
    env▹ τenv ->
    rec_concat_sort τ₁ τ₂ = τ₃ ->
    Forall (fun d : data => data_type d (Rec Closed τ₁ pf1)) dl ->
    (op1 ▷ τin >=> Coll (Rec Closed τ₂ pf2) ⊣ τc;τenv) ->
    (forall d : data,
                data_type d (Rec Closed τ₁ pf1) ->
                exists x : data,
                   brand_relation_brands ⊢ₑ op1 @ₑ y ⊣ c;env = Some x /\ data_type x (Coll (Rec Closed τ₂ pf2))) ->
    exists x : list data, (omap_product (fun z =>  brand_relation_brands ⊢ₑ op1@ₑ y ⊣ c;env) dl = Some x) /\ data_type (dcoll x) (Coll (Rec Closed τ₃ pf3)).
  Proof.
    intros dt_c Henv.
    intros; rewrite Forall_forall in *.
    induction dl; simpl in *; unfold omap_product in *; simpl.
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
    unfold oncoll_map_concat.
    elim (H2 (drec dl0) H); intros; clear H2.
    elim H5; intros; clear H5.
    rewrite H2; clear H2.
    dtype_inverter.
    apply Col_inv in H7.
    rename x0 into dl1.
    assert (exists y, (omap_concat (drec dl0) dl1) = Some y /\ (data_type  (dcoll y) (Coll (Rec Closed (rec_concat_sort τ₁ τ₂) pf3)))).
    unfold omap_concat.
    apply (omap_concat_typed_env τenv τ₁ τ₂ (rec_concat_sort τ₁ τ₂) env dl1 dl0 pf1 pf2 pf3); trivial.
    intros.
    rewrite Forall_forall in H7; specialize (H7 _ H2); trivial.
    destruct H2 as [? [eqq ?]].
    rewrite eqq; clear eqq.
    exists (x0++x).
    split. reflexivity.
    apply data_type_concat; assumption.
  Qed.

  (** Main typing soundness theorem for NRAEnv *)

  Theorem typed_nraenv_core_yields_typed_data {τc} {τenv τin τout} c (env:data) (d:data) (op:nraenv_core):
    bindings_type c τc ->
    (env ▹ τenv) -> (d ▹ τin) -> (op ▷ τin >=> τout ⊣ τc;τenv) ->
    (exists x, (brand_relation_brands ⊢ₑ op @ₑ d ⊣ c;env = Some x /\ (x ▹ τout))).
  Proof.
    intros dt_c Henv.
    intros.
    revert env Henv d H.
    dependent induction H0; simpl; intros.
    (* type_cNRAEnvGetConstant *)
    - unfold tdot in *.
      unfold edot in *.
      destruct (Forall2_lookupr_some dt_c H) as [? [eqq1 eqq2]].
      rewrite eqq1.
      eauto.
    (* type_cNRAEnvID *)
    - exists d; split; [reflexivity|assumption].
    (* type_cNRAEnvConst *)
    - exists (normalize_data brand_relation_brands c0); split; try reflexivity.
      assumption.
    (* type_cNRAEnvBinop *)
    - elim (IHnraenv_core_type1 env Henv d H0); elim (IHnraenv_core_type2 env Henv d H0); intros.
      elim H1; elim H2; intros; clear H1 H2.
      rewrite H3; simpl.
      rewrite H5; simpl.
      apply (typed_binary_op_yields_typed_data x0 x b H4 H6); assumption.
    (* type_cNRAEnvUnop *)
    - elim (IHnraenv_core_type env Henv d H1); intros.
      elim H2; intros; clear H2.
      rewrite H3.
      apply (typed_unary_op_yields_typed_data x u H4); assumption.
    (* type_cNRAEnvMap *)
    - elim (IHnraenv_core_type2 env Henv d H); intros; clear H IHnraenv_core_type2.
      elim H0; intros; clear H0.
      rewrite H; clear H.
      invcs H1.
      rtype_equalizer.
      subst.
      assert (EE : exists x : list data, (lift_map (nraenv_core_eval brand_relation_brands c op1 env) dl = Some x)
                                    /\ data_type (dcoll x) (Coll τ₂)).
      + apply (@lift_map_typed τc τenv τ₁ τ₂ c op1 env dl dt_c Henv); trivial.
        apply IHnraenv_core_type1; trivial.
      + destruct EE as [? [eqq dt]].
        simpl.
        rewrite eqq; simpl.
        eexists; split; try reflexivity.
        trivial.
    (* type_cNRAEnvMapProduct *)
    - elim (IHnraenv_core_type2 env Henv d H0); intros; clear IHnraenv_core_type2 H0.
      elim H1; intros; clear H1.
      rewrite H0; clear H0.
      invcs H2.
      assert (EE : exists x : list data, (omap_product (nraenv_core_eval brand_relation_brands c op1 env) dl = Some x) /\ data_type (dcoll x) (Coll (Rec Closed (rec_concat_sort τ₁ τ₂) pf3))).
      + apply (omap_product_typed_env op1 c env dl pf1 pf2 pf3 dt_c Henv); try assumption; try reflexivity.
        apply recover_rec_forall with (r:= r); assumption.
        apply IHnraenv_core_type1; assumption.
      + destruct EE as [? [eqq typ]].
        simpl; rewrite eqq; simpl.
        eexists; split; try reflexivity.
        trivial.
    (* type_cNRAEnvProduct *)
    - elim (IHnraenv_core_type1 env Henv d H0); intros; clear IHnraenv_core_type1.
      elim H1; intros; clear H1.
      rewrite H2; clear H2; invcs H3.
      assert (EE : exists x : list data, (omap_product (fun _ : data => brand_relation_brands ⊢ₑ op2 @ₑ d ⊣ c;env) dl = Some x) /\ data_type (dcoll x) (Coll (Rec Closed (rec_concat_sort τ₁ τ₂) pf3))).
      + apply (@omap_product_typed2_env τc τenv τ₁ τ₂ (rec_concat_sort τ₁ τ₂) τin c op2 env d dl pf1 pf2 pf3); try assumption; try reflexivity.
        apply recover_rec_forall with (r:= r); assumption.
        destruct (IHnraenv_core_type2 env Henv d H0) as [? [eqq dt]].
        rewrite eqq.
        intros.
        eexists; split; try reflexivity.
        trivial.
      + destruct EE as [? [eqq typ]].
        simpl; rewrite eqq; simpl.
        eexists; split; try reflexivity.
        trivial.
    (* type_cNRAEnvSelect *)
    - elim (IHnraenv_core_type2 env Henv d H); intros; clear IHnraenv_core_type2.
      elim H0; intros; clear H0.
      rewrite H1; clear H1 H0_0.
      invcs H2.
      rtype_equalizer.
      subst.
      assert (exists c2, 
          (lift_filter
             (fun x' : data =>
              match brand_relation_brands ⊢ₑ op1 @ₑ x' ⊣ c;env with
              | Some (dbool b) => Some b
              | _ => None
              end) dl) = Some c2 /\ Forall (fun d : data => data_type d τ) c2).
      + induction dl.
        * exists (@nil data). split. reflexivity. apply Forall_nil.
        * rewrite Forall_forall in *; intros.
          assert (forall x : data, In x dl -> data_type x τ)
                 by intuition.
          assert (data_type a τ)
            by (simpl in *; intuition).
          destruct (IHnraenv_core_type1 env Henv a H1) as [? [eqq dt]].
          simpl; rewrite eqq; simpl.
          dtype_inverter.
          destruct (IHdl H0) as [? [eqq1 dt1]].
          rewrite eqq1; simpl.
          assert (data_type a τ)
            by (simpl in *; intuition).
          destruct x0; simpl; eexists; split; try reflexivity; trivial.
          constructor; trivial.
      + destruct H0 as [? [eqq dt]].
        simpl; rewrite eqq; simpl.
        eexists; split; try reflexivity; trivial.
        constructor; trivial.
    (* type_cNRAEnvDefault *)
    - elim (IHnraenv_core_type1 env Henv d H); elim (IHnraenv_core_type2 env Henv d H); intros.
      elim H0; elim H1; intros; clear H0 H1 H.
      rewrite H2. rewrite H4. clear H2 H4.
      simpl.
      invcs H3; invcs H5; rtype_equalizer.
      subst.
      destruct dl.
      + eexists; split; try reflexivity; trivial.
        constructor; trivial.
      + eexists; split; try reflexivity; trivial.
        constructor; trivial.
    (* type_cNRAEnvEither *)
    - destruct (data_type_Either_inv H) as [[dd[? ddtyp]]|[dd[? ddtyp]]]; subst; eauto.
    (* type_cNRAEnvEitherConcat *)
    - destruct (IHnraenv_core_type2 env Henv d H1) as [? [??]].
      rewrite H2.
      destruct (IHnraenv_core_type1 env Henv d H1) as [? [??]].
      rewrite H4.
      destruct (data_type_Rec_inv H3); subst.
      destruct (data_type_Either_inv H5) as [[dd[? ddtyp]]|[dd[? ddtyp]]]; subst; eauto;
      destruct (data_type_Rec_inv ddtyp); subst;
      (eexists;split;[reflexivity| ];
      econstructor;
      eapply dtrec_rec_concat_sort; eauto).
    (* type_cNRAEnvApp *)
    - elim (IHnraenv_core_type1 env Henv d H); intros.
      elim H0; intros; clear H0 H.
      rewrite H1; simpl.
      elim (IHnraenv_core_type2 env Henv x H2); intros.
      elim H; intros; clear H.
      rewrite H0; simpl.
      exists x0;split;[reflexivity|assumption].
    (* type_cNRAEnvEnv *)
    - exists env; split; [reflexivity|assumption].
    (* type_cNRAEnvAppEnv *)
    - elim (IHnraenv_core_type1 env Henv d H); intros.
      elim H0; intros; clear H0.
      rewrite H1; simpl.
      elim (IHnraenv_core_type2 x H2 d H); intros.
      elim H0; intros; clear H0.
      rewrite H3; simpl.
      exists x0;split;[reflexivity|assumption].
    (* type_cNRAEnvMapEnv *)
    - intros.
      invcs Henv; rtype_equalizer.
      subst; simpl.
      assert (exists x : list data, (lift_map (fun env' : data => (nraenv_core_eval brand_relation_brands c op1 env' d)) dl = Some x) /\ data_type (dcoll x) (Coll τ₂)).
      * apply (@lift_map_env_typed τc τenv τin τ₂); try assumption.
      * destruct H1 as [? [eqq dt]].
        rewrite eqq; simpl.
        eexists; split; try reflexivity; trivial.
  Qed.

  (* Evaluation into single value for typed core NRAe *)

  Hint Constructors nra_type unary_op_type binary_op_type.
  Hint Resolve ATdot ATnra_data.
  (** Corrolaries of the main type soudness theorem *)

  Definition typed_nraenv_core_total {τc} {τenv τin τout} (op:nraenv_core) (HOpT: op ▷ τin >=> τout ⊣ τc;τenv) c (env:data) (d:data)
    (dt_c: bindings_type c τc) :
    (env ▹ τenv) ->
    (d ▹ τin) ->
    { x:data | x ▹ τout }.
  Proof.
    intro Henv.
    intros HdT.
    generalize (typed_nraenv_core_yields_typed_data c env d op dt_c Henv HdT HOpT).
    intros.
    destruct (brand_relation_brands ⊢ₑ op @ₑ d ⊣ c;env).
    assert (data_type d0 τout).
    - inversion H. inversion H0. inversion H1. trivial.
    - exists d0. trivial.
    - cut False. intuition. inversion H.
      destruct H0. inversion H0.
  Defined.

  Definition tnraenv_core_eval {τc} {τenv τin τout} (op:nraenv_core) (HOpT: op ▷ τin >=> τout ⊣ τc;τenv) c (env:data) (d:data)
             (dt_c: bindings_type c τc) : 
    (env ▹ τenv) -> (d ▹ τin) -> data.
  Proof.
    intros Henv.
    intros HdT.
    destruct (typed_nraenv_core_total op HOpT c env d dt_c Henv HdT).
    exact x.
  Defined.

  Theorem typed_nraenv_core_to_typed_nra {τc} {τenv τin τout} (op:nraenv_core):
    (nraenv_core_type τc op τenv τin τout) -> (nra_type τc (nra_of_nraenv_core op) (nra_context_type τenv τin) τout).
  Proof.
    intros.
    dependent induction H; simpl; intros.
    (* cNRAEnvGetConstant *)
    - unfold nra_bind, nra_context_type.
      econstructor; eauto.
    (* cNRAEnvID *)
    - eauto.
    (* cNRAEnvConst *)
    - eauto.
    (* cNRAEnvBinop *)
    - eauto.
    (* cNRAEnvUnop *)
    - eauto.
    (* cNRAEnvMap *)
    - apply (@type_NRAMap m τc (nra_context_type τenv τin) (nra_context_type τenv τ₁) τ₂); try assumption.
      eapply ATunnest_two.
      eapply (type_NRAUnop). eauto.
      unfold nra_wrap_a1, nra_double.
      eapply type_NRABinop. eauto.
      eapply (type_NRAUnop). eauto.
      eapply type_NRAUnop; eauto.
      eapply type_OpDot. unfold tdot, edot; simpl. auto.
      eapply (type_NRAUnop). eauto.
      eauto.
      unfold tdot, edot; auto.
      reflexivity.
      reflexivity.
    (* cNRAEnvMapProduct *)
    - apply (@type_NRAMap m τc (nra_context_type τenv τin) (Rec Closed (("PBIND"%string, τenv) :: ("PDATA"%string, (Rec Closed τ₁ pf1)) :: ("PDATA2"%string, (Rec Closed τ₂ pf2)) :: nil) (eq_refl _))).
      econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      reflexivity.
      econstructor; eauto.
      econstructor; eauto.
      reflexivity.
      apply (@type_NRAMapProduct m τc (nra_context_type τenv τin)
                          [("PBIND"%string, τenv); ("PDATA"%string, Rec Closed τ₁ pf1)]
                          [("PDATA2"%string, (Rec Closed τ₂ pf2))]
                          [("PBIND"%string, τenv); ("PDATA"%string, Rec Closed τ₁ pf1); ("PDATA2"%string, Rec Closed τ₂ pf2)]
                          (NRAMap (NRAUnop (OpRec "PDATA2") NRAID) (nra_of_nraenv_core op1))
                          (unnest_two "a1" "PDATA" (NRAUnop OpBag (nra_wrap_a1 (nra_of_nraenv_core op2))))
                          eq_refl eq_refl
            ); try reflexivity.
      eauto.
      unfold nra_wrap_a1.
      apply (ATunnest_two "a1" "PDATA" (NRAUnop OpBag (nra_double "PBIND" "a1" nra_bind (nra_of_nraenv_core op2))) τc (nra_context_type τenv τin) [("PBIND"%string, τenv); ("a1"%string, Coll (Rec Closed τ₁ pf1))] eq_refl (Rec Closed τ₁ pf1)); try reflexivity.
      apply (@type_NRAUnop m τc (nra_context_type τenv τin) (Rec Closed [("PBIND"%string, τenv); ("a1"%string, Coll (Rec Closed τ₁ pf1))] eq_refl)).
      econstructor; eauto.
      unfold nra_double, nra_bind.
      apply (@type_NRABinop m τc (nra_context_type  τenv τin) (Rec Closed [("PBIND"%string, τenv)] eq_refl) (Rec Closed [("a1"%string, Coll (Rec Closed τ₁ pf1))] eq_refl)); try eauto.
        econstructor; eauto.

        econstructor; eauto.
        econstructor; eauto.
    (* cNRAEnvProduct *)
    - eauto.
    (* cNRAEnvSelect *)
    - econstructor; eauto.
      2: { econstructor; eauto.
           eapply ATunnest_two.
           + econstructor; eauto.
             unfold nra_wrap_a1, nra_double.
             eapply type_NRABinop.
             * econstructor; reflexivity.
             * econstructor; eauto.
               econstructor; eauto.
               eapply type_OpDot; unfold tdot, edot; simpl; eauto.
             * econstructor; eauto.
           + unfold tdot, edot; simpl; eauto.
           + econstructor; eauto. }
        * econstructor; eauto.
          eapply type_OpDot; unfold tdot, edot; simpl; eauto.
    (* cNRAEnvDefault *)
    - eauto.
    (* type_cNRAEnvEither *)
    - econstructor.
      + econstructor; try reflexivity.
        * { econstructor.
            - econstructor; eauto.
              econstructor; eauto.
              reflexivity.
            - econstructor; eauto.
          }
        * { econstructor; eauto.
            - econstructor; eauto.
              econstructor; eauto.
              econstructor; eauto.
            
          } 
      + econstructor; eauto.
    (* cNRAEnvEitherConcat *)
    - eauto.
    (* cNRAEnvApp *)
    - apply (@type_NRAApp m τc (nra_context_type τenv τin) (nra_context_type τenv τ1) τ2).
      + unfold nra_context, nra_bind, nra_context_type, nra_double; simpl.
        unfold nra_wrap.
        apply (@type_NRABinop m τc (Rec Closed [("PBIND"%string, τenv); ("PDATA"%string, τin)] eq_refl) (Rec Closed (("PBIND"%string, τenv)::nil) (eq_refl _)) (Rec Closed (("PDATA"%string, τ1)::nil) (eq_refl _))).
        econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
      + trivial.
    (* cNRAEnvEnv *)
    - unfold nra_bind, nra_context_type. eauto.
    (* cNRAEnvAppEnv *)
    - apply (@type_NRAApp m τc (nra_context_type τenv τin) (nra_context_type τenv' τin) τ2).
      + unfold nra_context, nra_bind, nra_context_type, nra_double; simpl.
        apply (@type_NRABinop m τc (Rec Closed [("PBIND"%string, τenv); ("PDATA"%string, τin)] eq_refl) (Rec Closed (("PBIND"%string, τenv')::nil) (eq_refl _)) (Rec Closed (("PDATA"%string, τin)::nil) (eq_refl _))).
        econstructor; eauto.
        do 3 (econstructor; eauto).
        do 3 (econstructor; eauto).
      + trivial.
    (* cNRAEnvMapEnv *)
    - econstructor; eauto.
      eapply ATunnest_two.
      + econstructor; eauto.
        unfold nra_wrap_bind_a1, nra_double.
        eapply type_NRABinop; eauto.
        * do 3 (econstructor; eauto).
          reflexivity.
      + reflexivity.
      + simpl; trivial.
      Grab Existential Variables.
      eauto. eauto. eauto. eauto. eauto. 
      eauto. eauto. eauto. eauto. eauto.
      eauto. eauto.
  Qed.

  Lemma fold_nra_context_type (env d: {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true}) pf :
    Rec Closed [("PBIND"%string, env); ("PDATA"%string, d)] pf
    = nra_context_type env d.
  Proof.
    unfold nra_context_type.
    erewrite Rec_pr_irrel; eauto.
  Qed.

  Ltac defst l
    := match l with
       | @nil (string*rtype₀) => constr:(@nil (string*rtype))
       | cons (?x,proj1_sig ?y) ?l' =>
         let l'' := defst l' in
         constr:(cons (x,y) l'')
       end.
  
  Ltac rec_proj_simpler
    := repeat
         match goal with
         | [H: Rec₀ ?k ?l = proj1_sig ?τ |- _ ] => symmetry in H
         | [H: proj1_sig ?τ = Rec₀ ?k ?l |- _ ] =>
           let ll := defst l in
           let HH:=fresh "eqq" in
           generalize (@Rec₀_eq_proj1_Rec _ _ τ k ll); intros HH;
           simpl in HH; specialize (HH H); clear H; destruct HH;
           try subst τ
         end.
  
  Lemma UIP_bool {a b:bool} (pf1 pf2:a = b) : pf1 = pf2.
  Proof.
    apply UIP_dec. apply bool_dec.
  Qed.

  Ltac nra_inverter_ext
    :=
      simpl in *; match goal with
                  | [H:@nra_type _ _ (unnest_two _ _ _) _ (Coll _) |- _ ] => apply ATunnest_two_inv in H;
                                                                           destruct H as [? [? [? [? [? [? [?[??]]]]]]]]
                  | [H: prod _ _ |- _ ] => destruct H; simpl in *; try subst
                  | [H: context [Rec Closed [("PBIND"%string, ?env); ("PDATA"%string, ?d)] ?pf ] |- _ ] => unfold rtype in H; rewrite (fold_nra_context_type env d pf) in H
                  | [H: Rec₀ ?k ?l = proj1_sig ?τ |- _ ] => symmetry in H
                  | [H: proj1_sig ?τ = Rec₀ ?k ?l |- _ ] =>
                    let ll := defst l in
                    let HH:=fresh "eqq" in
                    generalize (@Rec₀_eq_proj1_Rec _ _ τ k ll); intros HH;
                    simpl in HH; specialize (HH H); clear H; destruct HH;
                    try subst τ
                  | [H:proj1_sig _ =
                       Rec₀ Closed
                            (map
                               (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                  (fst x, ` (snd x))) _) |- _ ]
                    => let Hpf := fresh "spf" in
                       apply Rec₀_eq_proj1_Rec in H; destruct H as [? Hpf]
                  | [H1:@eq bool ?a ?b,
                        H2:@eq bool ?a ?b |- _] => destruct (UIP_bool H1 H2)
                  end.

  Ltac nra_inverter2 :=
    repeat (try unfold nra_wrap, nra_wrap_a1, nra_wrap_bind_a1, nra_context, nra_double, nra_bind, nra_wrap in *; (nra_inverter_ext || nra_inverter); try subst).

  Ltac tdot_inverter :=
    repeat
      match goal with
        | [H: tdot _ _ = Some _ |- _ ] =>
          let HH:= fresh "eqq" in
          inversion H as [HH];
            match type of HH with
              | ?x1 = ?x2 => try (subst x2 || subst x1); clear H
              | _ => fail 1
            end
      end.

  Lemma typed_nraenv_core_to_typed_nra_inv' {k τc τenv τin τout pf} (op:nraenv_core):
    nra_type τc (nra_of_nraenv_core op) (Rec k [("PBIND"%string, τenv); ("PDATA"%string, τin)] pf) τout ->
    nraenv_core_type τc op τenv τin τout.
  Proof.
    Hint Constructors nraenv_core_type.
    revert k τenv τin τout pf.
    induction op; simpl; intros.
    - inversion H; clear H; subst.
      econstructor; trivial.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
    - nra_inverter2; try tdot_inverter; eauto.
  Qed.
  
  Theorem typed_nraenv_core_to_typed_nra_inv {τc} {τenv τin τout} (op:nraenv_core):
    nra_type τc (nra_of_nraenv_core op) (nra_context_type τenv τin) τout ->
    nraenv_core_type τc op τenv τin τout.
  Proof.
    unfold nra_context_type.
    apply typed_nraenv_core_to_typed_nra_inv'.
  Qed.

  Lemma typed_nraenv_core_const_sort_f {τc op τenv τin τout} :
    nraenv_core_type (rec_sort τc) op τenv τin τout ->
    nraenv_core_type τc op τenv τin τout.
  Proof.
    revert τc op τenv τin τout.
    induction op; simpl; inversion 1; rtype_equalizer; subst; eauto.
    unfold tdot, edot in *.
    rewrite (assoc_lookupr_drec_sort (odt:=ODT_string)) in H1.
    econstructor. apply H1.
  Qed.

  Lemma typed_nraenv_core_const_sort_b {τc op τenv τin τout} :
      nraenv_core_type τc op τenv τin τout ->
      nraenv_core_type (rec_sort τc) op τenv τin τout.
  Proof.
    revert τc op τenv τin τout.
    induction op; simpl; inversion 1; rtype_equalizer; subst; eauto.
    econstructor.
    unfold tdot, edot.
    rewrite (assoc_lookupr_drec_sort (odt:=ODT_string)).
    apply H1.
  Qed.

  Lemma typed_nraenv_core_const_sort τc op τenv τin τout :
    nraenv_core_type (rec_sort τc) op τenv τin τout <->
    nraenv_core_type τc op τenv τin τout.
  Proof.
    split; intros.
    - apply typed_nraenv_core_const_sort_f; trivial.
    - apply typed_nraenv_core_const_sort_b; trivial.
  Qed.

End TcNRAEnv.

(* Typed algebraic plan *)

Notation "Op ▷ A >=> B ⊣ C ; E" := (nraenv_core_type C Op E A B) (at level 70).
Notation "Op @▷ d ⊣ C ; e" := (tnraenv_core_eval C Op e d) (at level 70).

(* Used to prove type portion of typed directed rewrites *)
  
Hint Constructors nraenv_core_type.
Hint Constructors unary_op_type.
Hint Constructors binary_op_type.

Ltac nraenv_core_inverter := 
  match goal with
    | [H:Coll _ = Coll _ |- _] => inversion H; clear H
    | [H: `?τ₁ = Coll₀ (`?τ₂) |- _] => rewrite (Coll_right_inv τ₁ τ₂) in H; subst
    | [H:  Coll₀ (`?τ₂) = `?τ₁ |- _] => symmetry in H
    (* Note: do not generalize too hastily on unary_op/binary_op constructors *)
    | [H:cNRAEnvID ▷ _ >=> _ ⊣ _ ; _ |- _ ] => inversion H; clear H
    | [H:cNRAEnvEnv ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvMap _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvMapProduct _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvMapEnv _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvDefault _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvApp _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvAppEnv _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvEither _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvEitherConcat _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvProduct _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvSelect _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvUnop _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvBinop _ _ _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H:cNRAEnvConst _ ▷ _ >=> _ ⊣  _ ;_ |- _ ] => inversion H; clear H
    | [H: (_,_)  = (_,_) |- _ ] => inversion H; clear H
    | [H: map (fun x2 : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x2, ` (snd x2))) ?x0 = [] |- _] => apply (map_rtype_nil x0) in H; simpl in H; subst
    | [H: (map
             (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                (fst x, proj1_sig (snd x))) _)
          = 
          (map
             (fun x' : string * {τ₀' : rtype₀ | wf_rtype₀ τ₀' = true} =>
                (fst x', proj1_sig (snd x'))) _) |- _ ] =>
      apply map_rtype_fequal in H; trivial
    | [H:Rec _ _ _ = Rec _ _ _ |- _ ] => generalize (Rec_inv H); clear H; intro H; try subst
    | [H: context [(_::nil) = map 
                                (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                   (fst x, proj1_sig (snd x))) _] |- _] => symmetry in H
                                                                                         
    | [H: context [map 
                     (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                        (fst x, proj1_sig (snd x))) _ = (_::nil) ] |- _] => apply map_eq_cons in H;
        destruct H as [? [? [? [??]]]]
    | [H: Coll₀ _ = Coll₀ _ |- _ ] => inversion H; clear H
    | [H: Rec₀ _ _ = Rec₀ _ _ |- _ ] => inversion H; clear H
    | [H: _ ▷ _ >=> snd ?x ⊣  _ ;_ |- _] => destruct x; simpl in *; subst
    | [H:unary_op_type OpBag _ _ |- _ ] => inversion H; clear H; subst
    | [H:unary_op_type OpFlatten _ _ |- _ ] => inversion H; clear H; subst
    | [H:unary_op_type (OpRec _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unary_op_type (OpDot _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unary_op_type (OpRecProject _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unary_op_type (OpRecRemove _) _ _ |- _ ] => inversion H; clear H; subst
    | [H:unary_op_type OpLeft _ _ |- _ ] => inversion H; clear H; subst
    | [H:unary_op_type OpRight _ _ |- _ ] => inversion H; clear H; subst
    | [H:binary_op_type OpRecConcat _ _ _ |- _ ] => inversion H; clear H
    | [H:binary_op_type OpAnd _ _ _ |- _ ] => inversion H; clear H
    | [H:binary_op_type OpRecMerge _ _ _ |- _ ] => inversion H; clear H
  end; try rtype_equalizer; try assumption; try subst; simpl in *; try nraenv_core_inverter.

(* inverts, then tries and solve *)
Ltac nraenv_core_inferer := try nraenv_core_inverter; subst; try eauto.

(* simplifies when a goal evaluates an expression over well-typed data *)

Ltac input_well_typed :=
  repeat progress
         match goal with
           | [HO:?op ▷ ?τin >=> ?τout ⊣  ?τc ; ?τenv,
              HI:?x ▹ ?τin,
              HC:bindings_type ?c ?τc,
              HE:?env ▹ ?τenv
              |- context [(nraenv_core_eval ?h ?c ?op ?env ?x)]] =>
             let xout := fresh "dout" in
             let xtype := fresh "τout" in
             let xeval := fresh "eout" in
             destruct (typed_nraenv_core_yields_typed_data c _ _ op HC HE HI HO)
               as [xout [xeval xtype]]; rewrite xeval in *; simpl
         end.

