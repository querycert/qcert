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

Section TNNRCExtEq.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.
  Require Import String.
  Require Import List.
  Require Import Arith.

  Require Import Utils BasicSystem.
  Require Import NNRC NNRCExt TNNRCExt.

  (* Named Nested Relational Calculus *)

  (* A different kind of equivalence for rewrites *)

  Context {m:basic_model}.

  Definition tnnrc_ext_rewrites_to (e1 e2:nnrc) : Prop :=
    forall (τenv : tbindings) (τout:rtype),
      nnrc_ext_type τenv e1 τout ->
      (nnrc_ext_type τenv e2 τout) /\ (forall (env:bindings),
                                     bindings_type env τenv -> @nnrc_ext_eval _ brand_relation_brands env e1 = @nnrc_ext_eval _ brand_relation_brands env e2).

  Notation "e1 ⇒ᶜ e2" := (tnnrc_ext_rewrites_to e1 e2) (at level 80).

  Require Import NNRCExtEq.
  Open Scope nnrc_scope.

  Lemma data_normalized_bindings_type_map env τenv :
    bindings_type env τenv ->
    Forall (data_normalized brand_relation_brands) (map snd env).
  Proof.
    rewrite Forall_map.
    apply bindings_type_Forall_normalized.
  Qed.

  Hint Resolve data_normalized_bindings_type_map.
  
  Lemma nnrc_ext_rewrites_typed_with_untyped (e1 e2:nnrc) :
    e1 ≡ᶜ e2 ->
    (forall  {τenv: tbindings} {τout:rtype}, nnrc_ext_type τenv e1 τout -> nnrc_ext_type τenv e2 τout)
    -> e1 ⇒ᶜ e2.
  Proof.
    intros.
    unfold tnnrc_ext_rewrites_to; simpl; intros.
    split; auto 2; intros.
    apply H; eauto.
  Qed.

  (****************
   * Proper stuff *
   ****************)

  Require Import TNNRC TOps.
  
  Hint Constructors nnrc_type.
  Hint Constructors unaryOp_type.
  Hint Constructors binOp_type.

  Require Import ROpsEq.
  
  Global Instance tnnrc_ext_rewrites_to_pre : PreOrder tnnrc_ext_rewrites_to.
  Proof.
    constructor; red; intros.
    - unfold tnnrc_ext_rewrites_to; intros.
      split; try assumption; intros.
      reflexivity.
    - unfold tnnrc_ext_rewrites_to in *; intros.
      specialize (H τenv τout H1).
      elim H; clear H; intros.
      specialize (H0 τenv τout H).
      elim H0; clear H0; intros.
      split; try assumption; intros.
      rewrite (H2 env); try assumption.
      rewrite (H3 env); try assumption.
      reflexivity.
  Qed.
  
  (* NNRCVar *)

  Global Instance nnrc_ext_var_tproper:
    Proper (eq ==> tnnrc_ext_rewrites_to) NNRCVar.
  Proof.
    unfold Proper, respectful, tnnrc_ext_rewrites_to; intros.
    rewrite <- H.
    split; try assumption.
    intros; reflexivity.
  Qed.
  
  (* NNRCConst *)

  Global Instance nnrc_ext_const_tproper:
    Proper (eq ==> tnnrc_ext_rewrites_to) NNRCConst.
  Proof.
    unfold Proper, respectful, tnnrc_ext_rewrites_to; intros.
    rewrite <- H.
    split; try assumption.
    intros; reflexivity.
  Qed.

  (* NNRCBinop *)

  Global Instance nnrc_ext_binop_tproper:
    Proper (eq ==> tnnrc_ext_rewrites_to
               ==> tnnrc_ext_rewrites_to
               ==> tnnrc_ext_rewrites_to) NNRCBinop.
  Proof.
    unfold Proper, respectful, tnnrc_ext_rewrites_to; intros.
    rewrite H in *; clear H.
    inversion H2; clear H2; subst.
    econstructor; eauto.
    specialize (H0  τenv τ₁ H8); elim H0; clear H0 H8; intros.
    specialize (H1  τenv τ₂ H9); elim H1; clear H1 H9; intros.
    econstructor; eauto; intros.
    intros.
    specialize (H0  τenv τ₁ H8); elim H0; clear H0 H8; intros.
    specialize (H1  τenv τ₂ H9); elim H1; clear H1 H9; intros.
    unfold nnrc_ext_eval in *.
    simpl.
    rewrite (H2 env H); rewrite (H3 env H); reflexivity.
  Qed.
  
  (* NNRCUnop *)

  Global Instance nnrc_ext_unop_tproper :
    Proper (eq ==> tnnrc_ext_rewrites_to ==> tnnrc_ext_rewrites_to) NNRCUnop.
  Proof.
    unfold Proper, respectful, tnnrc_ext_rewrites_to; intros.
    rewrite H in *; clear H.
    inversion H1; clear H1; subst.
    econstructor; eauto.
    econstructor; eauto.
    specialize (H0  τenv τ₁ H6); elim H0; clear H0 H6; intros; assumption.
    intros.
    specialize (H0  τenv τ₁ H6); elim H0; clear H0 H6; intros.
    unfold nnrc_ext_eval in *.
    simpl. rewrite (H1 env H); reflexivity.
  Qed.

  (* NNRCLet *)

  Global Instance nnrc_ext_let_tproper :
    Proper (eq ==> tnnrc_ext_rewrites_to ==> tnnrc_ext_rewrites_to ==> tnnrc_ext_rewrites_to) NNRCLet.
  Proof.
    unfold Proper, respectful, tnnrc_ext_rewrites_to; intros.
    unfold nnrc_ext_eval,nnrc_ext_type in *.
    inversion H2; clear H2; subst.
    specialize (H0 τenv τ₁ H8); elim H0; clear H0 H8; intros.
    specialize (H1 ((y, τ₁) :: τenv) τout H9); elim H1; clear H1 H9; intros.
    econstructor; eauto.
    econstructor; eauto.
    intros; simpl.
    rewrite (H0 env H3).
    case_eq (nnrc_core_eval brand_relation_brands env (nnrc_ext_to_nnrc y0));
      intros; try reflexivity.
    rewrite (H2 ((y, d) :: env)); try reflexivity.
    unfold bindings_type.
    apply Forall2_cons; try assumption.
    simpl; split; try reflexivity.
    generalize (@typed_nnrc_ext_yields_typed_data _ τ₁ env τenv y0 H3 H); intros.
    elim H5; intros.
    elim H6; clear H6; intros.
    unfold nnrc_ext_eval,nnrc_ext_type in *.
    rewrite H4 in H6.
    inversion H6; assumption.
  Qed.
    
  (* NNRCFor *)

  Require Import TData.
  
  Lemma dcoll_wt (l:list data) (τ:rtype) (τenv:tbindings) (env:bindings) (e:nnrc):
    bindings_type env τenv ->
    nnrc_type τenv e (Coll τ) ->
    nnrc_core_eval brand_relation_brands env e = Some (dcoll l) ->
    forall x:data, In x l -> (data_type x τ).
  Proof.
    intros.
    generalize (@typed_nnrc_yields_typed_data _ (Coll τ) env τenv e H H0); intros.
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

  Global Instance nnrc_ext_for_tproper :
    Proper (eq ==> tnnrc_ext_rewrites_to ==> tnnrc_ext_rewrites_to ==> tnnrc_ext_rewrites_to) NNRCFor.
  Proof.
    unfold Proper, respectful, tnnrc_ext_rewrites_to; intros.
    inversion H2; clear H2; subst.
    specialize (H0  τenv (Coll τ₁) H8); elim H0; clear H0 H8; intros.
    specialize (H1  ((y, τ₁) :: τenv) τ₂ H9); elim H1; clear H1 H9; intros.
    econstructor; eauto.
    econstructor; eauto.
    intros; simpl.
    unfold nnrc_ext_eval,nnrc_ext_type in *; simpl.
    rewrite (H0 env H3).
    case_eq (nnrc_core_eval brand_relation_brands env (nnrc_ext_to_nnrc y0));
      intros; try reflexivity.
    destruct d; try reflexivity.
    assert (forall x, In x l -> (data_type x τ₁))
      by
        (apply (dcoll_wt l τ₁ τenv env (nnrc_ext_to_nnrc y0)); assumption).
    clear H4 H.
    induction l; try reflexivity.
    simpl in *.
    assert (forall x : data, In x l -> data_type x τ₁)
      by (intros; apply (H5 x); right; assumption).
    specialize (IHl H); clear H.
    rewrite (H2 ((y, a) :: env)).
    destruct (nnrc_core_eval brand_relation_brands ((y, a) :: env) (nnrc_ext_to_nnrc y1)); try reflexivity.
    - destruct ((rmap (fun d1 : data => nnrc_core_eval brand_relation_brands ((y, d1) :: env) (nnrc_ext_to_nnrc x1)) l));
      destruct ((rmap (fun d1 : data => nnrc_core_eval brand_relation_brands ((y, d1) :: env) (nnrc_ext_to_nnrc y1)) l));
      simpl in *; try congruence.
    - unfold bindings_type.
      apply Forall2_cons; try assumption.
      simpl; split; try reflexivity.
      apply (H5 a); left; reflexivity.
  Qed.
    
  (* NNRCIf *)

  Global Instance nnrc_ext_if_tproper :
    Proper (tnnrc_ext_rewrites_to ==> tnnrc_ext_rewrites_to
                              ==> tnnrc_ext_rewrites_to
                              ==> tnnrc_ext_rewrites_to) NNRCIf.
  Proof.
    unfold Proper, respectful, tnnrc_ext_rewrites_to; intros.
    inversion H2; clear H2; subst.
    specialize (H  τenv Bool H7); elim H; clear H H7; intros.
    specialize (H0  τenv τout H9); elim H0; clear H0 H9; intros.
    specialize (H1  τenv τout H10); elim H1; clear H1 H10; intros.
    econstructor; eauto.
    econstructor; eauto.
    intros; simpl.
    unfold nnrc_ext_eval,nnrc_ext_type in *; simpl.
    rewrite (H2 env H5). rewrite (H3 env H5). rewrite (H4 env H5).
    reflexivity.
  Qed.

  (* NNRCEither *)

  Global Instance nnrc_ext_either_tproper :
    Proper (tnnrc_ext_rewrites_to ==> eq ==> tnnrc_ext_rewrites_to
                              ==> eq ==> tnnrc_ext_rewrites_to
                              ==> tnnrc_ext_rewrites_to) NNRCEither.
  Proof.
    unfold Proper, respectful, tnnrc_ext_rewrites_to; intros.
    unfold nnrc_ext_eval,nnrc_ext_type in *; simpl.
    subst.
    simpl in H4.
    inversion H4; clear H4; subst.
    destruct (H _ _ H10).
    destruct (H1 _ _ H11).
    destruct (H3 _ _ H12).
    clear H H1 H3.
    simpl.
    split; [eauto | ]; intros.
    rewrite H2; trivial.
    destruct (@typed_nnrc_yields_typed_data _ _ _ _ _  H H0) as [?[??]].
    rewrite H1.
    apply data_type_Either_inv in H3.
    destruct H3 as [[?[??]]|[?[??]]]; subst.
    - apply H5. constructor; simpl; intuition; eauto.
    - eapply H7. constructor; simpl; intuition; eauto.
  Qed.

  (* NNRCGroupBy *)

  Lemma group_by_macro_eq g sl n1 n2 :
    NNRCGroupBy g sl n1 ⇒ᶜ NNRCGroupBy g sl n2
    <-> nnrc_group_by g sl n1 ⇒ᶜ nnrc_group_by g sl n2.
  Proof.
    Opaque nnrc_group_by.
    unfold tnnrc_ext_rewrites_to; intros.
    unfold nnrc_ext_type in *.
    unfold nnrc_ext_eval in *.
    split.
    - simpl. auto.
    - simpl. auto.
    Transparent nnrc_group_by.
  Qed.

  Global Instance nnrc_ext_groupby_tproper :
    Proper (eq ==> eq ==> tnnrc_ext_rewrites_to ==> tnnrc_ext_rewrites_to) NNRCGroupBy.
  Proof.
    unfold Proper, respectful; intros.
    subst.
    rewrite group_by_macro_eq.
    unfold nnrc_group_by.
    rewrite H1.
    reflexivity.
  Qed.

End TNNRCExtEq.

Notation "e1 ⇒ᶜ e2" := (tnnrc_ext_rewrites_to e1 e2) (at level 80).

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
