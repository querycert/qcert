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

(* This includes some rewrites/simplification rules for the Nested relational calculus *)

Require Import String.
Require Import List.
Require Import ListSet.
Require Import Arith.
Require Import Morphisms.
Require Import Setoid.
Require Import Decidable.
Require Import EquivDec.
Require Import Equivalence.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import NNRSimpSystem.
Require Import NNRSimpRewrite.
Require Import NNRSimpUnflatten.
Require Import TNNRSimpUnflatten.

Section TNNRSimpRewrite.
  Local Open Scope nnrs_imp.

  Context {m:basic_model}.

  Hint Immediate type_NNRSimpSkip.

  Lemma distinct_nil_trew :
    NNRSimpUnop OpDistinct (‵{||}) ⇒ᵉ ‵{||}.
  Proof.
    apply nnrs_imp_expr_eq_rewrites_to.
    - apply distinct_nil_eq.
    - intros ??? typ.
      invcs typ.
      invcs H2.
      eauto.
  Qed.

  Lemma for_nil_trew x e2 :
    (NNRSimpFor x ‵{||} e2) ⇒ˢ NNRSimpSkip.
  Proof.
    apply nnrs_imp_stmt_eq_rewrites_to.
    - apply for_nil_eq.
    - red; simpl; intros.
      repeat (match_destr; simpl; trivial).
    - eauto.
  Qed.

  (* {} ∪ e = e *)
  Lemma bagunion_nil_l_trew e :
    (NNRSimpBinop OpBagUnion ‵{||} e) ⇒ᵉ e.
  Proof.
    red; simpl; intros ??? typ.
    invcs typ.
    invcs H3.
    split.
    - trivial.
    - intros.
      match_option.
      unfold rondcoll2.
      simpl.
      eapply nnrs_imp_expr_eval_preserves_types in eqq; eauto.
      dtype_inverter; trivial.
  Qed.

  (* e ∪ {} = e *)
  Lemma bagunion_nil_r_trew e :
    (NNRSimpBinop OpBagUnion e ‵{||}) ⇒ᵉ e.
  Proof.
    red; simpl; intros ??? typ.
    invcs typ.
    invcs H3.
    split.
    - trivial.
    - intros.
      unfold olift2.
      match_option.
      eapply nnrs_imp_expr_eval_preserves_types in eqq; eauto.
      dtype_inverter.
      unfold rondcoll2, ondcoll2.
      simpl.
      rewrite bunion_nil_r; trivial.
  Qed.

  (* [] ⊕ e ≡ e *)
  Lemma concat_nil_l_trew (e:nnrs_imp_expr) :
    ‵[||] ⊕ e ⇒ᵉ e.
  Proof.
    red; simpl.
    intros ??? typ.
    invcs typ.
    invcs H5; simpl in *.
    invcs H3.
    apply dtrec_closed_inv in H1.
    invcs H1.
    split.
    - revert pf3.
      rewrite rec_concat_sort_nil_l.
      rewrite (sort_sorted_is_id _ pf2); intros.
      erewrite Rec_pr_irrel; eauto.
    - intros.
      match_option.
      eapply nnrs_imp_expr_eval_preserves_types in eqq; eauto.
      dtype_inverter.
      rewrite sort_sorted_is_id; trivial.
      apply data_type_normalized in eqq.
      invcs eqq; trivial.
  Qed.

  (* e ⊕ [] ≡ e *)
  Lemma concat_nil_r_trew (e:nnrs_imp_expr) :
    e ⊕ ‵[||]  ⇒ᵉ e.
  Proof.
    red; simpl.
    intros ??? typ.
    invcs typ.
    invcs H6; simpl in *.
    invcs H3.
    apply dtrec_closed_inv in H1.
    invcs H1.
    split.
    - revert pf3.
      rewrite rec_concat_sort_nil_r.
      rewrite (sort_sorted_is_id _ pf1); intros.
      erewrite Rec_pr_irrel; eauto.
    - intros.
      unfold olift2.
      match_option.
      eapply nnrs_imp_expr_eval_preserves_types in eqq; eauto.
      dtype_inverter.
      rewrite app_nil_r.
      rewrite sort_sorted_is_id; trivial.
      apply data_type_normalized in eqq.
      invcs eqq; trivial.
  Qed.
  
    (* [] ⊗ e ≡ {e} *)
  Lemma merge_nil_l_trew (e:nnrs_imp_expr) :
        ‵[||] ⊗ e  ⇒ᵉ   ‵{| e|}.
  Proof.
    red; simpl.
    intros ??? typ.
    invcs typ.
    invcs H5; simpl in *.
    invcs H3.
    - apply dtrec_closed_inv in H1.
      invcs H1.
      rewrite merge_bindings_nil_l in H.
      rewrite sort_sorted_is_id in H by trivial.
      invcs H.
      split.
      + econstructor; eauto.
        erewrite Rec_pr_irrel; econstructor.
      + intros.
        match_option.
        eapply nnrs_imp_expr_eval_preserves_types in eqq; eauto.
        dtype_inverter.
        unfold rec_concat_sort; simpl.
        rewrite sort_sorted_is_id; trivial.
        apply data_type_normalized in eqq.
        invcs eqq; trivial.
    - invcs H1.
      invcs H7.
      rtype_equalizer; subst.
      apply sublist_nil_r in H4; subst.
      unfold rec_concat_sort; simpl.
      rewrite merge_bindings_nil_l in H.
      rewrite sort_sorted_is_id in H by trivial.
      invcs H.
      split.
      + econstructor; eauto.
        erewrite Rec_pr_irrel; econstructor.
      + intros.
        match_option.
        eapply nnrs_imp_expr_eval_preserves_types in eqq; eauto.
        dtype_inverter.
        rewrite sort_sorted_is_id; trivial.
        apply data_type_normalized in eqq.
        invcs eqq; trivial.
  Qed.

  (* e ⊗ [] ≡ {e} *)
  Lemma merge_nil_r_trew (e:nnrs_imp_expr) :
        e ⊗ ‵[||]   ⇒ᵉ   ‵{| e|}.
  Proof.
    red; simpl.
    intros ??? typ.
    invcs typ.
    invcs H6; simpl in *.
    invcs H3.
    - apply dtrec_closed_inv in H1.
      invcs H1.
      rewrite merge_bindings_nil_r in H.
      rewrite sort_sorted_is_id in H by trivial.
      invcs H.
      split.
      + econstructor; eauto.
        erewrite Rec_pr_irrel; econstructor.
      + intros.
        unfold olift2.
        match_option.
        eapply nnrs_imp_expr_eval_preserves_types in eqq; eauto.
        dtype_inverter.
        rewrite merge_bindings_nil_r.
        rewrite sort_sorted_is_id; trivial.
        apply data_type_normalized in eqq.
        invcs eqq; trivial.
    - invcs H1.
      invcs H7.
      rtype_equalizer; subst.
      apply sublist_nil_r in H4; subst.
      rewrite merge_bindings_nil_r in H.
      rewrite sort_sorted_is_id in H by trivial.
      invcs H.
      split.
      + econstructor; eauto.
        erewrite Rec_pr_irrel; econstructor.
      + intros.
        unfold olift2.
        match_option.
        eapply nnrs_imp_expr_eval_preserves_types in eqq; eauto.
        dtype_inverter.
        rewrite merge_bindings_nil_r.
        rewrite sort_sorted_is_id; trivial.
        apply data_type_normalized in eqq.
        invcs eqq; trivial.
  Qed.

  Lemma flatten_nil_trew : ♯flatten( ‵{||}) ⇒ᵉ ‵{||}.
  Proof.
    red; simpl; intros ??? typ.
    invcs typ.
    invcs H2.
    split.
    - econstructor; simpl; repeat econstructor.
    - intros; reflexivity.
  Qed.
      
  Lemma flatten_nil_nil_trew : ♯flatten( ‵ (dcoll [dcoll []])) ⇒ᵉ ‵{||}.
  Proof.
    red; simpl; intros ??? typ.
    invcs typ.
    invcs H2.
    split.
    - econstructor; simpl; repeat econstructor.
    - intros; reflexivity.
  Qed.

  Lemma update_first_same {A B} dec (l:list (A*B)) v x:
    lookup dec l v = Some x ->
    update_first dec l v x = l.
  Proof.
    induction l; simpl; trivial; intros inn.
    repeat match_destr.
    - invcs inn; trivial.
    - rewrite IHl; trivial.
  Qed.

  Lemma assign_self_trew v : NNRSimpAssign v (NNRSimpVar v) ⇒ˢ NNRSimpSkip.
  Proof.
    red; intros Γc Γ typ.
    invcs typ.
    split; [| split]; simpl.
    - econstructor; simpl; repeat econstructor.
    - intros σc σc_bt σ σ_bt alreadydefined hsp alreadyin.
      specialize (alreadyin v).
      unfold equiv_decb in *.
      destruct (v == v); [ | congruence].
      red in hsp.
      rewrite Forall_forall in hsp.
      specialize (hsp _ (alreadyin (eq_refl _))).
      unfold equiv_dec, string_eqdec in *.
      match_option_in hsp; simpl.
      + destruct o; simpl; try contradiction.
        rewrite update_first_same; trivial.
      + red in σ_bt.
        apply lookup_none_nin in eqq.
        apply lookup_in_domain in H3.
        cut (domain Γ = domain σ); [congruence | ].
        revert σ_bt; clear.
        induction 1; trivial.
        destruct H; simpl.
        congruence.
    - intros x; simpl.
      unfold equiv_decb.
      destruct (x == v); simpl; trivial.
      destruct (v == x); simpl; trivial.
      congruence.
  Qed.

  (* unflattening *)
  Lemma unflatten_let_none_trew x (s s':nnrs_imp_stmt):
    nnrs_imp_stmt_unflatten_safe s x = Some s' ->
    NNRSimpLet x None s ⇒ˢ NNRSimpLet x None s'.
  Proof.
    red; intros eqq1 Γc Γ typ.
    invcs typ.
    rewrite (nnrs_imp_stmt_unflatten_safe_var_usage eqq1) in H2.
    split.
    - destruct (nnrs_imp_stmt_unflatten_safe_type _ _ _ eqq1 H3 τ)
               as [τ' [typ' ?]]; simpl.
      + match_destr; try congruence.
      + subst.
        simpl in typ'.
        match_destr_in typ'; try congruence.
        econstructor; eauto.
    - split.
      + intros σc σc_bt σ σ_bt.
        simpl.
        generalize (nnrs_imp_stmt_unflatten_safe_eval _ _ _ _ ((x, None)::σ) None eqq1 _ σc_bt ((x,τ)::Γ)); intros HH.
        cut_to HH; [ | constructor; simpl; intuition discriminate ].
        specialize (HH τ); simpl in HH.
        match_destr_in HH; try congruence.
        cut_to HH; trivial.
        specialize (HH None I).
        unfold lift2P, var in *.
        repeat match_option_in HH
        ; try contradiction.
        * destruct HH as [dd' [? eqq4]].
          subst.
          destruct dd'; try contradiction.
          generalize (nnrs_imp_stmt_eval_domain_stack eqq)
          ; destruct p; try discriminate
          ; destruct p
          ; simpl
          ; intros domeq.
          invcs domeq.
          destruct (equiv_dec s0 s0); try congruence.
        * destruct HH as [dd' [? eqq4]].
          subst.
          destruct dd'; try contradiction.
          generalize (nnrs_imp_stmt_eval_domain_stack eqq)
          ; destruct p; try discriminate
          ; destruct p
          ; simpl
          ; intros domeq.
          invcs domeq.
          destruct (equiv_dec s0 s0); try congruence.
      + apply stmt_var_usage_sub_let_none_proper.
         eapply nnrs_imp_stmt_unflatten_safe_var_usage_sub; eauto.
  Qed.        
  
  Lemma unflatten_let_some_trew x (e e':nnrs_imp_expr) (s s':nnrs_imp_stmt):
    nnrs_imp_expr_unflatten_init e = Some e' ->
    nnrs_imp_stmt_unflatten_safe s x = Some s' ->
    NNRSimpLet x (Some e) s ⇒ˢ NNRSimpLet x (Some e') s'.
  Proof.
    red; intros eqq_init eqq1 Γc Γ typ.
    invcs typ.
    split.
    - destruct (nnrs_imp_stmt_unflatten_safe_type _ _ _ eqq1 H4 τ)
               as [τ' [typ' ?]]; simpl.
      + match_destr; try congruence.
      + subst.
        simpl in typ'.
        match_destr_in typ'; try congruence.
        econstructor; eauto.
        eapply nnrs_imp_expr_unflatten_init_type; eauto.
    - { split.
        - intros σc σc_bt σ σ_bt.
      simpl.
      generalize (nnrs_imp_expr_unflatten_init_eval _ _ brand_relation_brands σc σ eqq_init)
      ; intros eveq.
      unfold lift2P, var in *.
      repeat match_option_in eveq; simpl; try contradiction.
      generalize (nnrs_imp_stmt_unflatten_safe_eval _ _ _ _ ((x, Some d)::σ) (Some d) eqq1 _ σc_bt ((x,τ)::Γ)); intros HH.
      generalize (nnrs_imp_expr_eval_preserves_types σc_bt σ_bt H2 _ eqq)
      ; intros dt.
      cut_to HH.
      + specialize (HH τ); simpl in HH.
        match_destr_in HH; try congruence.
        cut_to HH; trivial.
        specialize (HH (Some d0) eveq).
        unfold lift2P, var in *.
        repeat match_option_in HH
        ; try contradiction.
        * destruct HH as [dd' [? eqq6]].
          subst.
          destruct dd'; try contradiction.
          generalize (nnrs_imp_stmt_eval_domain_stack eqq2)
          ; destruct p; try discriminate
          ; destruct p
          ; simpl
          ; intros domeq.
          invcs domeq.
          destruct (equiv_dec s0 s0); try congruence.
        * destruct HH as [dd' [? eqq6]].
          subst.
          destruct dd'; try contradiction.
          generalize (nnrs_imp_stmt_eval_domain_stack eqq2)
          ; destruct p; try discriminate
          ; destruct p
          ; simpl
          ; intros domeq.
          invcs domeq.
        destruct (equiv_dec s0 s0); try congruence.
      + constructor; simpl; trivial.
        split; trivial.
        intros ? eqq3; invcs eqq3; trivial.
        - apply stmt_var_usage_sub_let_some_proper.
          + rewrite (nnrs_imp_expr_unflatten_init_free_vars _ _ eqq_init).
            reflexivity.
          + eapply nnrs_imp_stmt_unflatten_safe_var_usage_sub; eauto.
      } 
  Qed.

  (* TODO: we can do unflattening for either/for as well!
     The only thing that needs to change is the initialization check.
     In both cases, we can at least handle constants.
   *)
  
  (* renaming *)
  Lemma rename_let_trew x x' e s:
    ~ In x' (nnrs_imp_stmt_free_vars s) ->
    ~ In x' (nnrs_imp_stmt_bound_vars s) ->
    (NNRSimpLet x e s) ⇒ˢ
            (NNRSimpLet x' e (nnrs_imp_stmt_rename s x x')).
  Proof.
    intros.
    apply nnrs_imp_stmt_eq_rewrites_to.
    - apply rename_let_eq; trivial.
    - apply nnrs_imp_stmt_rename_let_var_usage_sub; trivial.
    - intros.
      invcs H1.
      + econstructor; eauto.
        apply nnrs_imp_stmt_type_rename; eauto.
      + econstructor.
        * rewrite nnrs_imp_stmt_rename_var_usage_eq_to; trivial.
        * apply nnrs_imp_stmt_type_rename; eauto.
  Qed.

  Lemma rename_for_trew x x' e s:
    ~ In x' (nnrs_imp_stmt_free_vars s) ->
    ~ In x' (nnrs_imp_stmt_bound_vars s) ->
    (NNRSimpFor x e s) ⇒ˢ
            (NNRSimpFor x' e (nnrs_imp_stmt_rename s x x')).
  Proof.
    intros.
    apply nnrs_imp_stmt_eq_rewrites_to.
    - apply rename_for_eq; trivial.
    - apply nnrs_imp_stmt_rename_for_var_usage_sub; trivial.
    - intros.
      invcs H1.
      econstructor; eauto.
      apply nnrs_imp_stmt_type_rename; eauto.
  Qed.

  Lemma rename_either_l_trew e s₁ x₁ x₁' x₂ s₂:
    ~ In x₁' (nnrs_imp_stmt_free_vars s₁) ->
    ~ In x₁' (nnrs_imp_stmt_bound_vars s₁) ->
    (NNRSimpEither e x₁ s₁ x₂ s₂) ⇒ˢ
            (NNRSimpEither e x₁' (nnrs_imp_stmt_rename s₁ x₁ x₁') x₂ s₂).
  Proof.
    intros.
    apply nnrs_imp_stmt_eq_rewrites_to.
    - apply rename_either_l_eq; trivial.
    - apply nnrs_imp_stmt_rename_either_l_var_usage_sub; trivial.
    - intros.
      invcs H1.
      econstructor; eauto.
      apply nnrs_imp_stmt_type_rename; eauto.
  Qed.

  Lemma rename_either_r_trew e s₁ x₁ x₂ x₂'  s₂:
    ~ In x₂' (nnrs_imp_stmt_free_vars s₂) ->
    ~ In x₂' (nnrs_imp_stmt_bound_vars s₂) ->
    (NNRSimpEither e x₁ s₁ x₂ s₂) ⇒ˢ
            (NNRSimpEither e x₁ s₁ x₂' (nnrs_imp_stmt_rename s₂ x₂ x₂')).
  Proof.
    intros.
    apply nnrs_imp_stmt_eq_rewrites_to.
    - apply rename_either_r_eq; trivial.
    - apply nnrs_imp_stmt_rename_either_r_var_usage_sub; trivial.
    - intros.
      invcs H1.
      econstructor; eauto.
      apply nnrs_imp_stmt_type_rename; eauto.
  Qed.

  Ltac disect_tac H stac
    := 
      unfold var in *
      ; cut_to H; unfold domain in *; [ | solve[stac]..]
      ; unfold lift2P in H
      ; (repeat match_option_in H; try contradiction).

  Ltac pcong
    := solve[repeat (match goal with
                     | [H: _ = _ |- _ ] => rewrite H in *; clear H
                     end; try tauto)].

  Ltac ren_eval_t stac
    := repeat progress (
                repeat rewrite in_app_iff in *
                ; repeat
                    match goal with
                    | [H : ~ (_ \/ _ ) |- _ ] => apply not_or in H
                    | [H : (_ \/ _ ) -> False |- _ ] => apply not_or in H
                    | [H: _ /\ _ |- _ ] => destruct H
                    | [ H : _ * _ |- _ ] => destruct H
                    | [H: _::_ = _::_ |- _ ] => invcs H
                    | [ H: domain (_ ++ _) = domain _ |- _ ] =>
                      rewrite domain_app in H
                      ; unfold domain in H
                      ; symmetry in H; apply map_app_break in H
                      ; destruct H as [? [?[?[??]]]]; subst; simpl in *
                    | [ H: map (_ ++ _) = map _ |- _ ] =>
                      rewrite map_app in H
                      ; symmetry in H; apply map_app_break in H
                      ; destruct H as [? [?[?[??]]]]; subst; simpl in *
                    | [ H: _ :: _ = map _ ?x |- _ ] =>
                      destruct x; try discriminate; simpl in H; invcs H
                    | [ H: _ :: _ = domain ?x |- _ ] =>
                      destruct x; try discriminate; simpl in H; invcs H
                    | [H : ~ In _ (remove _ _ _) |- _ ] =>
                      apply not_in_remove_impl_not_in in H; [| congruence]
                    | [H : ?x ++ _ = ?y ++ _ |- _ ] =>
                      let HH := fresh in
                      assert (HH:domain y = domain x) by
                          (unfold domain in *;
                           try (intuition congruence)
                           ; pcong)
                      ; apply app_inv_head_domain in H;[clear HH|apply HH]
                                                         

                    | [ H: forall a b c, _ -> ?x1 ++ ?dd :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                      specialize (H x1 (snd dd) x2); simpl in H
                      ; match dd with
                        | (_,_) => idtac
                        | _ => destruct dd
                        end
                      ; simpl in *
                      ; cut_to H; [ | eauto 3 | reflexivity]
                    | [ H: forall a b c, _ -> ?dd0::?x1 ++ ?dd :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                      specialize (H (dd0::x1) (snd dd) x2); simpl in H
                      ; match dd with
                        | (_,_) => idtac
                        | _ => destruct dd
                        end
                      ; simpl in *
                      ; cut_to H; [ | eauto 3 | reflexivity]
                    | [ H: forall a b c, _ -> ?dd0::?dd :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                      specialize (H (dd0::nil) (snd dd) x2); simpl in H
                      ; match dd with
                        | (_,_) => idtac
                        | _ => destruct dd
                        end
                      ; simpl in *
                      ; cut_to H; [ | eauto 3 | reflexivity]

                    end
                ; simpl in *; trivial; intros; try subst; try solve [congruence | f_equal; congruence]).          

  Ltac ren_eval_tt := ren_eval_t ltac:(try tauto; try congruence).

  Lemma let_let_coalesce_trew x₁ x₂ x₃ oe s₁ s₂ :
    x₁ <> x₂ ->
    ~ In x₁ (nnrs_imp_stmt_free_vars s₁) ->
    ~ In x₃ (nnrs_imp_stmt_free_vars s₁) ->
    ~ In x₃ (nnrs_imp_stmt_bound_vars s₁) ->
    x₁ = x₃ \/ (~ In x₃ (nnrs_imp_stmt_free_vars s₂)
                /\ ~ In x₃ (nnrs_imp_stmt_bound_vars s₂)) ->
    NNRSimpLet x₁ None
               (NNRSimpSeq
                  (NNRSimpLet x₂ oe
                              (NNRSimpSeq s₁
                                          (NNRSimpAssign x₁ (NNRSimpVar x₂))))
                  s₂)
               ⇒ˢ
               NNRSimpLet x₃
               oe
               (NNRSimpSeq (nnrs_imp_stmt_rename s₁ x₂ x₃)
                           (nnrs_imp_stmt_rename s₂ x₁ x₃)).
  Proof.
    red; intros.
    invcs H4.
    invcs H9.
    simpl in *.
    invcs H7.
    - case_eq (nnrs_imp_expr_may_use e₁ x₁)
      ; intros nin1 ; rewrite nin1 in *; try congruence.
      apply nnrs_imp_expr_may_use_free_vars_neg in nin1.
      unfold equiv_decb in H8.
      destruct (x₂ == x₁); try congruence.
      destruct (x₁ == x₂); try congruence.
      destruct (x₁ == x₁); try congruence.
      assert (used1:nnrs_imp_stmt_var_usage s₁ x₁ <> VarMayBeUsedWithoutAssignment).
      { destruct (nnrs_imp_stmt_var_usage s₁ x₁); congruence. }
      clear H8.
      invcs H12.
      invcs H8.
      invcs H11.
      simpl in *.
      destruct (string_dec x₁ x₂); try congruence.
      destruct (string_dec x₁ x₁); try congruence.
      unfold var in *.
      destruct (equiv_dec x₂ x₂); try congruence.
      invcs H12; invcs H6.
      split.
      + econstructor.
        * eapply (nnrs_imp_expr_type_unused_remove _ nil) in H9
          ; simpl; try tauto; eauto.
        * { econstructor.
            - apply nnrs_imp_stmt_type_rename_f; eauto.
              eapply (nnrs_imp_expr_type_unused_remove _ nil) in H9
              ; simpl; try tauto; eauto.
              eapply (nnrs_imp_stmt_type_unused_remove Γc ((x₂, τ1)::nil)) in H7
              ; simpl; eauto.
            - destruct H3.
              + subst.
                rewrite nnrs_imp_stmt_rename_id; trivial.
              + apply nnrs_imp_stmt_type_rename_f; eauto.
                eapply (nnrs_imp_expr_type_unused_remove _ nil) in H9
                ; simpl; try tauto; eauto.
                eapply (nnrs_imp_stmt_type_unused_remove Γc ((x₂, τ1)::nil)) in H7
                ; simpl; eauto; tauto.
          }
      + split.
        * { intros.
          generalize (nnrs_imp_expr_eval_unused brand_relation_brands σc nil); simpl
          ; intros HH; rewrite HH; clear HH; try tauto.
          case_eq ( (nnrs_imp_expr_eval brand_relation_brands σc σ e₁)); simpl; trivial.
          intros ? eqq.
          generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((x₂, Some d) :: nil) σ s₁ x₁ None); simpl; intros HH1.
          cut_to HH1; [ | tauto].
          generalize (nnrs_imp_stmt_eval_rename brand_relation_brands σc σ s₁ x₂ x₃ (Some d))
          ; simpl; intros HH2.
          cut_to HH2; [| tauto..].
          unfold var in *.
          unfold lift2P in HH1.
          repeat match_option_in HH1
          ; rewrite eqq1 in HH2
          ; repeat match_option_in HH2
          ; try contradiction
          ; simpl
          ; repeat (match_destr_in HH2; try contradiction).
          generalize (nnrs_imp_stmt_eval_domain_stack eqq0)
          ; generalize (nnrs_imp_stmt_eval_domain_stack eqq1)
          ; generalize (nnrs_imp_stmt_eval_domain_stack eqq2)
          ; intros.
          ren_eval_tt.
          destruct (s == s); try congruence.
          destruct (string_dec s0 s); try congruence.
          destruct (string_dec s0 s0); try congruence.
          unfold id; simpl.
          generalize (nnrs_imp_stmt_eval_preserves_some eqq1)
          ; simpl; intros HH.
          invcs HH.
          cut_to H17; try congruence.
          destruct o; simpl; try congruence.
          destruct H3.
          + subst.
            rewrite nnrs_imp_stmt_rename_id; trivial.
          + generalize (nnrs_imp_stmt_eval_rename brand_relation_brands σc p0 s₂ s0 x₃ (Some d0))
            ; simpl; intros HH.
            cut_to HH; [ | tauto..].
            unfold var in *.
            repeat match_option_in HH
            ; (repeat match_destr_in HH; try contradiction).
            intuition congruence.
          }
        * intros v; simpl.
          unfold equiv_decb.
          { unfold var in *.
            destruct (x₁ == v); unfold equiv, complement in *.
            - subst.
              simpl.
              apply nnrs_imp_expr_may_use_free_vars_neg in nin1.
              rewrite nin1.
              destruct (x₃ == v); trivial.
              rewrite nnrs_imp_stmt_rename_var_usage_neq by eauto.
              apply nnrs_imp_stmt_free_unassigned in H0.
              rewrite H0.
              intuition.
              replace (nnrs_imp_stmt_var_usage (nnrs_imp_stmt_rename s₂ v x₃) v)
                with VarNotUsedAndNotAssigned; trivial.
              symmetry.
              apply nnrs_imp_stmt_free_unassigned.
              rewrite nnrs_imp_stmt_rename_free_vars by eauto.
              intros inn.
              apply in_replace_all in inn.
              destruct inn; intuition congruence.
            - destruct (nnrs_imp_expr_may_use e₁ v); simpl; trivial.
              destruct (x₂ == v); unfold equiv, complement in *.
              + subst.
                destruct (x₃ == v); unfold equiv, complement in *.
                * subst.
                  destruct H3 as [?|[nin3 nin4]]; [congruence | ].
                  apply nnrs_imp_stmt_free_unassigned in nin3.
                  rewrite nin3; simpl; trivial.
                * { replace (nnrs_imp_stmt_var_usage (nnrs_imp_stmt_rename s₁ v x₃) v)
                      with VarNotUsedAndNotAssigned; trivial.
                    - rewrite nnrs_imp_stmt_rename_var_usage_neq by eauto.
                      reflexivity.
                    - symmetry.
                      apply nnrs_imp_stmt_free_unassigned.
                      rewrite nnrs_imp_stmt_rename_free_vars by eauto.
                      intros inn.
                      apply in_replace_all in inn.
                      destruct inn; intuition congruence.
                  }
              + destruct (v == x₂); [congruence | ].
                destruct (x₃ == v); unfold equiv, complement in *.
                * subst.
                  destruct H3 as [?|[nin3 nin4]]; [congruence | ].
                  apply nnrs_imp_stmt_free_unassigned in nin3.
                  apply nnrs_imp_stmt_free_unassigned in H1.
                  rewrite H1, nin3; simpl; trivial.
                * { repeat rewrite nnrs_imp_stmt_rename_var_usage_neq by eauto.
                    destruct ( nnrs_imp_stmt_var_usage s₁ v); simpl; trivial.
                    reflexivity.
                  }
          } 
    - { simpl in H9.
        unfold equiv_decb in *.
        destruct (x₂ == x₂); try congruence.
        match_case_in H9
        ; intros eqq; rewrite eqq in *; try congruence.
        invcs H12.
        invcs H11.
        invcs H12.
        simpl in *.
        destruct (string_dec x₁ x₂); try congruence.
        destruct (string_dec x₁ x₁); try congruence.
        unfold var in *.
        destruct (equiv_dec x₂ x₂); try congruence.
        invcs H13; invcs H6.
        destruct (equiv_dec x₂ x₁); try congruence.
        destruct (x₁ == x₁); try congruence.
        destruct (x₁ == x₂); try congruence.
        assert (used1:nnrs_imp_stmt_var_usage s₁ x₁ <> VarMayBeUsedWithoutAssignment).
        { destruct (nnrs_imp_stmt_var_usage s₁ x₁); congruence. }
        clear H8 c c0 e e0 e1 e2 n H9.
        split.
        - econstructor.
          + simpl.
            destruct (string_dec x₂ x₃).
            * subst.
              rewrite nnrs_imp_stmt_rename_id, eqq; congruence.
            * rewrite nnrs_imp_stmt_rename_var_usage_eq_to by trivial.
              rewrite eqq.
              congruence.
          + { econstructor.
              - apply nnrs_imp_stmt_type_rename_f; eauto.
                eapply (nnrs_imp_stmt_type_unused_remove Γc ((x₂, τ1)::nil)) in H7
                ; simpl; eauto.
              - destruct H3.
                + subst.
                  rewrite nnrs_imp_stmt_rename_id; trivial.
                + apply nnrs_imp_stmt_type_rename_f; eauto; try tauto.
            }        
        - { split.
            - intros.
              generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((x₂, None) :: nil) σ s₁ x₁ None); simpl; intros HH1.
              cut_to HH1; [ | tauto].
          generalize (nnrs_imp_stmt_eval_rename brand_relation_brands σc σ s₁ x₂ x₃ None)
          ; simpl; intros HH2.
          cut_to HH2; [| tauto..].
          unfold var in *.
          unfold lift2P in HH1.
          repeat match_option_in HH1
          ; rewrite eqq1 in HH2
          ; repeat match_option_in HH2
          ; try contradiction
          ; simpl
          ; repeat (match_destr_in HH2; try contradiction).
          generalize (nnrs_imp_stmt_eval_domain_stack eqq0)
          ; generalize (nnrs_imp_stmt_eval_domain_stack eqq1)
          ; generalize (nnrs_imp_stmt_eval_domain_stack eqq2)
          ; intros.
          destruct HH2 as [?[?[??]]]; subst.
          ren_eval_tt.
          destruct (s == s); try congruence.
          destruct (string_dec s0 s); try congruence.
          destruct (string_dec s0 s0); try congruence.
          unfold id; simpl.
          destruct (nnrs_imp_stmt_eval_must_assign_assigns eqq1 s eqq)
            as [dd ddin].
          simpl in ddin.
          match_destr_in ddin; try congruence.
          invcs ddin.
          simpl.
          destruct H3.
          + subst.
            rewrite nnrs_imp_stmt_rename_id; trivial.
          + generalize (nnrs_imp_stmt_eval_rename brand_relation_brands σc p0 s₂ s0 x₃ (Some dd))
            ; simpl; intros HH.
            cut_to HH; [ | tauto..].
            unfold var in *.
            repeat match_option_in HH
            ; (repeat match_destr_in HH; try contradiction).
            intuition congruence.
       - intros v; simpl.
         unfold equiv_decb.
         { unfold var in *.
           destruct (x₁ == v); unfold equiv, complement in *.
           - subst.
             simpl.
             destruct (x₃ == v); trivial.
             rewrite nnrs_imp_stmt_rename_var_usage_neq by eauto.
             apply nnrs_imp_stmt_free_unassigned in H0.
              rewrite H0.
              intuition.
              replace (nnrs_imp_stmt_var_usage (nnrs_imp_stmt_rename s₂ v x₃) v)
                with VarNotUsedAndNotAssigned; trivial.
              symmetry.
              apply nnrs_imp_stmt_free_unassigned.
              rewrite nnrs_imp_stmt_rename_free_vars by eauto.
              intros inn.
              apply in_replace_all in inn.
              destruct inn; intuition congruence.
           - destruct (x₂ == v); unfold equiv, complement in *.
              + subst.
                destruct (x₃ == v); unfold equiv, complement in *.
                * subst.
                  destruct H3 as [?|[nin3 nin4]]; [congruence | ].
                  apply nnrs_imp_stmt_free_unassigned in nin3.
                  rewrite nin3; simpl; trivial.
                * { replace (nnrs_imp_stmt_var_usage (nnrs_imp_stmt_rename s₁ v x₃) v)
                      with VarNotUsedAndNotAssigned; trivial.
                    - rewrite nnrs_imp_stmt_rename_var_usage_neq by eauto.
                      reflexivity.
                    - symmetry.
                      apply nnrs_imp_stmt_free_unassigned.
                      rewrite nnrs_imp_stmt_rename_free_vars by eauto.
                      intros inn.
                      apply in_replace_all in inn.
                      destruct inn; intuition congruence.
                  }
              + destruct (v == x₂); [congruence | ].
                destruct (x₃ == v); unfold equiv, complement in *.
                * subst.
                  destruct H3 as [?|[nin3 nin4]]; [congruence | ].
                  apply nnrs_imp_stmt_free_unassigned in nin3.
                  apply nnrs_imp_stmt_free_unassigned in H1.
                  rewrite H1, nin3; simpl; trivial.
                * { repeat rewrite nnrs_imp_stmt_rename_var_usage_neq by eauto.
                    destruct ( nnrs_imp_stmt_var_usage s₁ v); simpl; trivial.
                    reflexivity.
                  }
             } 
          }
      } 
  Qed.
  
  Lemma let_let_coalesce_trew1 x₁ x₂ oe s₁ s₂ :
    x₁ <> x₂ ->
    ~ In x₁ (nnrs_imp_stmt_free_vars s₁) ->
    ~ In x₁ (nnrs_imp_stmt_bound_vars s₁) ->
    NNRSimpLet x₁ None
               (NNRSimpSeq
                  (NNRSimpLet x₂ oe
                              (NNRSimpSeq s₁
                                          (NNRSimpAssign x₁ (NNRSimpVar x₂))))
                  s₂)
               ⇒ˢ
               NNRSimpLet x₁ oe
               (NNRSimpSeq (nnrs_imp_stmt_rename s₁ x₂ x₁)
                           s₂).
  Proof.
    intros.
    generalize (let_let_coalesce_trew x₁ x₂ x₁ oe s₁ s₂)
    ; simpl; intros HH.
    rewrite nnrs_imp_stmt_rename_id in HH.
    apply HH; try tauto.
  Qed.

  Lemma for_for_fuse_trew x₁ tmp₁ source expr tmp₂ expr₂ tmp₃ body rest :
    x₁ <> tmp₁ ->
    x₁ <> tmp₂ ->
    tmp₂ <> tmp₁ ->
    ~ In x₁ (nnrs_imp_expr_free_vars expr) ->
    ~ In x₁ (nnrs_imp_expr_free_vars source) ->
    ~ In tmp₂ (nnrs_imp_expr_free_vars source) ->
    ~ In tmp₂ (nnrs_imp_expr_free_vars expr) ->
    ~ In tmp₁ (nnrs_imp_stmt_free_vars body) ->
    ~ In x₁ (nnrs_imp_stmt_free_vars body) ->
    ~ In x₁ (nnrs_imp_stmt_free_vars rest) ->
    liftP (fun e => ~ In x₁ (nnrs_imp_expr_free_vars e)) expr₂ ->
    disjoint (nnrs_imp_stmt_maybewritten_vars body) (nnrs_imp_expr_free_vars expr) ->
    NNRSimpLet x₁ (Some (NNRSimpConst (dcoll nil)))
                   (NNRSimpSeq
                      (NNRSimpFor tmp₁ source
                                  (NNRSimpAssign x₁
                                              (NNRSimpBinop
                                                 OpBagUnion
                                                 (NNRSimpVar x₁)
                                                 (NNRSimpUnop OpBag expr))))
                      (NNRSimpLet tmp₂ expr₂
                                  (NNRSimpSeq
                                     (NNRSimpFor tmp₃ (NNRSimpVar x₁)
                                                 body
                                     )
                                     rest)))
                   ⇒ˢ
                   (NNRSimpLet tmp₂ expr₂
                               (NNRSimpSeq
                                  (NNRSimpFor tmp₁ source
                                              (NNRSimpLet tmp₃ (Some expr) body))
                                  rest)).
      Proof.
        intros.
        apply nnrs_imp_stmt_eq_rewrites_to.
        - apply for_for_fuse_eq; trivial.
        - intros v; simpl.
          unfold equiv_decb.
          destruct (x₁ == v); simpl; unfold equiv, complement in *.
          + subst.
            destruct (tmp₂ == v); [congruence | ].
            destruct (tmp₁ == v); [congruence | ].
            apply nnrs_imp_expr_may_use_free_vars_neg in H2.
            apply nnrs_imp_expr_may_use_free_vars_neg in H3.
            apply nnrs_imp_stmt_free_unassigned in H7.
            apply nnrs_imp_stmt_free_unassigned in H8.
            rewrite H2, H3, H7, H8.
            destruct expr₂.
            * simpl in *.
              apply nnrs_imp_expr_may_use_free_vars_neg in H9.
              rewrite H9.
              destruct (tmp₃ == v); trivial.
            * destruct (tmp₃ == v); trivial.
          + destruct (nnrs_imp_expr_may_use source v); simpl; trivial.
             destruct (v == x₁); [congruence | ]; simpl.
             destruct (tmp₁ == v); unfold equiv, complement in *.
            * subst.
              match_destr; simpl; trivial.
              apply nnrs_imp_stmt_free_unassigned in H6.
              rewrite H6.
              destruct (tmp₂ == v); simpl; trivial.
              destruct (tmp₃ == v); reflexivity.
            * destruct (nnrs_imp_expr_may_use expr v); simpl; trivial.
              match_destr; simpl; trivial.
              destruct (tmp₂ == v); simpl; trivial.
              destruct (tmp₃ == v); simpl; try reflexivity.
        - intros ? ? typ.
          invcs typ.
          invcs H16.
          invcs H15.
          invcs H19.
          invcs H15.
          invcs H23.
          invcs H22.
          invcs H15.
          invcs H20.
          rtype_equalizer; subst.
          simpl in *.
          unfold equiv_dec, string_eqdec in *.
          destruct (string_dec x₁ tmp₁); try congruence.
          destruct (string_dec x₁ x₁); try congruence.
          invcs H18.
          invcs H13.
          invcs H17.
          + invcs H19.
            invcs H17.
            invcs H19.
            simpl in *.
            unfold equiv_dec, string_eqdec in *.
            destruct (string_dec x₁ tmp₂); try congruence.
            destruct (string_dec x₁ x₁); try congruence.
            invcs H13; rtype_equalizer; subst.
            { econstructor.
              - apply (nnrs_imp_expr_type_unused_remove Γc nil Γ) in H15; eauto.
              - econstructor.
                + econstructor.
                  * apply (nnrs_imp_expr_type_unused_remove Γc nil Γ) in H16; eauto.
                    apply (nnrs_imp_expr_type_unused_add Γc nil Γ); eauto.
                  * { econstructor.
                      - apply (nnrs_imp_expr_type_unused_remove Γc ((tmp₁, τ0)::nil) Γ) in H21; eauto.
                        apply (nnrs_imp_expr_type_unused_add Γc ((tmp₁, τ0)::nil) Γ); eauto.
                      - apply (nnrs_imp_stmt_type_unused_remove Γc ((tmp₃, τ1) :: (tmp₂, τ) ::nil) Γ) in H22; eauto.
                        apply (nnrs_imp_stmt_type_unused_add Γc ((tmp₃, τ1)::nil) ((tmp₂, τ)::Γ)); eauto.
                    }
                + apply (nnrs_imp_stmt_type_unused_remove Γc ((tmp₂, τ)::nil) Γ) in H18; eauto.
            }
          + invcs H19.
            invcs H17.
            invcs H19.
            simpl in *.
            unfold equiv_decb, equiv_dec, string_eqdec in *.
            destruct (string_dec x₁ tmp₂); try congruence.
            destruct (string_dec x₁ x₁); try congruence.
            destruct (string_dec tmp₂ x₁); try congruence.
            invcs H13; rtype_equalizer; subst.
            { econstructor.
              - simpl.
                unfold equiv_decb, equiv_dec, string_eqdec in *.
                destruct (string_dec tmp₁ tmp₂); try congruence.
                rewrite <- nnrs_imp_expr_may_use_free_vars_neg in H4, H5.
                rewrite H4, H5.
                destruct (string_dec tmp₃ tmp₂); simpl; trivial.
              - eapply (nnrs_imp_stmt_type_unused_remove Γc ((tmp₂, τ)::nil) Γ) in H18; eauto.
                econstructor; eauto.
                econstructor.
                + apply (nnrs_imp_expr_type_unused_remove Γc nil Γ) in H16; eauto.
                   apply (nnrs_imp_expr_type_unused_add Γc nil Γ); eauto.
                + econstructor.
                  * apply (nnrs_imp_expr_type_unused_remove Γc ((tmp₁, τ0)::nil) Γ) in H21; eauto.
                    apply (nnrs_imp_expr_type_unused_add Γc ((tmp₁, τ0)::nil) Γ); eauto.
                  * apply (nnrs_imp_stmt_type_unused_remove Γc ((tmp₃, τ1) :: (tmp₂, τ) ::nil) Γ) in H22; eauto.
                    apply (nnrs_imp_stmt_type_unused_add Γc ((tmp₃, τ1)::nil) ((tmp₂, τ)::Γ)); eauto.
            }
      Qed.

End TNNRSimpRewrite.
