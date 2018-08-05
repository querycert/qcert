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
Require Import Bool.
Require Import Morphisms.
Require Import Setoid.
Require Import Decidable.
Require Import EquivDec.
Require Import Equivalence.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import NNRSimpSystem.
Require Import NNRSimpUnflatten.

Section TNNRSimpUnflatten.
  Local Open Scope nnrs_imp.

  Context {m:basic_model}.

  Hint Immediate type_NNRSimpSkip.


  Section eval.
    (* these evaluation lemmas require the Coll (Coll constraint).
       We could probably write them via checking the shape of the 
       evaluated data instead, but since we ultimately care about 
       well-typed expresions anyway, this seems more straightforward.
     *)
    Lemma nnrs_imp_expr_unflatten_write_eval e e' v σc σ :
      nnrs_imp_expr_unflatten_write e v = Some e' ->
      forall Γc,
        bindings_type σc Γc ->
        forall Γ,
          pd_bindings_type σ Γ ->
          forall τ,
            [ Γc ; Γ  ⊢ e ▷ Coll (Coll τ) ] ->
            forall d d',
              lookup equiv_dec σ v = Some d ->
              lift2P flattens_to d d' ->
              lift2P
                flattens_to
                (nnrs_imp_expr_eval brand_relation_brands σc σ e)
                (nnrs_imp_expr_eval brand_relation_brands σc (update_first equiv_dec σ v d') e').
    Proof.
      intros eqq Γc Γc_bt Γ Γ_bt  τ typ d d' inn ft.
      revert e' eqq typ.
      nnrs_imp_expr_cases (induction e) Case
      ; simpl ; intros e' eqq typ
      ; try discriminate.
      - Case "NNRSimpVar"%string.
        match_destr_in eqq.
        invcs eqq; simpl.
        rewrite e.
        unfold var in *.
        rewrite inn.
        rewrite lookup_update_eq_in; eauto.
        apply lookup_in_domain in inn; trivial.
      - Case "NNRSimpConst"%string.
        destruct d0; try discriminate.
        destruct l; try discriminate.
        + invcs eqq; simpl; reflexivity.
        + destruct d0; try discriminate.
          destruct l; try discriminate.
          invcs eqq; simpl.
          unfold oflatten; simpl.
          rewrite app_nil_r; trivial.
      - Case "NNRSimpBinop"%string.
        destruct b; try discriminate.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
        simpl.
        invcs typ.
        invcs H3.
        apply Coll_right_inv in H; subst.
        specialize (IHe1 _ eqq1 H5).
        specialize (IHe2 _ eqq2 H6).
        unfold lift2P in *; simpl.
        repeat match_option_in IHe1
        ; simpl in *
        ; try contradiction.
        repeat match_option_in IHe2
        ; simpl in *
        ; try contradiction.

        destruct d0; simpl in *; try contradiction
        ; destruct d1; simpl in *; try contradiction
        ; trivial.
        destruct d2; simpl in *; try contradiction
        ; destruct d3; simpl in *; try contradiction
        ; trivial.
        unfold bunion.
        erewrite oflatten_app; eauto.
      - Case "NNRSimpUnop"%string.
        destruct u; simpl; try discriminate.
        match_destr_in eqq.
        invcs eqq.
        invcs typ.
        invcs H2.
        apply Coll_right_inv in H.
        rtype_equalizer; subst.
        replace (nnrs_imp_expr_eval brand_relation_brands σc (update_first equiv_dec σ v d') e')
          with (nnrs_imp_expr_eval brand_relation_brands σc σ e').
        + 
          case_eq (nnrs_imp_expr_eval brand_relation_brands σc σ e'); simpl; trivial.
          intros ? eqq.
          eapply nnrs_imp_expr_eval_preserves_types in eqq; eauto.
          dtype_inverter.
          rewrite oflatten_cons with (r':=nil); simpl; trivial.
          rewrite app_nil_r; trivial.
        + eapply nnrs_imp_expr_eval_same.
          red; intros.
          destruct (x == v).
          * rewrite e in *; tauto.
          * rewrite lookup_update_neq; eauto.
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

    Ltac fuse_t stac
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

                      | [ H: forall a b c, _ -> ?x1 :: ?dd :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                        specialize (H (x1::nil) (snd dd) x2); simpl in H
                        ; match dd with
                          | (_,_) => idtac
                          | _ => destruct dd
                          end
                        ; simpl in *
                        ; cut_to H; [ | eauto 3 | reflexivity]
                      end
                  ; simpl in *; trivial; intros; try subst; try contradiction; try solve [congruence | f_equal; congruence]).

    Ltac fuse_tt := fuse_t ltac:(try tauto; try congruence).

    Lemma nnrs_imp_stmt_unflatten_eval s s' v σc σ d :
      nnrs_imp_stmt_unflatten s v = Some s' ->
      forall Γc,
        bindings_type σc Γc ->
        forall Γ,
          pd_bindings_type σ Γ ->
          forall τ,
            lookup equiv_dec σ v = Some d ->
            lookup equiv_dec Γ v = Some (Coll (Coll τ)) ->
            [ Γc ; Γ  ⊢ s ] ->
            forall d',
              lift2P flattens_to d d' ->
              lift2P
                (fun σ₁' σ₂' =>
                   match lookup equiv_dec σ₁' v with
                   | Some dd => 
                     exists dd',
                     σ₂' = update_first equiv_dec σ₁' v dd'
                     /\ lift2P flattens_to dd dd'
                   | None => False
                   end
                )
                (nnrs_imp_stmt_eval brand_relation_brands σc s σ)
                (nnrs_imp_stmt_eval brand_relation_brands σc s' (update_first equiv_dec σ v d')).
    Proof.
      intros eqq Γc σc_bt.
      revert s' σ d eqq.
      nnrs_imp_stmt_cases (induction s) Case
      ; simpl ; intros s' σ d eqq Γ σ_bt τ σinn Γinn typ d' ft.
      - Case "NNRSimpSkip"%string.
        invcs eqq; simpl; intros.
        unfold var in *.
        rewrite σinn.
        eauto.
      - Case "NNRSimpSeq"%string.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1 [eqq2 ?]] ]; subst; simpl.
        invcs typ.
        specialize (IHs1 _ _ _ eqq1 _ σ_bt _ σinn Γinn H2 _ ft).
        unfold lift2P in *.
        do 3 (match_option_in IHs1; simpl in *
              ; try contradiction).
        destruct IHs1 as [dd' [? ft']].
        subst.
        generalize (nnrs_imp_stmt_eval_preserves_types _ σc_bt σ_bt H2 _ eqq)
        ; intros p_bt.
        eapply IHs2; eauto.
      - Case "NNRSimpAssign"%string.
        destruct (equiv_dec v0 v); unfold equiv, complement in *.
        + subst; simpl in *.
          apply some_lift in eqq.
          destruct eqq as [? eqq ?]; subst.
          invcs typ.
          unfold equiv_dec, string_eqdec in *.
          rewrite Γinn in H3.
          invcs H3.
          generalize (nnrs_imp_expr_unflatten_write_eval _ _ _ _ _
                                                         eqq _ σc_bt _ σ_bt _ H2 _ _ σinn ft)
          ; intros ft'.
          simpl.
          unfold lift2P in ft'.
          unfold equiv_dec, string_eqdec in *.

          repeat match_option_in ft'
          ; simpl in *
          ; try contradiction.
          rewrite σinn.
          simpl.
          repeat rewrite lookup_update_eq_in.
          * exists (Some d1).
            repeat rewrite update_first_update_first_eq; simpl.
            tauto.
          * apply lookup_in_domain in σinn; trivial.
          * apply lookup_in_domain in σinn; trivial.
        + apply some_lift in eqq.
          destruct eqq as [? eqq ?]; subst.
          invcs typ.
          rewrite (nnrs_imp_expr_unflatten_read_eval _ _ _ brand_relation_brands σc _ _ _
                                                     eqq σinn ft).
          simpl.
          unfold equiv_dec, string_eqdec, var in *.
          match_option; simpl; trivial.
          rewrite lookup_update_neq by eauto.
          match_option; simpl; trivial.
          rewrite lookup_update_neq by eauto.
          rewrite σinn.
          exists d'.
          split; trivial.
          rewrite update_first_update_first_neq_swap; eauto.
      - Case "NNRSimpLet"%string.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1 [eqq2 ?]] ]; subst; simpl.
        invcs typ.
        + simpl in eqq1.
          apply some_lift in eqq1.
          destruct eqq1 as [? eqq1 ?]; subst.
          rewrite <- (nnrs_imp_expr_unflatten_read_eval _ _ _ brand_relation_brands σc _ _ _
                                                        eqq1 σinn ft).
          case_eq (nnrs_imp_expr_eval brand_relation_brands σc σ e₁); simpl; trivial
          ; intros ? eveqq.
          match_destr_in eqq2; unfold equiv, complement in *.
          * subst.
            invcs eqq2.
            destruct (in_update_break_first _ σinn d')
              as [?[? [? [eqq2 nin]]]]
            ; subst.
            rewrite eqq2.
            generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((v, Some d0)::x) x2 x0 v d)
            ; simpl ; intros HH1.
            cut_to HH1; [| tauto].
            generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((v, Some d0)::x) x2 x0 v d')
            ; simpl ; intros HH2.
            cut_to HH2; [| tauto].
            unfold lift2P, var in *.
            repeat match_option_in HH1
            ; rewrite eqq0 in HH2
            ; try contradiction
            ; repeat match_option_in HH2
            ; try contradiction.
            apply nnrs_imp_stmt_eval_domain_stack in eqq.
            apply nnrs_imp_stmt_eval_domain_stack in eqq3.
            fuse_tt.
            rewrite lookup_app.
            rewrite lookup_nin_none; [|  unfold domain in *; congruence].
            simpl.
            destruct (equiv_dec s s); [| congruence].
            exists o0.
            rewrite update_app_nin; [|  unfold domain in *; congruence].
            simpl.
            destruct (equiv_dec s s); [| congruence].
            specialize (HH1 ((s,o1)::x5) o2 x6); simpl in HH1.
            cut_to HH1; [| unfold domain in *; congruence | trivial].
            specialize (HH2 ((s,o)::x3) o0 x4); simpl in HH2.
            cut_to HH2; [| unfold domain in *; congruence | trivial].
            destruct HH1; subst.
            fuse_tt.
            split; trivial.
          * assert (σ_bt_cons : pd_bindings_type ((v0, Some d0) :: σ) ((v0, τ0) :: Γ)).
            {
              econstructor; simpl; trivial.
              split; trivial; intros.
              invcs H.
              eapply nnrs_imp_expr_eval_preserves_types  in eveqq; eauto.
            } 
            specialize (IHs _ ((v0, Some d0)::σ) d eqq2 ((v0, τ0) :: Γ) σ_bt_cons τ).
            cut_to IHs; simpl; trivial; try solve [match_destr; congruence].
            specialize (IHs _ ft).
            simpl in IHs.
            unfold var in *.
            destruct (equiv_dec v v0); try congruence.
            unfold lift2P in *.
            do 2 match_option_in IHs
            ; try contradiction.
            generalize (nnrs_imp_stmt_eval_domain_stack eqq)
            ; generalize (nnrs_imp_stmt_eval_domain_stack eqq0)
            ; intros.
            fuse_tt.
            destruct (equiv_dec v s0); [congruence| ].
            match_option_in IHs.
            destruct IHs as [dd' [HH1 HH2]].
            invcs HH1.
            exists dd'; split; trivial.
        + simpl in eqq1; invcs eqq1.
          match_destr_in eqq2; unfold equiv, complement in *.
          * subst.
            invcs eqq2.
            destruct (in_update_break_first _ σinn d')
              as [?[? [? [eqq2 nin]]]]
            ; subst.
            rewrite eqq2.
            generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((v, None)::x) x1 x0 v d)
            ; simpl ; intros HH1.
            cut_to HH1; [| tauto].
            generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((v, None)::x) x1 x0 v d')
            ; simpl ; intros HH2.
            cut_to HH2; [| tauto].
            unfold lift2P, var in *.
            repeat match_option_in HH1
            ; rewrite eqq0 in HH2
            ; try contradiction
            ; repeat match_option_in HH2
            ; try contradiction.
            apply nnrs_imp_stmt_eval_domain_stack in eqq.
            apply nnrs_imp_stmt_eval_domain_stack in eqq1.
            fuse_tt.
            rewrite lookup_app.
            rewrite lookup_nin_none; [|  unfold domain in *; congruence].
            simpl.
            destruct (equiv_dec s s); [| congruence].
            exists o0.
            rewrite update_app_nin; [|  unfold domain in *; congruence].
            simpl.
            destruct (equiv_dec s s); [| congruence].
            specialize (HH1 ((s,o1)::x4) o2 x5); simpl in HH1.
            cut_to HH1; [| unfold domain in *; congruence | trivial].
            specialize (HH2 ((s,o)::x2) o0 x3); simpl in HH2.
            cut_to HH2; [| unfold domain in *; congruence | trivial].
            destruct HH1; subst.
            fuse_tt.
            split; trivial.
          * assert (σ_bt_cons : pd_bindings_type ((v0, None) :: σ) ((v0, τ0) :: Γ)).
            {
              econstructor; simpl; trivial.
              split; trivial; intros.
              invcs H.
            } 
            specialize (IHs _ ((v0, None)::σ) d eqq2 ((v0, τ0) :: Γ) σ_bt_cons τ).
            cut_to IHs; simpl; trivial; try solve [match_destr; congruence].
            specialize (IHs _ ft).
            simpl in IHs.
            unfold var in *.
            destruct (equiv_dec v v0); try congruence.
            unfold lift2P in *.
            do 2 match_option_in IHs
            ; try contradiction.
            generalize (nnrs_imp_stmt_eval_domain_stack eqq)
            ; generalize (nnrs_imp_stmt_eval_domain_stack eqq0)
            ; intros.
            fuse_tt.
            destruct (equiv_dec v s0); [congruence| ].
            match_option_in IHs.
            destruct IHs as [dd' [HH1 HH2]].
            invcs HH1.
            exists dd'; split; trivial.
      - Case "NNRSimpFor"%string.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1 [eqq2 ?]] ]; subst; simpl.
        invcs typ.
        rewrite <- (nnrs_imp_expr_unflatten_read_eval _ _ _ brand_relation_brands σc _ _ _
                                                      eqq1 σinn ft).
        case_eq (nnrs_imp_expr_eval brand_relation_brands σc σ n); simpl; trivial
        ; intros ? eveqq.
        eapply nnrs_imp_expr_eval_preserves_types  in eveqq; eauto.
        dtype_inverter.
        invcs eveqq; rtype_equalizer; subst.
        clear x n eqq1 H2.
        revert σ Γ d d' σinn σ_bt H4 Γinn ft.
        induction d0; intros σ Γ d d' σinn σ_bt typ Γinn ft; simpl; unfold var in *.
        + rewrite σinn; eauto.
        + invcs H1.
          specialize (IHd0 H3); clear H3.
          match_destr_in eqq2; unfold equiv, complement in *.
          * subst.
            invcs eqq2.
            destruct (in_update_break_first _ σinn d')
              as [?[? [? [eqq2 nin]]]]
            ; subst.
            rewrite eqq2.
            clear eqq2.
            generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((v, Some a)::x) x1 x0 v d)
            ; simpl ; intros HH1.
            cut_to HH1; [| tauto].
            generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((v, Some a)::x) x1 x0 v d')
            ; simpl ; intros HH2.
            cut_to HH2; [| tauto].
            unfold lift2P, var in *.
            repeat match_option_in HH1
            ; rewrite eqq0 in HH2
            ; try contradiction
            ; repeat match_option_in HH2
            ; try contradiction.
            generalize (nnrs_imp_stmt_eval_domain_stack eqq).
            generalize (nnrs_imp_stmt_eval_domain_stack eqq1).
            fuse_tt.
            specialize (HH1 ((s,o)::x2) o0 x3); simpl in HH1.
            cut_to HH1; [| unfold domain in *; congruence | trivial].
            specialize (HH2 ((s,o1)::x4) o2 x5); simpl in HH2.
            cut_to HH2; [| unfold domain in *; congruence | trivial].
            destruct HH1; subst.
            fuse_tt.
            { eapply nnrs_imp_stmt_eval_preserves_types  in eqq; eauto.
              - specialize (IHd0 (x4 ++ (s, o0) :: x5) Γ o0 o2).
                { cut_to IHd0; trivial.
                  - unfold lift2P in *.
                    rewrite update_app_nin in IHd0; [ | unfold domain in *; congruence].
                    simpl in IHd0.
                    destruct (equiv_dec s s); [| congruence].
                    trivial.
                  - rewrite lookup_app.
                    rewrite lookup_nin_none; simpl.
                    + destruct (equiv_dec s s); [| congruence]; trivial.
                    + unfold domain in *; congruence.
                  - invcs eqq; auto.
                } 
              - econstructor; simpl; trivial; split; trivial; intros ? eqqq; invcs eqqq; trivial.
            }
          * assert (σ_bt_cons : pd_bindings_type ((v0, Some a) :: σ) ((v0, τ0) :: Γ)).
            {
              econstructor; simpl; trivial.
              split; trivial; intros.
              invcs H; trivial.
            } 
            specialize (IHs _ ((v0, Some a)::σ) d eqq2 ((v0, τ0) :: Γ) σ_bt_cons τ).
            cut_to IHs; simpl; trivial; try solve [match_destr; congruence].
            specialize (IHs _ ft).
            simpl in IHs.
            unfold var in *.
            destruct (equiv_dec v v0); try congruence.
            unfold lift2P in *.
            do 2 match_option_in IHs
            ; try contradiction.
            generalize (nnrs_imp_stmt_eval_domain_stack eqq)
            ; generalize (nnrs_imp_stmt_eval_domain_stack eqq0)
            ; intros.
            fuse_tt.
            destruct (equiv_dec v s0); [congruence| ].
            match_option_in IHs; try contradiction.
            destruct IHs as [dd' [HH1 HH2]].
            invcs HH1.
            clear H3.
            generalize (nnrs_imp_stmt_eval_preserves_types _ σc_bt σ_bt_cons typ _ eqq)
            ; intros p_bt.
            invcs p_bt.
            specialize (IHd0 p1 Γ o1 dd').
            cut_to IHd0; trivial.
      - Case "NNRSimpIf"%string.
        unfold lift3 in eqq.
        repeat match_option_in eqq.
        invcs eqq; simpl in *.
        invcs typ.
        rewrite <- (nnrs_imp_expr_unflatten_read_eval _ _ _ brand_relation_brands σc _ _ _
                                                      eqq0 σinn ft).
        match_option; simpl; trivial.
        destruct d0; simpl; trivial.
        destruct b; eauto.
      - Case "NNRSimpEither"%string.
        unfold lift3 in eqq.
        repeat match_option_in eqq.
        invcs eqq; simpl in *.
        invcs typ.
        rewrite <- (nnrs_imp_expr_unflatten_read_eval _ _ _ brand_relation_brands σc _ _ _
                                                      eqq0 σinn ft).
        match_option; simpl; trivial.
        eapply nnrs_imp_expr_eval_preserves_types  in eqq; eauto.
        destruct d0; simpl; trivial
        ; invcs eqq; rtype_equalizer; subst.
        + match_destr_in eqq1; unfold equiv, complement in *.
          * subst.
            invcs eqq1.
            destruct (in_update_break_first _ σinn d')
              as [?[? [? [eqq1 nin]]]]
            ; subst.
            rewrite eqq1.
            generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((v, Some d0)::x) x0 n1 v d)
            ; simpl ; intros HH1.
            cut_to HH1; [| tauto].
            generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((v, Some d0)::x) x0 n1 v d')
            ; simpl ; intros HH2.
            cut_to HH2; [| tauto].
            unfold lift2P, var in *.
            repeat match_option_in HH1
            ; rewrite eqq3 in HH2
            ; try contradiction
            ; repeat match_option_in HH2
            ; try contradiction.
            apply nnrs_imp_stmt_eval_domain_stack in eqq.
            apply nnrs_imp_stmt_eval_domain_stack in eqq4.
            fuse_tt.
            rewrite lookup_app.
            rewrite lookup_nin_none; [|  unfold domain in *; congruence].
            simpl.
            destruct (equiv_dec s s); [| congruence].
            exists o0.
            rewrite update_app_nin; [|  unfold domain in *; congruence].
            simpl.
            destruct (equiv_dec s s); [| congruence].
            specialize (HH1 ((s,o1)::x3) o2 x4); simpl in HH1.
            cut_to HH1; [| unfold domain in *; congruence | trivial].
            specialize (HH2 ((s,o)::x1) o0 x2); simpl in HH2.
            cut_to HH2; [| unfold domain in *; congruence | trivial].
            destruct HH1; subst.
            fuse_tt.
            split; trivial.
          * assert (σ_bt_cons : pd_bindings_type ((v0, Some d0) :: σ) ((v0, τl) :: Γ)).
            {
              econstructor; simpl; trivial.
              split; trivial; intros.
              invcs H; trivial.
            } 
            specialize (IHs1 _ ((v0, Some d0)::σ) d eqq1 ((v0, τl) :: Γ) σ_bt_cons τ).
            cut_to IHs1; simpl; trivial; try solve [match_destr; congruence].
            specialize (IHs1 _ ft).
            simpl in IHs1.
            unfold var in *.
            destruct (equiv_dec v v0); try congruence.
            unfold lift2P in *.
            do 2 match_option_in IHs1
            ; try contradiction.
            generalize (nnrs_imp_stmt_eval_domain_stack eqq)
            ; generalize (nnrs_imp_stmt_eval_domain_stack eqq3)
            ; intros.
            fuse_tt.
            destruct (equiv_dec v s); [congruence| ].
            match_option_in IHs1.
            destruct IHs1 as [dd' [HH1 HH2]].
            invcs HH1.
            exists dd'; split; trivial. 
        + match_destr_in eqq2; unfold equiv, complement in *.
          * subst.
            invcs eqq2.
            destruct (in_update_break_first _ σinn d')
              as [?[? [? [eqq2 nin]]]]
            ; subst.
            rewrite eqq2.
            generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((v, Some d0)::x) x0 n2 v d)
            ; simpl ; intros HH1.
            cut_to HH1; [| tauto].
            generalize (nnrs_imp_stmt_eval_unused brand_relation_brands σc ((v, Some d0)::x) x0 n2 v d')
            ; simpl ; intros HH2.
            cut_to HH2; [| tauto].
            unfold lift2P, var in *.
            repeat match_option_in HH1
            ; rewrite eqq3 in HH2
            ; try contradiction
            ; repeat match_option_in HH2
            ; try contradiction.
            apply nnrs_imp_stmt_eval_domain_stack in eqq.
            apply nnrs_imp_stmt_eval_domain_stack in eqq4.
            fuse_tt.
            rewrite lookup_app.
            rewrite lookup_nin_none; [|  unfold domain in *; congruence].
            simpl.
            destruct (equiv_dec s s); [| congruence].
            exists o0.
            rewrite update_app_nin; [|  unfold domain in *; congruence].
            simpl.
            destruct (equiv_dec s s); [| congruence].
            specialize (HH1 ((s,o1)::x3) o2 x4); simpl in HH1.
            cut_to HH1; [| unfold domain in *; congruence | trivial].
            specialize (HH2 ((s,o)::x1) o0 x2); simpl in HH2.
            cut_to HH2; [| unfold domain in *; congruence | trivial].
            destruct HH1; subst.
            fuse_tt.
            split; trivial.
          * assert (σ_bt_cons : pd_bindings_type ((v1, Some d0) :: σ) ((v1, τr) :: Γ)).
            {
              econstructor; simpl; trivial.
              split; trivial; intros.
              invcs H; trivial.
            } 
            specialize (IHs2 _ ((v1, Some d0)::σ) d eqq2 ((v1, τr) :: Γ) σ_bt_cons τ).
            cut_to IHs2; simpl; trivial; try solve [match_destr; congruence].
            specialize (IHs2 _ ft).
            simpl in IHs2.
            unfold var in *.
            destruct (equiv_dec v v1); try congruence.
            unfold lift2P in *.
            do 2 match_option_in IHs2
            ; try contradiction.
            generalize (nnrs_imp_stmt_eval_domain_stack eqq)
            ; generalize (nnrs_imp_stmt_eval_domain_stack eqq3)
            ; intros.
            fuse_tt.
            destruct (equiv_dec v s); [congruence| ].
            match_option_in IHs2.
            destruct IHs2 as [dd' [HH1 HH2]].
            invcs HH1.
            exists dd'; split; trivial. 
    Qed.

  End eval.
  
  Section typ.

    Lemma nnrs_imp_expr_unflatten_init_type {e e':nnrs_imp_expr}:
      nnrs_imp_expr_unflatten_init e = Some e' ->
      forall {Γc Γ τ},
        [ Γc ; Γ  ⊢ e ▷ Coll (Coll τ) ]  ->
        [ Γc ; Γ  ⊢ e' ▷ Coll τ ].
    Proof.
      revert e'.
      nnrs_imp_expr_cases (induction e) Case
      ; simpl ; intros e' eqq Γc Γ τ typ
      ; try discriminate.
      - Case "NNRSimpConst"%string.
        destruct d; simpl in *
        ; invcs eqq.
        invcs typ.
        invcs H2.
        apply Coll_right_inv in H1; subst.
        destruct l; invcs H0; simpl.
        + repeat econstructor.
        + simpl in H3; invcs H3.
          invcs H2; rtype_equalizer; subst.
          destruct d; try discriminate.
          destruct l; try discriminate.
          invcs H1.
          econstructor.
          rewrite <- H.
          econstructor; trivial.
      - Case "NNRSimpBinop"%string.
        destruct b; try discriminate.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
        invcs typ.
        invcs H3.
        apply Coll_right_inv in H; subst.
        econstructor; eauto.
        econstructor.
      - Case "NNRSimpUnop"%string.
        destruct u; try discriminate.
        destruct e; try discriminate.
        + destruct d; try discriminate.
          invcs typ.
          invcs H2.
          apply Coll_right_inv in H; subst.
          invcs eqq; trivial.
        + destruct u; try discriminate.
          invcs eqq.
          invcs typ.
          invcs H2.
          apply Coll_right_inv in H; subst.
          trivial.
    Qed.
    
    Lemma nnrs_imp_expr_unflatten_read_type e e' v :
      nnrs_imp_expr_unflatten_read e v = Some e' ->
      forall {Γc Γ τo},
        [ Γc ; Γ  ⊢ e ▷ τo]  ->
        forall τ,
          lookup equiv_dec Γ v = Some (Coll τ) ->
          [ Γc ; (update_first equiv_dec Γ v τ)   ⊢ e' ▷ τo ].
    Proof.
      revert e'.
      nnrs_imp_expr_cases (induction e) Case
      ; simpl ; intros e' eqq Γc Γ τo typ τ inn.
      - Case "NNRSimpGetConstant"%string.
        invcs eqq.
        invcs typ.
        econstructor; trivial.
      - Case "NNRSimpVar"%string.
        match_destr_in eqq.
        invcs eqq; simpl.
        invcs typ.
        econstructor.
        rewrite lookup_update_neq; trivial.
        eauto.
      - Case "NNRSimpConst"%string.
        invcs eqq; simpl; trivial.
        invcs typ.
        econstructor; trivial.
      - Case "NNRSimpBinop"%string.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
        invcs typ.
        econstructor; eauto.
      - Case "NNRSimpUnop"%string.
        invcs typ.
        destruct u
        ; try solve [apply some_lift in eqq
                     ; destruct eqq as [eqq1 eqq2]
                     ; subst; simpl
                     ; econstructor; eauto].
        destruct e
        ; try solve [apply some_lift in eqq
                     ; destruct eqq as [eqq1 eqq2]
                     ; subst; simpl
                     ; econstructor; eauto].
        invcs H2.
        invcs H4.
        match_destr_in eqq.
        + invcs eqq; simpl.
          rewrite e in *.
          unfold var in *.
          rewrite inn in H1; invcs H1; rtype_equalizer.
          apply Coll_right_inv in H0; subst.
          econstructor.
          rewrite lookup_update_eq_in; try congruence.
          apply lookup_in_domain in inn; trivial.
        + invcs eqq; simpl.
          econstructor; econstructor.
          rewrite lookup_update_neq; eauto.
      - Case "NNRSimpGroupBy"%string.
        apply some_lift in eqq.
        destruct eqq as [??]; subst; simpl.
        invcs typ.
        econstructor; trivial.
        eauto.
    Qed.

    Lemma nnrs_imp_expr_unflatten_write_type e e' v :
      nnrs_imp_expr_unflatten_write e v = Some e' ->
      forall {Γc Γ τo},
        [ Γc ; Γ  ⊢ e ▷ Coll (Coll τo)]  ->
        forall τ,
          lookup equiv_dec Γ v = Some (Coll τ) ->
          [ Γc ; (update_first equiv_dec Γ v τ)   ⊢ e' ▷ Coll τo ].
    Proof.
      revert e'.
      nnrs_imp_expr_cases (induction e) Case
      ; simpl ; intros e' eqq Γc Γ τo typ τ inn
      ; try discriminate.
      - Case "NNRSimpVar"%string.
        match_destr_in eqq.
        rewrite e in *; clear v0 e.
        invcs eqq; simpl.
        invcs typ.
        rewrite inn in H1.
        invcs H1.
        apply Coll_right_inv in H0; subst.
        econstructor.
        rewrite lookup_update_eq_in; eauto.
        apply lookup_in_domain in inn; trivial.
      - Case "NNRSimpConst"%string.
        invcs typ.
        destruct d; simpl; try discriminate.
        destruct l; simpl; try discriminate.
        + invcs eqq.
          econstructor.
          repeat econstructor.
        + destruct d; simpl; try discriminate.
          destruct l; simpl; try discriminate.
          invcs eqq.
          econstructor.
          simpl in H1.
          invcs H1.
          apply Coll_right_inv in H0; subst.
          invcs H2; trivial.
      - Case "NNRSimpBinop"%string.
        destruct b; try discriminate.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
        invcs typ.
        invcs H3.
        apply Coll_right_inv in H; subst.
        econstructor; eauto.
        econstructor.
      - Case "NNRSimpUnop"%string.
        invcs typ.
        destruct u; try discriminate.
        match_destr_in eqq.
        invcs eqq.
        invcs H2.
        apply Coll_right_inv in H; subst.
        apply (nnrs_imp_expr_type_update_first_irrelevant Γc nil)
        ; simpl; tauto.
    Qed.

    Lemma nnrs_imp_stmt_unflatten_type s s' v :
      nnrs_imp_stmt_unflatten s v = Some s' ->
      forall {Γc Γ},
        [ Γc ; Γ  ⊢ s]  ->
        forall τ,
          lookup equiv_dec Γ v = Some (Coll (Coll τ)) ->
          [ Γc ; (update_first equiv_dec Γ v (Coll τ))   ⊢ s'].
    Proof.
      revert s'
      ; nnrs_imp_stmt_cases (induction s) Case
      ; simpl in *; intros s' eqq Γc Γ typ τ inn.
      - Case "NNRSimpSkip"%string.
        invcs eqq.
        econstructor.
      - Case "NNRSimpSeq"%string.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
        invcs typ.
        econstructor; eauto.
      - Case "NNRSimpAssign"%string.
        apply some_lift in eqq.
        destruct eqq as [??]; subst; simpl.
        invcs typ.
        match_destr_in e; unfold equiv, complement in *.
        + subst.
          unfold equiv_dec, string_eqdec in *.
          rewrite inn in H3.
          invcs H3.
          econstructor.
          * eapply nnrs_imp_expr_unflatten_write_type in e; eauto.
          * rewrite lookup_update_eq_in; eauto.
            apply lookup_in_domain in inn; trivial.
        + econstructor.
          * eapply nnrs_imp_expr_unflatten_read_type in e; eauto.
          * rewrite lookup_update_neq; eauto.
      - Case "NNRSimpLet"%string.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
        invcs typ; simpl in *.
        + apply some_lift in eqq1.
          destruct eqq1 as [? eqq1 ?]; subst; simpl.
          econstructor.
          * eapply nnrs_imp_expr_unflatten_read_type in eqq1; eauto.
          * { match_destr_in eqq2; unfold equiv, complement in *.
              - invcs eqq2.
                apply (nnrs_imp_stmt_type_update_first_irrelevant Γc ((v, τ0) :: nil))
                ; simpl; tauto.
              - specialize (IHs _ eqq2 _ _ H4).
                simpl in IHs.
                unfold var in *.
                destruct (equiv_dec v v0); [congruence | ].
                eauto.
            }
        + invcs eqq1.
          match_destr_in eqq2; unfold equiv, complement in *.
          * invcs eqq2.
            econstructor; trivial.
            apply (nnrs_imp_stmt_type_update_first_irrelevant Γc ((v, τ0) :: nil))
            ; simpl; tauto.
          * { econstructor.
              - rewrite <- (nnrs_imp_stmt_unflatten_var_usage eqq2); trivial.
              - specialize (IHs _ eqq2 _ _ H4).
                simpl in IHs.
                unfold var in *.
                destruct (equiv_dec v v0); [congruence | ].
                eauto.
            }
      - Case "NNRSimpFor"%string.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
        invcs typ.
        eapply nnrs_imp_expr_unflatten_read_type in eqq1; eauto.
        econstructor; trivial; eauto.
        match_destr_in eqq2; unfold equiv, complement in *.
        + invcs eqq2.
          apply (nnrs_imp_stmt_type_update_first_irrelevant Γc ((v, τ0) :: nil))
          ; simpl; tauto.
        +  specialize (IHs _ eqq2 _ _ H4).
           simpl in IHs.
           unfold var in *.
           destruct (equiv_dec v v0); [congruence | ].
           eauto.
      - Case "NNRSimpIf"%string.
        unfold lift3 in eqq.
        repeat match_option_in eqq.
        invcs eqq; simpl.
        invcs typ.
        eapply nnrs_imp_expr_unflatten_read_type in eqq0; eauto.
        econstructor; eauto.
      - Case "NNRSimpEither"%string.
        unfold lift3 in eqq.
        repeat match_option_in eqq.
        invcs eqq; simpl.
        invcs typ.
        eapply nnrs_imp_expr_unflatten_read_type in eqq0; eauto.
        econstructor; eauto.
        + match_destr_in eqq1; unfold equiv, complement in *.
          * invcs eqq1.
            apply (nnrs_imp_stmt_type_update_first_irrelevant Γc ((v, τl) :: nil))
            ; simpl; tauto.
          * specialize (IHs1 _ eqq1 _ _ H6).
            simpl in IHs1.
            unfold var in *.
            destruct (equiv_dec v v0); [congruence | ].
            eauto.
        + match_destr_in eqq2; unfold equiv, complement in *.
          * invcs eqq2.
            apply (nnrs_imp_stmt_type_update_first_irrelevant Γc ((v, τr) :: nil))
            ; simpl; tauto.
          * specialize (IHs2 _ eqq2 _ _ H7).
            simpl in IHs2.
            unfold var in *.
            destruct (equiv_dec v v1); [congruence | ].
            eauto.
    Qed.

  End typ.

  Section type_enrich.

    Lemma nnrs_imp_expr_unflatten_read_enrich_type {e e' v} :
      nnrs_imp_expr_unflatten_read e v = Some e' ->
      forall {Γc Γ τo},
        [ Γc ; Γ  ⊢ e ▷ τo]  ->
        forall τ,
          In v (nnrs_imp_expr_free_vars e) ->
          lookup equiv_dec Γ v = Some τ ->
          exists τ', τ = Coll (Coll τ').
    Proof.
      revert e'.
      nnrs_imp_expr_cases (induction e) Case
      ; simpl ; intros e' eqq Γc Γ τo typ τ inn1 inn2
      ; try contradiction.
      - Case "NNRSimpVar"%string.
        match_destr_in eqq.
        intuition.
      - Case "NNRSimpBinop"%string.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1[eqq2 ?]]]; subst.
        invcs typ.
        rewrite in_app_iff in inn1.
        destruct inn1 as [inn1|inn1]; eauto.
      - Case "NNRSimpUnop"%string.
        invcs typ.
        destruct u
        ; try solve [apply some_lift in eqq
                     ; destruct eqq as [eqq1 eqq2]
                     ; subst; simpl
                     ; invcs H2; eauto].
        invcs H2.
        destruct e
        ; try solve [apply some_lift in eqq
                     ; destruct eqq as [eqq1 eqq2]
                     ; subst; simpl; eauto].
        simpl in inn1.
        match_destr_in eqq; [ | intuition congruence].
        invcs eqq.
        invcs H4.
        intuition; subst.
        rewrite H1 in inn2.
        invcs inn2.
        eauto.
      - Case "NNRSimpGroupBy"%string.
        apply some_lift in eqq.
        destruct eqq as [? eqq ?].
        subst; simpl.
        invcs typ.
        eauto.
    Qed.

    Lemma nnrs_imp_stmt_unflatten_read_out_type s s' v :
      nnrs_imp_stmt_unflatten s v = Some s' ->
      nnrs_imp_stmt_read_out s v = true ->
      forall {Γc Γ},
        [ Γc ; Γ  ⊢ s]  ->
        forall τ,
          lookup equiv_dec Γ v = Some τ ->
          exists τ', τ = Coll (Coll τ').
    Proof.
      revert s'
      ; nnrs_imp_stmt_cases (induction s) Case
      ; simpl in *; intros s' eqq_un eqq_ro Γc Γ typ τ inn
      ; unfold nequiv_decb, equiv_decb in *.
      - Case "NNRSimpSkip"%string.
        discriminate.
      - Case "NNRSimpSeq"%string.
        apply orb_true_elim in eqq_ro.
        invcs typ.
        apply some_lift2 in eqq_un.
        destruct eqq_un as [?[? eqq1[eqq2 ?]]]; subst.
        intuition eauto.
      - Case "NNRSimpAssign"%string.
        invcs typ.
        apply some_lift in eqq_un.
        destruct eqq_un as [? eqq ?].
        subst; simpl.
        match_destr_in eqq_ro.
        simpl in *.
        eapply nnrs_imp_expr_unflatten_read_enrich_type; eauto.
        apply nnrs_imp_expr_may_use_free_vars; auto.
      - Case "NNRSimpLet"%string.
        apply orb_true_elim in eqq_ro.
        apply some_lift2 in eqq_un.
        destruct eqq_un as [?[? eqq1[eqq2 ?]]]; subst.
        destruct eqq_ro.
        + destruct o; try discriminate.
          invcs typ.
          simpl in eqq1.
          apply some_lift in eqq1.
          destruct eqq1 as [? eqq ?]; subst.
          eapply nnrs_imp_expr_unflatten_read_enrich_type; eauto.
          apply nnrs_imp_expr_may_use_free_vars; auto.
        + match_destr_in e; simpl in e.
          invcs typ; eapply IHs; eauto
          ; simpl
          ; match_destr
          ; congruence.
      - Case "NNRSimpFor"%string.
        apply orb_true_elim in eqq_ro.
        apply some_lift2 in eqq_un.
        destruct eqq_un as [?[? eqq1[eqq2 ?]]]; subst.
        invcs typ.
        destruct eqq_ro.
        + eapply nnrs_imp_expr_unflatten_read_enrich_type; eauto.
          apply nnrs_imp_expr_may_use_free_vars; auto.
        + match_destr_in eqq2.
          simpl in e.
          eapply IHs; eauto.
          simpl; match_destr; congruence.
      - unfold lift3 in eqq_un; repeat match_option_in eqq_un.
        invcs eqq_un; subst.
        invcs typ.
        apply orb_true_elim in eqq_ro.
        destruct eqq_ro as [eqq_ro | eqq_ro].
        + apply orb_true_elim in eqq_ro.
          destruct eqq_ro as [eqq_ro | eqq_ro].
          * eapply nnrs_imp_expr_unflatten_read_enrich_type; eauto.
            apply nnrs_imp_expr_may_use_free_vars; auto.
          * eauto.
        + eauto.
      - unfold lift3 in eqq_un; repeat match_option_in eqq_un.
        invcs eqq_un; subst.
        invcs typ.
        apply orb_true_elim in eqq_ro.
        destruct eqq_ro as [eqq_ro | eqq_ro].
        + apply orb_true_elim in eqq_ro.
          destruct eqq_ro as [eqq_ro | eqq_ro].
          * eapply nnrs_imp_expr_unflatten_read_enrich_type; eauto.
            apply nnrs_imp_expr_may_use_free_vars; auto.
          * match_destr_in eqq_ro.
            eapply IHs1; eauto.
            simpl; match_destr; congruence.
        + match_destr_in eqq_ro.
          eapply IHs2; eauto.
          simpl; match_destr; congruence.
    Qed.

  End type_enrich.

  Section unflatten_safe.

    Lemma nnrs_imp_stmt_unflatten_safe_eval s s' v σc σ d :
      nnrs_imp_stmt_unflatten_safe s v = Some s' ->
      forall Γc,
        bindings_type σc Γc ->
        forall Γ,
          pd_bindings_type σ Γ ->
          forall τ,
            lookup equiv_dec σ v = Some d ->
            lookup equiv_dec Γ v = Some τ ->
            [ Γc ; Γ  ⊢ s ] ->
            forall d',
              lift2P flattens_to d d' ->
              lift2P
                (fun σ₁' σ₂' =>
                   match lookup equiv_dec σ₁' v with
                   | Some dd => 
                     exists dd',
                     σ₂' = update_first equiv_dec σ₁' v dd'
                     /\ lift2P flattens_to dd dd'
                   | None => False
                   end
                )
                (nnrs_imp_stmt_eval brand_relation_brands σc s σ)
                (nnrs_imp_stmt_eval brand_relation_brands σc s' (update_first equiv_dec σ v d')).
    Proof.
      unfold nnrs_imp_stmt_unflatten_safe.
      intros eqq1 Γc Γc_bt Γ Γ_bt τ inn1 inn2 typ; intros.
      match_case_in eqq1; intros eqq2; rewrite eqq2 in eqq1; try discriminate.
      intros.
      destruct (nnrs_imp_stmt_unflatten_read_out_type _ _ _ eqq1 eqq2 typ _ inn2)
      ; subst.
      eapply nnrs_imp_stmt_unflatten_eval; eauto.
    Qed.
    
    Lemma nnrs_imp_stmt_unflatten_safe_type s s' v :
      nnrs_imp_stmt_unflatten_safe s v = Some s' ->
      forall {Γc Γ},
        [ Γc ; Γ  ⊢ s]  ->
        forall τ,
          lookup equiv_dec Γ v = Some τ ->
          exists τ',
            [ Γc ; (update_first equiv_dec Γ v (Coll τ'))   ⊢ s']
            /\  τ = Coll (Coll τ').
    Proof.
      unfold nnrs_imp_stmt_unflatten_safe.
      intros eqq1 Γc Γ typ τ inn.
      match_case_in eqq1; intros eqq2; rewrite eqq2 in eqq1; try discriminate.
      destruct (nnrs_imp_stmt_unflatten_read_out_type _ _ _ eqq1 eqq2 typ _ inn)
      ; subst.
      econstructor; split; try reflexivity.
      eapply nnrs_imp_stmt_unflatten_type; eauto.
    Qed.

    Lemma nnrs_imp_stmt_unflatten_safe_var_usage {s s' v}:
      nnrs_imp_stmt_unflatten_safe s v = Some s' ->
      forall v',
        nnrs_imp_stmt_var_usage s v' = nnrs_imp_stmt_var_usage s' v'.
    Proof.
      unfold nnrs_imp_stmt_unflatten_safe.
      intros eqq1; intros.
      match_case_in eqq1; intros eqq2; rewrite eqq2 in eqq1; try discriminate.
      eapply nnrs_imp_stmt_unflatten_var_usage; eauto.
    Qed.

    Lemma nnrs_imp_stmt_unflatten_safe_var_usage_sub {s x s'} :
      nnrs_imp_stmt_unflatten_safe s x = Some s' ->
      stmt_var_usage_sub s s'.
    Proof.
      intros eqq1 v.
      eapply nnrs_imp_stmt_unflatten_safe_var_usage in eqq1.
      rewrite eqq1.
      reflexivity.
    Qed.

  End unflatten_safe.
  
End TNNRSimpUnflatten.
