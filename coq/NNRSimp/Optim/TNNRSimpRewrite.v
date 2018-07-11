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
    - eauto.
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
      + { intros.
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
          cut_to H15; try congruence.
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

End TNNRSimpRewrite.
