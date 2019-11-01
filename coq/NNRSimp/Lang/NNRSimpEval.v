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

(** NNRSimp is a variant of the named nested relational calculus
     (NNRC) that is meant to be more imperative in feel.  It is used
     as an intermediate language between NNRC and more imperative /
     statement oriented backends *)

Require Import String.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Arith.
Require Import Max.
Require Import Bool.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRSimp.
Require Import NNRSimpVars.

Section NNRSimpEval.
  Import ListNotations.

  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  Local Open Scope nnrs_imp.
  Local Open Scope string.

  (** ** Evaluation Semantics *)
  Section Evaluation.

    (** Evaluation takes a NNRSimp expression and an environment. It
          returns an optional value. When [None] is returned, it
          denotes an error. An error is always propagated. *)

    Fixpoint nnrs_imp_expr_eval
             (σc:bindings) (σ:pd_bindings) (e:nnrs_imp_expr)
    : option data
      := match e with
         | NNRSimpGetConstant v =>
           edot σc v

         | NNRSimpVar v =>
           olift id (lookup equiv_dec σ v)

         | NNRSimpConst d =>
           Some (normalize_data h d)

         | NNRSimpBinop bop e₁ e₂ =>
           olift2 (fun d₁ d₂ => binary_op_eval h bop d₁ d₂)
                  (nnrs_imp_expr_eval σc σ e₁)
                  (nnrs_imp_expr_eval σc σ e₂)

         | NNRSimpUnop uop e =>
           olift (fun d => unary_op_eval h uop d)
                 (nnrs_imp_expr_eval σc σ e)

         | NNRSimpGroupBy g sl e =>
           match nnrs_imp_expr_eval σc σ e with
           | Some (dcoll dl) => lift dcoll (group_by_nested_eval_table g sl dl)
           | _ => None
           end
         end.

    Fixpoint nnrs_imp_stmt_eval
             (σc:bindings) (s:nnrs_imp_stmt) 
             (σ:pd_bindings) : option (pd_bindings)
      := match s with
         | NNRSimpSkip => Some σ
         | NNRSimpSeq s₁ s₂ =>
           olift (nnrs_imp_stmt_eval σc s₂)
                 (nnrs_imp_stmt_eval σc s₁ σ)
                 
         | NNRSimpAssign v e =>
           match nnrs_imp_expr_eval σc σ e, lookup string_dec σ v with
           | Some d, Some _ => Some (update_first string_dec σ v (Some d))
           | _, _ => None
           end
             
         | NNRSimpLet v eo s₀ =>
           let evals := (fun init =>
                           match nnrs_imp_stmt_eval σc s₀ ((v,init)::σ) with
                           | Some (_::σ') => Some σ'
                           | _ => None
                           end) in
           match eo with
           | Some e => olift evals (lift Some (nnrs_imp_expr_eval σc σ e))
           | None => evals None
           end
             
         | NNRSimpFor v e s₀ =>
           match nnrs_imp_expr_eval σc σ e with
           | Some (dcoll c1) =>
             let fix for_fun (dl:list data) σ₁ :=
                 match dl with
                 | nil => Some σ₁
                 | d::dl' =>
                   match nnrs_imp_stmt_eval σc s₀ ((v,Some d)::σ₁) with
                   | Some (_::σ₂) => for_fun dl' σ₂ 
                   | _ => None
                   end
                 end in
             for_fun c1 σ 
           | _ => None
           end

         | NNRSimpIf e s₁ s₂ =>
           match nnrs_imp_expr_eval σc σ e  with
           | Some (dbool true) => nnrs_imp_stmt_eval σc s₁ σ
           | Some (dbool false) => nnrs_imp_stmt_eval σc s₂ σ
           | _ => None
           end

         | NNRSimpEither e x₁ s₁ x₂ s₂ =>
           match nnrs_imp_expr_eval σc σ e with
           | Some (dleft d) =>
             match nnrs_imp_stmt_eval σc s₁ ((x₁,Some d)::σ) with
             | Some (_::σ₂) => Some σ₂
             | _ => None
             end
           | Some (dright d) =>
             match nnrs_imp_stmt_eval σc s₂ ((x₂,Some d)::σ) with
             | Some (_::σ₂) => Some σ₂
             | _ => None
             end
           | _ => None
           end
         end.

    Definition nnrs_imp_eval σc (q:nnrs_imp) : option (option data) :=
      let (s, ret) := q in
      match nnrs_imp_stmt_eval σc s ((ret, None)::nil) with
      | Some ((_,o)::_) => Some o
      | _ => None
      end.

    Definition nnrs_imp_eval_top σc (q:nnrs_imp) :=
      olift id (nnrs_imp_eval (rec_sort σc) q).

  End Evaluation.

  Section Core.
    Program Definition nnrs_imp_core_eval σc (q:nnrs_imp_core)
      := nnrs_imp_eval σc q.

    Program Definition nnrs_imp_core_eval_top σc (q:nnrs_imp_core)
      :=  olift id (nnrs_imp_core_eval (rec_sort σc) q).
    
  End Core.

  Section props.

    Ltac destr H :=
      let eqq := fresh "eqq" in
      first [
          match goal with
            [H:  _ * _ |- _ ] => destruct H
          end |
          (match_case_in H;
           [intros [???] eqq | intros eqq]; rewrite eqq in H; try discriminate)
          | (match_case_in H;
             [intros [??] eqq | intros eqq]; rewrite eqq in H; try discriminate)
          | (match_case_in H;
             [intros ?? eqq | intros eqq]; rewrite eqq in H; try discriminate)
          | (match_case_in H;
             [intros ? eqq | intros eqq]; rewrite eqq in H; try discriminate)
          | (match_case_in H;
             [intros eqq | intros ? ? eqq]; try rewrite eqq in H; try discriminate)
          | (match_case_in H;
             [intros eqq | intros ? eqq]; try rewrite eqq in H; try discriminate)
        ]; subst.

    Instance preserves_some_pre {A} :
      PreOrder (fun x y: option A => x <> None -> y <> None).
    Proof.
      constructor; red; intuition.
    Qed.
    
    Lemma nnrs_imp_stmt_eval_preserves_some {s σc σ₁ σ₂} :
      nnrs_imp_stmt_eval σc s σ₁ = Some σ₂ ->
      Forall2 (fun x y => x <> None -> y <> None) (codomain σ₁) (codomain σ₂).
    Proof.
      revert σ₁ σ₂.
      nnrs_imp_stmt_cases (induction s) Case; intros σ₁ σ₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRSimpSkip".
        invcs sem; trivial.
        reflexivity.
      - Case "NNRSimpSeq".
        apply some_olift in sem.
        destruct sem as [σ' ? ?].
        transitivity (codomain σ'); eauto.
      - Case "NNRSimpAssign".
        invcs sem.
        clear.
        induction σ₁; simpl; trivial.
        destruct a; simpl.
        match_destr; constructor; simpl; eauto; try congruence.
        reflexivity.
      - Case "NNRSimpLet".
        apply some_olift in sem.
        destruct sem as [d eqq1 eqq2 ].
        match_option_in eqq2.
        destruct p; try discriminate.
        invcs eqq2.
        specialize (IHs _ _ eqq).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRSimpLet".
        invcs sem.
        specialize (IHs _ _ eqq).
        simpl in IHs; invcs IHs; trivial.
      - Case  "NNRSimpFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ σ₂ sem.
        induction l; intros σ₁ σ₂  sem; invcs sem; try reflexivity.
        repeat destr H0.
        specialize (IHl _ _ H0).
        specialize (IHs _ _ eqq).
        simpl in IHs; invcs IHs.
        etransitivity; eauto.
      - Case "NNRSimpIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRSimpEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.
    
    Lemma nnrs_imp_stmt_eval_domain_stack {s σc σ₁ σ₂} :
      nnrs_imp_stmt_eval σc s σ₁ = Some σ₂ -> domain σ₁ = domain σ₂.
    Proof.
      revert σ₁ σ₂.
      nnrs_imp_stmt_cases (induction s) Case; intros σ₁ σ₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRSimpSkip".
        invcs sem; trivial.
      - Case "NNRSimpSeq".
        apply some_olift in sem.
        destruct sem as [σ' ? ?].
        transitivity (domain σ'); eauto.
      - Case "NNRSimpAssign".
        invcs sem.
        rewrite domain_update_first; trivial.
      - Case "NNRSimpLet".
        apply some_olift in sem.
        destruct sem as [d eqq1 eqq2 ].
        match_option_in eqq2.
        destruct p; try discriminate.
        invcs eqq2.
        specialize (IHs _ _ eqq).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRSimpLet".
        invcs sem.
        specialize (IHs _ _ eqq).
        simpl in IHs; invcs IHs; trivial.
      - Case  "NNRSimpFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ σ₂ sem.
        induction l; intros σ₁ σ₂  sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ H0).
        specialize (IHs _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRSimpIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRSimpEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrs_imp_stmt_eval_lookup_some_some {σc s σ σ' }:
      nnrs_imp_stmt_eval σc s σ = Some σ' ->
      forall x d,
        lookup equiv_dec σ x = Some (Some d) ->
        exists o : data, lookup equiv_dec σ' x = Some (Some o).
    Proof.
      intros eqq.
      generalize (nnrs_imp_stmt_eval_domain_stack eqq)
      ; generalize (nnrs_imp_stmt_eval_preserves_some eqq).
      clear s eqq.
      revert σ'; induction σ; intros σ' f2 deq
      ; destruct σ'; simpl; intros; try discriminate.

      destruct a.
      destruct p.
      simpl in *.
      invcs deq.
      invcs f2.
      match_destr; eauto.
      invcs H.
      destruct o0; eauto; intuition congruence.
    Qed.

    Local Open Scope list.


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

                      | [H : nnrs_imp_stmt_eval _ _ _ ?p1 = ?p2 |- _ ] =>
                        apply nnrs_imp_stmt_eval_domain_stack in H

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

    Lemma nnrs_imp_stmt_eval_lookup_preserves_unwritten {σc s}  l l' σ σ' :
      nnrs_imp_stmt_eval σc s (l++σ) = Some (l'++σ') ->
      domain l = domain l' ->
      forall x,
        In x (domain l) \/ ~ In x (nnrs_imp_stmt_maybewritten_vars s) ->
        lookup equiv_dec σ x = lookup equiv_dec σ' x.
    Proof.
      revert  l l' σ σ'
      ; nnrs_imp_stmt_cases (induction s) Case
      ; simpl
      ; intros l l' σ σ' eqq domeq x inn
      ; repeat rewrite in_app_iff in *
      ; try rewrite IHs
      ; try rewrite IHs1
      ; try rewrite IHs2.
      - Case "NNRSimpSkip"%string.
        invcs eqq; trivial.
        fuse_tt.
      - Case "NNRSimpSeq"%string.
        apply some_olift in eqq.
        destruct eqq as [? eqq1 eqq2].
        generalize (nnrs_imp_stmt_eval_domain_stack eqq1)
        ; intros eqq3.
        rewrite domain_app in eqq3
        ; unfold domain in eqq3
        ; symmetry in eqq3; apply map_app_break in eqq3
        ; destruct eqq3 as [? [?[?[??]]]]; subst; simpl in *.
        rewrite (IHs1 _ _ _ _ eqq1) by tauto.
        rewrite (IHs2 _ _ _ _ (symmetry eqq2)); trivial
        ; unfold domain in *.
        + congruence.
        + destruct inn as [inn|inn].
          * left; congruence.
          * right; tauto.
      - Case "NNRSimpAssign"%string.
        match_destr_in eqq.
        match_destr_in eqq.
        invcs eqq.
        destruct (in_dec string_dec v (domain l)).
        + rewrite update_app_in in H0 by trivial.
          apply app_inv_head_domain in H0.
          * intuition congruence.
          * rewrite domain_update_first; eauto.
        + rewrite update_app_nin in H0 by trivial.
          apply app_inv_head_domain in H0; [| eauto 2].
          destruct H0; subst.
          rewrite lookup_update_neq; trivial.
          destruct inn; try tauto.
          intros; subst; congruence.
      - Case "NNRSimpLet"%string.
        destruct o.
        + apply some_olift in eqq.
          destruct eqq as [???].
          apply some_lift in e.
          destruct e as [? eqq1 ?]; subst.
          match_option_in e0.
          match_destr_in e0.
          invcs e0.
          generalize (nnrs_imp_stmt_eval_domain_stack eqq)
          ; destruct p; simpl; intros eqq2.
          invcs eqq2.
          apply (IHs ((s0, Some x1) :: l) ((s0,o)::l') σ σ' eqq)
          ; simpl; try congruence.
          destruct inn as [inn|inn].
          * eauto.
          * apply remove_nin_inv in inn.
            intuition.
        + apply some_olift in eqq.
          destruct eqq as [???].
          match_destr_in e0.
          invcs e0.
          generalize (nnrs_imp_stmt_eval_domain_stack e)
          ; destruct p; simpl; intros eqq2.
          invcs eqq2.
          apply (IHs ((s0, None) :: l) ((s0,o)::l') σ σ' e)
          ; simpl; try congruence.
          destruct inn as [inn|inn].
          * eauto.
          * apply remove_nin_inv in inn.
            intuition.
      - Case "NNRSimpFor"%string.        
        apply some_olift in eqq.
        destruct eqq as [???].
        match_destr_in e0.
        clear e.
        revert l l' σ σ' domeq inn e0.
        induction l0; simpl; intros  l l' σ σ' domeq inn eqq.
        + invcs eqq.
          fuse_tt.
        + match_option_in eqq.
          destruct p; simpl; try discriminate.
          generalize (nnrs_imp_stmt_eval_domain_stack eqq0)
          ; destruct p; simpl; intros eqq2.
          invcs eqq2.
          rewrite domain_app in H1
          ; unfold domain in H1
          ; symmetry in H1; apply map_app_break in H1
          ; destruct H1 as [? [?[?[??]]]]; subst; simpl in *.
          specialize (IHs  ((s0, Some a) :: l) ((s0, o) :: x0) _ _ eqq0).
          cut_to IHs; simpl; [| unfold domain in *; try congruence].
          specialize (IHs x).
          rewrite IHs.
          * {
              eapply IHl0; try eapply eqq; unfold domain in *.
              - congruence.
              - destruct inn as [inn|inn]; [ | eauto ].
                left; congruence.
            }
          * simpl. destruct inn as [inn|inn]; [eauto | ].
            apply remove_nin_inv in inn; intuition congruence.
      - Case "NNRSimpIf"%string.
        match_option_in eqq.
        destruct d; simpl; try discriminate.
        destruct b.
        + eapply IHs1; try eapply eqq; tauto.
        + eapply IHs2; try eapply eqq; tauto.
      - Case "NNRSimpEither"%string.
        match_option_in eqq.
        destruct d; simpl; try discriminate
        ; match_option_in eqq
        ; destruct p; try discriminate
        ; invcs eqq.
        + generalize (nnrs_imp_stmt_eval_domain_stack eqq1)
          ; destruct p; simpl; intros eqq2.
          invcs eqq2.
          apply (IHs1 ((s, Some d) :: l) ((s,o)::l') _ _ eqq1)
          ; simpl; try congruence.
          destruct inn as [inn|inn]; [eauto | ].
          apply not_or in inn.
          destruct inn as [inn1 inn2].
          apply remove_nin_inv in inn1.
          intuition congruence.
        + generalize (nnrs_imp_stmt_eval_domain_stack eqq1)
          ; destruct p; simpl; intros eqq2.
          invcs eqq2.
          apply (IHs2 ((s, Some d) :: l) ((s,o)::l') _ _ eqq1)
          ; simpl; try congruence.
          destruct inn as [inn|inn]; [eauto | ].
          apply not_or in inn.
          destruct inn as [inn1 inn2].
          apply remove_nin_inv in inn2.
          intuition congruence.
    Qed.

    Lemma nnrs_imp_expr_eval_same σc pd₁ pd₂ s :
      lookup_equiv_on (nnrs_imp_expr_free_vars s) pd₁ pd₂ ->
      nnrs_imp_expr_eval σc pd₁ s = nnrs_imp_expr_eval σc pd₂ s.
    Proof.
      revert pd₁ pd₂.
      induction s; simpl; intros; eauto 3.
      - rewrite H; simpl; tauto.
      - apply lookup_equiv_on_dom_app in H; destruct H as [leo1 leo2].
        rewrite (IHs1 _ _ leo1).
        rewrite (IHs2 _ _ leo2).
        trivial.
      - rewrite (IHs _ _ H); trivial.
      - rewrite (IHs _ _ H); trivial.
    Qed.

    Lemma nnrs_imp_expr_eval_group_by_unfold σc σ g sl e :
      nnrs_imp_expr_eval σc σ (NNRSimpGroupBy g sl e) = 
      match nnrs_imp_expr_eval σc σ e with
      | Some (dcoll dl) => lift dcoll (group_by_nested_eval_table g sl dl)
      | _ => None
      end.
    Proof.
      reflexivity.
    Qed.

    Global Instance nnrs_imp_expr_eval_proper 
      : Proper (eq ==> lookup_equiv ==> eq ==> eq) nnrs_imp_expr_eval.
    Proof.
      intros ?????????; subst.
      apply nnrs_imp_expr_eval_same.
      apply lookup_equiv_on_lookup_equiv; trivial.
    Qed.

  End props.

  Section eval_eqs.

    Local Close Scope string.

    Lemma nnrs_imp_expr_eval_free σc (l1 l2 l3:pd_bindings) e :
      disjoint (nnrs_imp_expr_free_vars e) (domain l2) ->
      nnrs_imp_expr_eval σc (l1 ++ l2 ++ l3) e
      =
      nnrs_imp_expr_eval σc (l1 ++ l3) e.
    Proof.
      induction e; simpl; eauto; intros.
      - repeat rewrite lookup_app.
        repeat match_option.
        specialize (H v); simpl in H.
        apply lookup_in_domain in eqq0.
        intuition.
      - apply disjoint_app_l in H.
        rewrite IHe1, IHe2; tauto.
      - rewrite IHe; tauto.
      - rewrite IHe; tauto.
    Qed.

    Lemma nnrs_imp_expr_eval_free_tail σc (l1 l2:pd_bindings) e :
      disjoint (nnrs_imp_expr_free_vars e) (domain l2) ->
      nnrs_imp_expr_eval σc (l1 ++ l2) e
      =
      nnrs_imp_expr_eval σc l1 e.
    Proof.
      intros.
      generalize (nnrs_imp_expr_eval_free σc l1 l2 nil).
      repeat rewrite app_nil_r; auto.
    Qed.
    
    Lemma nnrs_imp_expr_eval_unused c l σ e v d :
      (In v (domain l) 
       \/ ~ In v (nnrs_imp_expr_free_vars e)) ->
      nnrs_imp_expr_eval c (l ++ (v, d) :: σ) e
      = nnrs_imp_expr_eval c (l ++ σ) e.
    Proof.
      intros inn.
      apply nnrs_imp_expr_eval_same.
      unfold lookup_equiv_on; simpl; intros.
      repeat rewrite lookup_app.
      match_case; intros.
      simpl.
      match_destr; unfold equiv in *.
      subst.
      apply lookup_none_nin in H0.
      tauto.
    Qed.

    Section swap.
      
      Lemma nnrs_imp_expr_eval_swap c l σ e v₁ v₂ d₁ d₂:
        v₁ <> v₂ ->
        nnrs_imp_expr_eval c (l++(v₁,d₁)::(v₂,d₂)::σ) e =
        nnrs_imp_expr_eval c (l++(v₂,d₂)::(v₁,d₁)::σ) e.
      Proof.
        intros neq.
        apply nnrs_imp_expr_eval_same.
        unfold lookup_equiv_on; simpl; intros.
        repeat rewrite lookup_app.
        match_destr.
        simpl.
        repeat match_destr.
        congruence.
      Qed.

      Lemma nnrs_imp_stmt_eval_swap c l σ s v₁ v₂ d₁ d₂:
        v₁ <> v₂ ->
        lift2P
          (fun σ₁' σ₂' =>
             (forall l' d₁' d₂' σ'',
                 domain l' = domain l ->
                 σ₁' = l' ++ (v₁,d₁')::(v₂,d₂')::σ'' ->
                 σ₂' = l' ++ (v₂,d₂')::(v₁,d₁')::σ'')
          )
          (nnrs_imp_stmt_eval c s (l++(v₁,d₁)::(v₂,d₂)::σ))
          (nnrs_imp_stmt_eval c s (l++(v₂,d₂)::(v₁,d₁)::σ)).
      Proof.

        Ltac swap_t
          := repeat (repeat match goal with
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
                              assert (HH:domain y = domain x) by (unfold domain in *; intuition congruence)
                              ; apply app_inv_head_domain in H;[clear HH|apply HH]
                                                                 

                            | [ H: forall a b c d, _ -> ?x1 ++ ?dd1 :: ?dd2 :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                              specialize (H x1 (snd dd1) (snd dd2) x2); simpl in H
                              ; match dd1 with
                                | (_,_) => idtac
                                | _ => destruct dd1
                                end
                              ; simpl in *
                              ; cut_to H; [ | eauto 3 | reflexivity]
                            | [ H: forall a b c d, _ -> ?dd0::?x1 ++ ?dd1 :: ?dd2 :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                              specialize (H (dd0::x1) (snd dd1) (snd dd2) x2); simpl in H
                              ; match dd1 with
                                | (_,_) => idtac
                                | _ => destruct dd1
                                end
                              ; simpl in *
                              ; cut_to H; [ | eauto 3 | reflexivity]
                            | [H : nnrs_imp_stmt_eval _ _ ?p1 = ?p2 |- _ ] =>
                              match p1 with
                              | p2 => fail 1
                              | _ =>  apply nnrs_imp_stmt_eval_domain_stack in H
                              end
                            end; intros; simpl in *; trivial; try solve [unfold domain in *; congruence]
                    ).

        Ltac un2p H :=
          unfold lift2P in H; unfold var in *; simpl in H
          ; repeat match_option_in H; try contradiction
          ; swap_t.

        intros neq.
        revert l σ d₁ d₂.
        nnrs_imp_stmt_cases (induction s) Case
        ; simpl; intros l σ d₁ d₂.
        - Case "NNRSimpSkip"%string.
          swap_t.
        - Case "NNRSimpSeq"%string.
          specialize (IHs1 l σ d₁ d₂); un2p IHs1.
          specialize (IHs2 x1 x2 o1 o2); un2p IHs2.
        - Case "NNRSimpAssign"%string.
          rewrite nnrs_imp_expr_eval_swap by trivial.
          match_destr; try reflexivity.
          repeat rewrite lookup_app.
          case_eq (lookup string_dec l v); [intros ? inn | intros nin].
          + apply lookup_in_domain in inn.
            repeat rewrite update_app_in by trivial.
            simpl; intros.
            apply app_inv_head_domain in H0.
            * destruct H0 as [eqq1 eqq2].
              invcs eqq2; trivial.
            * rewrite domain_update_first; trivial.
          + apply lookup_none_nin in nin.
            repeat rewrite update_app_nin by trivial.
            simpl.
            destruct (string_dec v v₁)
            ; destruct (string_dec v v₂)
            ; simpl
            ; intros
            ; subst
            ; try congruence
            ; swap_t.

            match_destr; simpl; trivial.
            swap_t.
        - Case "NNRSimpLet"%string.
          destruct o.
          + rewrite nnrs_imp_expr_eval_swap by trivial.
            destruct (nnrs_imp_expr_eval c (l ++ (v₂, d₂) :: (v₁, d₁) :: σ) n)
            ; simpl; try reflexivity.
            specialize (IHs ((v, Some d)::l) σ d₁ d₂); un2p IHs.
          + specialize (IHs ((v, None)::l) σ d₁ d₂); un2p IHs.
        - Case "NNRSimpFor"%string.
          rewrite nnrs_imp_expr_eval_swap by trivial.
          destruct (nnrs_imp_expr_eval c (l ++ (v₂, d₂) :: (v₁, d₁) :: σ) n)
          ; simpl; try reflexivity.
          destruct d; simpl; try reflexivity.
          revert l σ d₁ d₂.
          induction l0; intros  l σ d₁ d₂; swap_t.
          specialize (IHs ((v, Some a)::l) σ d₁ d₂); un2p IHs.
          specialize (IHl0 x1 x2 o3 o4); un2p IHl0.
          apply IHl0; swap_t.
        - Case "NNRSimpIf"%string.
          rewrite nnrs_imp_expr_eval_swap by trivial.
          destruct (nnrs_imp_expr_eval c (l ++ (v₂, d₂) :: (v₁, d₁) :: σ) n)
          ; simpl; try reflexivity.
          destruct d; simpl; try reflexivity.
          destruct b.
          + specialize (IHs1 l σ d₁ d₂); un2p IHs1.
          + specialize (IHs2 l σ d₁ d₂); un2p IHs2.
        - Case "NNRSimpEither"%string.
          rewrite nnrs_imp_expr_eval_swap by trivial.
          destruct (nnrs_imp_expr_eval c (l ++ (v₂, d₂) :: (v₁, d₁) :: σ) n)
          ; simpl; try reflexivity.
          destruct d; simpl; try reflexivity.
          + specialize (IHs1 ((v, Some d)::l) σ d₁ d₂); un2p IHs1.
          + specialize (IHs2 ((v0, Some d)::l) σ d₁ d₂); un2p IHs2.
      Qed.
      
    End swap.

    Section unused.

      
      Ltac disect_tac H stac
        := 
          unfold var in *
          ; cut_to H; unfold domain in *; [ | solve[stac]..]
          ; unfold lift2P in H
          ; (repeat match_option_in H; try contradiction).

      Ltac unused_eval_t stac
        := repeat progress (
                    intros
                    ; repeat rewrite in_app_iff in *
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
                          assert (HH:domain y = domain x) by (unfold domain in *; intuition congruence)
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

                                        
                        | [H : nnrs_imp_stmt_eval _ _ ?p1 = ?p2 |- _ ] =>
                          match p1 with
                          | p2 => fail 1
                          | _ =>  apply nnrs_imp_stmt_eval_domain_stack in H
                          end                   
                        | [H:forall l σ d,
                              _ -> _ -> _ -> _ -> lift2P _ (nnrs_imp_stmt_eval _ ?s _) _
                                                         
                              |- lift2P _ (olift _ (nnrs_imp_stmt_eval _ ?s (?l ++ (_, ?d) :: ?σ) ))
                                        _ ] =>
                          specialize (H l σ d)
                          ; disect_tac H stac
                        | [H:forall l σ d,
                              _ -> _ -> _ -> _ -> lift2P _ (nnrs_imp_stmt_eval _ ?s _) _
                                                         
                              |- lift2P _ (nnrs_imp_stmt_eval _ ?s (?l ++ (_, ?d) :: ?σ) )
                                        _ ] =>
                          specialize (H l σ d)
                          ; disect_tac H stac
                        | [H:forall l σ d,
                              _ -> _ -> _ -> _ -> lift2P _ (nnrs_imp_stmt_eval _ ?s _) _
                                                         
                              |- lift2P _ (match nnrs_imp_stmt_eval _ ?s (?x::?l ++ (_, ?d) :: ?σ)
                                           with | Some _ => _ | None => _ end)
                                        _ ] =>
                          specialize (H (x::l) σ d); simpl in H
                          ; disect_tac H stac
                        end; simpl in *; trivial; try tauto; try solve [try unfold domain in *; try congruence]).

      Ltac unused_eval_tt := unused_eval_t ltac:(try tauto; try congruence).

      Lemma nnrs_imp_stmt_eval_unused c l σ s v d:
        (In v (domain l) \/
         ~ In v (nnrs_imp_stmt_free_vars s)) ->
        lift2P
          (fun σ₁' σ₂' =>
             (forall l' d' σ'',
                 domain l' = domain l ->
                 σ₁' = l' ++ (v,d')::σ'' ->
                 σ₂' = l' ++ σ''
                 /\ d = d')
          )
          (nnrs_imp_stmt_eval c s (l++(v,d)::σ))
          (nnrs_imp_stmt_eval c s (l++σ)).
      Proof.
        Ltac un2p H :=
          unfold lift2P in H; unfold var in *; simpl in H
          ; repeat match_option_in H; try contradiction
          ; unused_eval_tt.

        Ltac cut2p H
          := cut_to H;
             [un2p H
             | try unfold domain in *; simpl in *; intuition
               ; repeat match goal with
                        | [H: In _ (remove _ _ _) -> False |- _ ] =>
                          apply remove_nin_inv in H
                        end
               ; intuition].
        
        revert l σ d.
        nnrs_imp_stmt_cases (induction s) Case
        ; simpl; intros l σ d inn
        ; repeat rewrite in_app_iff in inn
        ; unused_eval_tt.
        - Case "NNRSimpSeq"%string.
          specialize (IHs1 l σ d); cut2p IHs1.
          subst.
          specialize (IHs2 x1 x2 o); cut2p IHs2.
          unfold domain in *; rewrite <- H0; tauto.
        - Case "NNRSimpAssign"%string.
          rewrite nnrs_imp_expr_eval_unused by tauto.
          match_destr; try reflexivity.
          repeat rewrite lookup_app.
          case_eq (lookup string_dec l v0); [intros ? inn2 | intros nin].
          + apply lookup_in_domain in inn2.
            repeat rewrite update_app_in by trivial.
            simpl; intros.
            apply app_inv_head_domain in H0.
            * destruct H0 as [eqq1 eqq2].
              invcs eqq2; tauto.
            * rewrite domain_update_first; trivial.
          + apply lookup_none_nin in nin.
            repeat rewrite update_app_nin by trivial.
            simpl.
            destruct (string_dec v0 v)
            ; simpl
            ; intros
            ; subst
            ; try tauto.
            match_destr; simpl; trivial.
            unused_eval_tt.
        - Case "NNRSimpLet"%string.
          destruct o.
          + rewrite nnrs_imp_expr_eval_unused by tauto.
            destruct (nnrs_imp_expr_eval c (l ++ σ) n)
            ; simpl; try reflexivity.
            intuition
            ; repeat match goal with
                     | [H: In _ (remove _ _ _) -> False |- _ ] =>
                       apply remove_nin_inv in H
                     end
            ; specialize (IHs ((v0, Some d0)::l) σ d); cut2p IHs.
          + specialize (IHs ((v0, None)::l) σ d); cut2p IHs.
        - Case "NNRSimpFor"%string.
          rewrite nnrs_imp_expr_eval_unused by tauto.
          destruct (nnrs_imp_expr_eval c (l ++ σ) n)
          ; simpl; try reflexivity.
          destruct d0; simpl; try reflexivity.
          revert l σ d inn.
          induction l0; intros  l σ d inn; unused_eval_tt.
          specialize (IHs ((v0, Some a)::l) σ d); cut2p IHs.
          subst.
          specialize (IHl0 x1 x2 o1); cut2p IHl0.
          + subst; unused_eval_tt.
          + intuition congruence.
        - Case "NNRSimpIf"%string.
          rewrite nnrs_imp_expr_eval_unused by tauto.
          destruct (nnrs_imp_expr_eval c (l ++ σ) n)
          ; simpl; try reflexivity.
          destruct d0; simpl; try reflexivity.
          destruct b.
          + specialize (IHs1 l σ d); un2p IHs1.
          + specialize (IHs2 l σ d); un2p IHs2.
        - Case "NNRSimpEither"%string.
          rewrite nnrs_imp_expr_eval_unused by tauto.
          destruct (nnrs_imp_expr_eval c (l ++ σ) n)
          ; simpl; try reflexivity.
          destruct d0; simpl; try reflexivity.
          + specialize (IHs1 ((v0, Some d0)::l) σ d); cut2p IHs1.
          + specialize (IHs2 ((v1, Some d0)::l) σ d); cut2p IHs2.
      Qed.

    End unused.

  End eval_eqs.

End NNRSimpEval.

Arguments nnrs_imp_stmt_eval_domain_stack {fruntime h s σc σ₁ σ₂}.
Arguments nnrs_imp_stmt_eval_preserves_some {fruntime h s σc σ₁ σ₂}.
Arguments nnrs_imp_stmt_eval_lookup_some_some {fruntime h σc s σ σ' }.
Arguments nnrs_imp_stmt_eval_lookup_preserves_unwritten {fruntime h σc s}.
