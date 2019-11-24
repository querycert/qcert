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

(** NNRS is a variant of the named nested relational calculus
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
Require Import NNRS.
Require Import NNRSVars.

Section NNRSEval.
  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  Local Open Scope nnrs.
  Local Open Scope string.

  (** ** Evaluation Semantics *)
  Section Evaluation.

    (** Evaluation takes a NNRS expression and an environment. It
          returns an optional value. When [None] is returned, it
          denotes an error. An error is always propagated. *)

    Fixpoint nnrs_expr_eval
             (σc:bindings) (σ:pd_bindings) (e:nnrs_expr)
    : option data
      := match e with
         | NNRSGetConstant v =>
           edot σc v

         | NNRSVar v =>
           olift id (lookup equiv_dec σ v)

         | NNRSConst d =>
           Some (normalize_data h d)

         | NNRSBinop bop e₁ e₂ =>
           olift2 (fun d₁ d₂ => binary_op_eval h bop d₁ d₂)
                  (nnrs_expr_eval σc σ e₁)
                  (nnrs_expr_eval σc σ e₂)

         | NNRSUnop uop e =>
           olift (fun d => unary_op_eval h uop d)
                 (nnrs_expr_eval σc σ e)

         | NNRSGroupBy g sl e =>
           match nnrs_expr_eval σc σ e with
           | Some (dcoll dl) => lift dcoll (group_by_nested_eval_table g sl dl)
           | _ => None
           end
         end.

    Fixpoint nnrs_stmt_eval
             (σc:bindings) (σ:pd_bindings) (ψc:mc_bindings) (ψd:md_bindings)
             (s:nnrs_stmt) : option (pd_bindings*mc_bindings*md_bindings)
      := match s with
         | NNRSSeq s₁ s₂ =>
           match nnrs_stmt_eval σc σ ψc ψd s₁ with
           | Some (σ₁, ψc₁, ψd₁) => nnrs_stmt_eval σc σ₁ ψc₁ ψd₁ s₂
           | None => None
           end

         | NNRSLet v e s₀ =>
           match nnrs_expr_eval σc σ e with
           | Some d =>
             match nnrs_stmt_eval σc ((v,Some d)::σ) ψc ψd s₀ with
             | Some (_::σ₁, ψc₁, ψd₁) => Some (σ₁, ψc₁,ψd₁)
             | _ => None
             end
           | None => None
           end

         | NNRSLetMut v s₁ s₂ =>
           match nnrs_stmt_eval σc σ ψc ((v,None)::ψd) s₁ with
           | Some (σ₁, ψc₁, (_,d)::ψd₁) =>
             match nnrs_stmt_eval σc ((v,d)::σ₁) ψc₁ ψd₁ s₂ with
             | Some (_::σ₂, ψc₂, ψd₂) => Some (σ₂, ψc₂,ψd₂)
             | _ => None
             end
           | _ => None
           end

         | NNRSLetMutColl v s₁ s₂ =>
           match nnrs_stmt_eval σc σ ((v,nil)::ψc) ψd s₁ with
           | Some (σ₁, ((_,dl)::ψc₁), ψd₁) =>
             match nnrs_stmt_eval σc ((v,Some (dcoll dl))::σ₁) ψc₁ ψd₁ s₂ with
             | Some ((_::σ₂), ψc₂, ψd₂) => Some (σ₂,ψc₂,ψd₂)
             | _ => None
             end
           | _ => None
           end

         | NNRSAssign v e =>
           match nnrs_expr_eval σc σ e, lookup string_dec ψd v with
           | Some d, Some _ => Some (σ, ψc, update_first string_dec ψd v (Some d))
           | _, _ => None
           end

         | NNRSPush v e =>
           match nnrs_expr_eval σc σ e, lookup string_dec ψc v with
           | Some d, Some dl => Some (σ, update_first string_dec ψc v (dl++d::nil)%list, ψd)
           | _, _ => None
           end

         | NNRSFor v e s₀ =>
           match nnrs_expr_eval σc σ e with
           | Some (dcoll c1) =>
             let fix for_fun (dl:list data) σ₁ ψc₁ ψd₁ :=
                 match dl with
                 | nil => Some (σ₁, ψc₁, ψd₁)
                 | d::dl' =>
                   match nnrs_stmt_eval σc ((v,Some d)::σ₁) ψc₁ ψd₁ s₀ with
                   | Some (_::σ₂, ψc₂, ψd₂) => for_fun dl' σ₂ ψc₂ ψd₂
                   | _ => None
                   end
                 end in
             for_fun c1 σ ψc ψd
           | _ => None
           end

         | NNRSIf e s₁ s₂ =>
           match nnrs_expr_eval σc σ e  with
           | Some (dbool true) => nnrs_stmt_eval σc σ ψc ψd s₁
           | Some (dbool false) => nnrs_stmt_eval σc σ ψc ψd s₂
           | _ => None
           end

         | NNRSEither e x₁ s₁ x₂ s₂ =>
           match nnrs_expr_eval σc σ e with
           | Some (dleft d) =>
             match nnrs_stmt_eval σc ((x₁,Some d)::σ) ψc ψd s₁ with
             | Some (_::σ₂, ψc₂, ψd₂) => Some (σ₂, ψc₂, ψd₂)
             | _ => None
             end
           | Some (dright d) =>
             match nnrs_stmt_eval σc ((x₂,Some d)::σ) ψc ψd s₂ with
             | Some (_::σ₂, ψc₂, ψd₂) => Some (σ₂, ψc₂, ψd₂)
             | _ => None
             end
           | _ => None
           end
         end.

    Definition nnrs_eval σc (q:nnrs) : option (option data) :=
      let (s, ret) := q in
      match nnrs_stmt_eval σc nil nil ((ret, None)::nil) s with
      | Some (_, _, (_,o)::_) => Some o
      | _ => None
      end.

    Definition nnrs_eval_top σc (q:nnrs) :=
      olift id (nnrs_eval (rec_sort σc) q).

  End Evaluation.

  Section Core.
    Program Definition nnrs_core_eval σc (q:nnrs_core)
      := nnrs_eval σc q.

    Program Definition nnrs_core_eval_top σc (q:nnrs_core)
      :=  olift id (nnrs_core_eval (rec_sort σc) q).
    
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


    Lemma nnrs_stmt_eval_env_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrs_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) ->
      σ₁ = σ₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrs_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRSSeq".
        apply IHs1 in eqq.
        apply IHs2 in sem.
        congruence.
      - Case "NNRSLet".
        invcs sem.
        specialize (IHs _ _ _ _ _ _ eqq0).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRSLetMut".
        invcs sem.
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs2; invcs IHs2; trivial.
        eauto.
      - Case "NNRSLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs2; invcs IHs2.
        congruence.
      - Case "NNRSAssign".
        invcs sem; trivial.
      - Case "NNRSPush".
        invcs sem; trivial.
      - Case  "NNRSFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem.
        induction l; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂  sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ _ _ _ _ H0).
        specialize (IHs _ _ _ _ _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRSIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRSEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ _ _ _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ _ _ _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.
    
    Lemma nnrs_stmt_eval_env_domain_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrs_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) -> domain σ₁ = domain σ₂.
    Proof.
      intros eqq.
      generalize (nnrs_stmt_eval_env_stack eqq); intros.
      congruence.
    Qed.

    Lemma nnrs_stmt_eval_mcenv_domain_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrs_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) -> domain ψc₁ = domain ψc₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrs_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRSSeq".
        transitivity (domain m0); eauto.
      - Case "NNRSLet".
        invcs sem.
        specialize (IHs _ _ _ _ _ _ eqq0).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRSLetMut".
        invcs sem.
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        etransitivity; eauto.
      - Case "NNRSLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs1; invcs IHs1.
        congruence.
      - Case "NNRSAssign".
        invcs sem; trivial.
      - Case "NNRSPush".
        invcs sem.
        rewrite domain_update_first; trivial.
      - Case  "NNRSFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem.
        induction l; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂  sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ _ _ _ _ H0).
        specialize (IHs _ _ _ _ _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRSIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRSEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ _ _ _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ _ _ _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrs_stmt_eval_mdenv_domain_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrs_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) -> domain ψd₁ = domain ψd₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrs_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRSSeq".
        transitivity (domain m); eauto.
      - Case "NNRSLet".
        invcs sem.
        specialize (IHs _ _ _ _ _ _ eqq0).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRSLetMut".
        invcs sem.
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs1; invcs IHs1; trivial.
        etransitivity; eauto.
      - Case "NNRSLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs1; invcs IHs1.
        congruence.
      - Case "NNRSAssign".
        invcs sem.
        rewrite domain_update_first; trivial.
      - Case "NNRSPush".
        invcs sem; trivial.
      - Case  "NNRSFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem.
        induction l; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂  sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ _ _ _ _ H0).
        specialize (IHs _ _ _ _ _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRSIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRSEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ _ _ _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ _ _ _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrs_stmt_eval_domain_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrs_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) ->
      σ₁ = σ₂
      /\ domain ψc₁ = domain ψc₂
      /\ domain ψd₁ = domain ψd₂.
    Proof.
      repeat split.
      - eapply nnrs_stmt_eval_env_stack; eauto.
      - eapply nnrs_stmt_eval_mcenv_domain_stack; eauto.
      - eapply nnrs_stmt_eval_mdenv_domain_stack; eauto.
    Qed.

    Local Close Scope string.
    
    Lemma nnrs_expr_eval_group_by_unfold σc σ g sl e :
      nnrs_expr_eval σc σ (NNRSGroupBy g sl e) = 
      match nnrs_expr_eval σc σ e with
      | Some (dcoll dl) => lift dcoll (group_by_nested_eval_table g sl dl)
      | _ => None
      end.
    Proof.
      reflexivity.
    Qed.

  End props.

  Section eval_eqs.

    Local Close Scope string.

    Lemma nnrs_expr_eval_same σc pd₁ pd₂ e :
      lookup_equiv_on (nnrs_expr_free_vars e) pd₁ pd₂ ->
      nnrs_expr_eval σc pd₁ e = nnrs_expr_eval σc pd₂ e.
    Proof.
      revert pd₁ pd₂.
      induction e; simpl; intros; eauto 3.
      - rewrite H; simpl; tauto.
      - apply lookup_equiv_on_dom_app in H; destruct H as [leo1 leo2].
        rewrite (IHe1 _ _ leo1).
        rewrite (IHe2 _ _ leo2).
        trivial.
      - rewrite (IHe _ _ H); trivial.
      - rewrite (IHe _ _ H); trivial.
    Qed.
    
    Lemma nnrs_expr_eval_free_env σc (l1 l2 l3:pd_bindings) e :
      disjoint (nnrs_expr_free_vars e) (domain l2) ->
      nnrs_expr_eval σc (l1 ++ l2 ++ l3) e
      =
      nnrs_expr_eval σc (l1 ++ l3) e.
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

    Lemma nnrs_expr_eval_free_env_tail σc (l1 l2:pd_bindings) e :
      disjoint (nnrs_expr_free_vars e) (domain l2) ->
      nnrs_expr_eval σc (l1 ++ l2) e
      =
      nnrs_expr_eval σc l1 e.
    Proof.
      intros.
      generalize (nnrs_expr_eval_free_env σc l1 l2 nil).
      repeat rewrite app_nil_r; auto.
    Qed.
    
    Lemma nnrs_expr_eval_unused_env c l σ e v d :
      (In v (domain l) 
       \/ ~ In v (nnrs_expr_free_vars e)) ->
      nnrs_expr_eval c (l ++ (v, d) :: σ) e
      = nnrs_expr_eval c (l ++ σ) e.
    Proof.
      intros inn.
      apply nnrs_expr_eval_same.
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
      
      Lemma nnrs_expr_eval_swap_env c l σ e v₁ v₂ d₁ d₂:
        v₁ <> v₂ ->
        nnrs_expr_eval c (l++(v₁,d₁)::(v₂,d₂)::σ) e =
        nnrs_expr_eval c (l++(v₂,d₂)::(v₁,d₁)::σ) e.
      Proof.
        intros neq.
        apply nnrs_expr_eval_same.
        unfold lookup_equiv_on; simpl; intros.
        repeat rewrite lookup_app.
        match_destr.
        simpl.
        repeat match_destr.
        congruence.
      Qed.

      Lemma nnrs_stmt_eval_swap_env c l σ ψc ψd s v₁ v₂ d₁ d₂:
        v₁ <> v₂ ->
        lift2P
          (fun '(σ₁', ψc₁', ψd₁') '(σ₂', ψc₂', ψd₂') =>
             (forall l' d₁' d₂' σ'',
                 domain l' = domain l ->
                 σ₁' = l' ++ (v₁,d₁')::(v₂,d₂')::σ'' ->
                 σ₂' = l' ++ (v₂,d₂')::(v₁,d₁')::σ'')
             /\ ψc₁' = ψc₂'
             /\ ψd₁' = ψd₂'
          )
          (nnrs_stmt_eval c (l++(v₁,d₁)::(v₂,d₂)::σ) ψc ψd s)
          (nnrs_stmt_eval c (l++(v₂,d₂)::(v₁,d₁)::σ) ψc ψd s).
      Proof.
        intros neq.
        revert l σ ψc ψd d₁ d₂.
        nnrs_stmt_cases (induction s) Case
        ; simpl; intros l σ ψc ψd d₁ d₂.
        - Case "NNRSSeq"%string.
          specialize (IHs1 l σ ψc ψd d₁ d₂).
          unfold lift2P in *.
          repeat match_option_in IHs1; try contradiction.
          destruct p as [[??]?].
          destruct p0 as [[??]?].
          destruct IHs1 as [eqs1 [eqs2 eqs3]].
          subst.
          apply nnrs_stmt_eval_domain_stack in eqq.
          destruct eqq as [eqd1 [eqd2 eqd3]].
          subst.
          specialize (eqs1 _ _ _ _ (eq_refl _) (eq_refl _)).
          subst.
          specialize (IHs2 l σ m1 m2 d₁ d₂).
          repeat match_option_in IHs2; try contradiction.
        - Case "NNRSLet"%string.
          rewrite nnrs_expr_eval_swap_env by trivial.
          match_destr; simpl; trivial.
          unfold lift2P in *.
          specialize (IHs ((v, Some d) :: l) σ ψc ψd d₁ d₂).
          simpl in IHs.
          unfold var in *.
          repeat match_option_in IHs; try contradiction.
          destruct p as [[??]?].
          destruct p0 as [[??]?].
          destruct IHs as [eqs1 [eqs2 eqs3]].
          subst.
          apply nnrs_stmt_eval_domain_stack in eqq.
          destruct eqq as [eqd1 [eqd2 eqd3]].
          subst.
          specialize (eqs1 ((v,Some d)::l) _ _ _ (eq_refl _) (eq_refl _)).
          subst; simpl.
          repeat split; trivial; intros.
          apply app_inv_head_domain in H0; trivial.
          destruct H0 as [eql1 eql2].
          invcs eql2; trivial.
        - Case "NNRSLetMut"%string.
          specialize (IHs1 l σ ψc ((v, None) :: ψd) d₁ d₂).
          unfold lift2P in *.
          repeat match_option_in IHs1; try contradiction.
          destruct p as [[??]?].
          destruct p0 as [[??]?].
          destruct IHs1 as [eqs1 [eqs2 eqs3]]; subst.
          apply nnrs_stmt_eval_domain_stack in eqq.
          destruct eqq as [eqd1 [eqd2 eqd3]]; subst.
          destruct m2; try discriminate.
          destruct p; simpl in *.
          simpl in eqd3; invcs eqd3.
          specialize (eqs1 _ _ _ _ (eq_refl _) (eq_refl _)); subst.
          specialize (IHs2 ((s, o) :: l) σ m1 m2 d₁ d₂).
          simpl in *.
          unfold var in *.
          repeat match_option_in IHs2; try contradiction.
          destruct p as [[??]?].
          destruct p0 as [[??]?].
          apply nnrs_stmt_eval_domain_stack in eqq.
          destruct eqq as [eqd1' [eqd2' eqd3']]; subst.
          destruct IHs2 as [eqs1' [eqs2' eqs3']]; subst.
          specialize (eqs1' ((s,o)::l) _ _ _ (eq_refl _) (eq_refl _)); subst; simpl.
          repeat split; trivial; intros.
          apply app_inv_head_domain in H0; trivial.
          destruct H0 as [eql1 eql2].
          invcs eql2; trivial.
        - Case "NNRSLetMutColl"%string.
          specialize (IHs1 l σ ((v,nil)::ψc) ψd d₁ d₂).
          unfold lift2P in *.
          repeat match_option_in IHs1; try contradiction.
          destruct p as [[??]?].
          destruct p0 as [[??]?].
          destruct IHs1 as [eqs1 [eqs2 eqs3]]; subst.
          apply nnrs_stmt_eval_domain_stack in eqq.
          destruct eqq as [eqd1 [eqd2 eqd3]]; subst.
          destruct m1; try discriminate.
          destruct p; simpl in *.
          simpl in eqd3; invcs eqd3.
          specialize (eqs1 _ _ _ _ (eq_refl _) (eq_refl _)); subst.
          specialize (IHs2 ((v, (Some (dcoll l0))) :: l) σ m1 m2 d₁ d₂).
          simpl in *.
          unfold var in *.
          repeat match_option_in IHs2; try contradiction.
          destruct p as [[??]?].
          destruct p0 as [[??]?].
          apply nnrs_stmt_eval_domain_stack in eqq.
          destruct eqq as [eqd1' [eqd2' eqd3']]; subst.
          destruct IHs2 as [eqs1' [eqs2' eqs3']]; subst.
          specialize (eqs1' ((v,Some (dcoll l0))::l) _ _ _ (eq_refl _) (eq_refl _)); subst; simpl.
          repeat split; trivial; intros.
          apply app_inv_head_domain in H1; trivial.
          destruct H1 as [eql1 eql2].
          invcs eql2; trivial.
        - Case "NNRSAssign"%string.
          rewrite nnrs_expr_eval_swap_env by trivial.
          destruct (nnrs_expr_eval c (l ++ (v₂, d₂) :: (v₁, d₁) :: σ) n); simpl; trivial.
          match_destr; simpl; trivial.
          repeat split; trivial; intros.
          apply app_inv_head_domain in H0; trivial.
          destruct H0 as [eql1 eql2].
          invcs eql2; trivial.
        - Case "NNRSPush"%string.
          rewrite nnrs_expr_eval_swap_env by trivial.
          destruct (nnrs_expr_eval c (l ++ (v₂, d₂) :: (v₁, d₁):: σ) n); simpl; trivial.
          match_destr; simpl; trivial.
          repeat split; trivial; intros.
          apply app_inv_head_domain in H0; trivial.
          destruct H0 as [eql1 eql2].
          invcs eql2; trivial.
        - Case "NNRSFor"%string.
          rewrite nnrs_expr_eval_swap_env by trivial.
          destruct (nnrs_expr_eval c (l ++ (v₂, d₂) :: (v₁, d₁) :: σ) n); simpl; trivial.
          match_destr; simpl; trivial.
          revert l σ ψc ψd d₁ d₂
          ; induction l0
          ; intros l σ ψc ψd d₁ d₂; simpl.
          + repeat split; trivial; intros.
            apply app_inv_head_domain in H0; trivial.
            destruct H0 as [eql1 eql2].
            invcs eql2; trivial.
          + specialize (IHs ((v, Some a) :: l) σ ψc ψd d₁ d₂).
            simpl in IHs.
            unfold lift2P in *.
            unfold var in *.
            repeat match_option_in IHs; try contradiction.
            destruct p as [[??]?].
            destruct p0 as [[??]?].
            destruct IHs as [eqs1 [eqs2 eqs3]].
            subst.
            apply nnrs_stmt_eval_domain_stack in eqq.
            destruct eqq as [eqd1 [eqd2 eqd3]].
            subst.
            specialize (eqs1 ((v,Some a)::l) _ _ _ (eq_refl _) (eq_refl _)).
            subst; simpl.
            specialize (IHl0 l σ m1 m2 d₁ d₂).
            simpl in *.
            unfold lift2P in *.
            unfold var in *.
            repeat match_option_in IHl0; try contradiction.
        - Case "NNRSIf"%string.
          rewrite nnrs_expr_eval_swap_env by trivial.
          match_destr; simpl; trivial.
          destruct d; simpl; trivial.
          destruct b; eauto.
        - Case "NNRSEither"%string.
          rewrite nnrs_expr_eval_swap_env by trivial.
          match_destr; simpl; trivial.
          destruct d; simpl; trivial.
          + unfold lift2P in *.
            specialize (IHs1 ((v, Some d) :: l) σ ψc ψd d₁ d₂).
            simpl in IHs1.
            unfold var in *.
            repeat match_option_in IHs1; try contradiction.
            destruct p as [[??]?].
            destruct p0 as [[??]?].
            destruct IHs1 as [eqs1 [eqs2 eqs3]].
            subst.
            apply nnrs_stmt_eval_domain_stack in eqq.
            destruct eqq as [eqd1 [eqd2 eqd3]].
            subst.
            specialize (eqs1 ((v,Some d)::l) _ _ _ (eq_refl _) (eq_refl _)).
            subst; simpl.
            repeat split; trivial; intros.
            apply app_inv_head_domain in H0; trivial.
            destruct H0 as [eql1 eql2].
            invcs eql2; trivial.
          + unfold lift2P in *.
            specialize (IHs2 ((v0, Some d) :: l) σ ψc ψd d₁ d₂).
            simpl in IHs2.
            unfold var in *.
            repeat match_option_in IHs2; try contradiction.
            destruct p as [[??]?].
            destruct p0 as [[??]?].
            destruct IHs2 as [eqs1 [eqs2 eqs3]].
            subst.
            apply nnrs_stmt_eval_domain_stack in eqq.
            destruct eqq as [eqd1 [eqd2 eqd3]].
            subst.
            specialize (eqs1 ((v0,Some d)::l) _ _ _ (eq_refl _) (eq_refl _)).
            subst; simpl.
            repeat split; trivial; intros.
            apply app_inv_head_domain in H0; trivial.
            destruct H0 as [eql1 eql2].
            invcs eql2; trivial.
      Qed.

    End swap.

    Section unused.

      
      Ltac disect_tac H stac
        := 
          unfold var in *
          ; cut_to H; unfold domain in *; [ | solve[stac]..]
          ; unfold lift2P in H
          ; (repeat match_option_in H; try contradiction).

      Ltac rename_inv_tac1 stac
        :=    unfold var in *
              ; repeat rewrite or_assoc
              ; try match goal with
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
                    | [H: _ * _ * _ |- _ ] => destruct H as [[??]?]; simpl in *
                    | [H: _ * _ |- _ ] => destruct H as [??]; simpl in *
                    | [H : nnrs_stmt_eval _ ?p1 _ _ _ = Some (?p2,_,_) |- _ ] =>
                      match p1 with
                      | p2 => fail 1
                      | _ => generalize (nnrs_stmt_eval_domain_stack H)
                             ; intros [?[??]]
                      end
                    | [H: ~ (_ \/ _) |- _] => apply not_or in H
                    | [H: _ /\ _ |- _ ] => destruct H
                    | [H: ?x = ?x |- _] => clear H
                    | [ H: forall a b c, _ -> ?x :: ?x1 ++ ?dd :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                      specialize (H (x::x1) (snd dd) x2); simpl in H
                      ; match dd with
                        | (_,_) => idtac
                        | _ => destruct dd
                        end
                      ; simpl in *
                      ; cut_to H; [ | eauto 3 | reflexivity]
                    | [ H: forall a b c, _ -> ?x1 ++ ?dd :: ?x2 = _ ++ _ :: _ -> _ |- _] =>
                      specialize (H x1 (snd dd) x2)
                      ; match dd with
                        | (_,_) => idtac
                        | _ => destruct dd
                        end
                      ; simpl in *
                      ; cut_to H; [ | eauto 3 | reflexivity]
                    | [H : ?x ++ _ = ?y ++ _ |- _ ] =>
                      let HH := fresh in
                      assert (HH:domain y = domain x) by (unfold domain in *; intuition congruence)
                      ; apply app_inv_head_domain in H;[clear HH|apply HH]
                    | [H: _ :: _ = _ :: _ |- _] => invcs H
                    | [H: ?x = (_,_) |- _ ] =>
                      match x with
                      | (_,_) => idtac
                      | _ => destruct x; simpl in H
                      end
                      ; invcs H
                    | [H: (_,_) = ?x |- _ ] =>
                      match x with
                      | (_,_) => fail 1
                      | _ => destruct x; simpl in H
                      end
                      ; invcs H
                    | [|- _ /\ _ ] => try split; [| tauto]
                    | [ |- lift2P _ (match ?x with
                                       _ => _
                                     end)
                                  (match ?x with
                                     _ => _
                                   end) ] => destruct x; try reflexivity
                    | [H:forall l es ec ed d, _ -> lift2P _ (nnrs_stmt_eval _ _ _ _ ?s) _
                                                          
                                              |- lift2P _ (nnrs_stmt_eval _ (?l ++ (_, ?d) :: ?σ) ?ψc ?ψd ?s)
                                                        _ ] => specialize (H l σ ψc ψd d)
                                                               ; disect_tac H stac

                    | [H:forall l es ec ed d, _ -> lift2P _ (nnrs_stmt_eval _ _ _ _ ?s) _
                                                          
                                              |- lift2P _ (match nnrs_stmt_eval _ (?l ++ (_, ?d) :: ?σ) ?ψc ?ψd ?s with
                                                           | Some _ => _
                                                           | None => _
                                                           end) _ ] => specialize (H l σ ψc ψd d)
                                                                       ; disect_tac H stac
                    | [H:forall l es ec ed d, _ -> lift2P _ (nnrs_stmt_eval _ _ _ _ ?s) _
                                                          
                                              |- lift2P _ (match nnrs_stmt_eval _ (?x :: ?l ++ (_, ?d) :: ?σ) ?ψc ?ψd ?s with
                                                           | Some _ => _
                                                           | None => _
                                                           end) _ ] => specialize (H (x::l) σ ψc ψd d); simpl in H
                                                                       ; disect_tac H stac
                    | [H:forall l es ec ed d, _ -> lift2P _ (nnrs_stmt_eval _ _ _ _ ?s) _
                                                          
                                              |- lift2P _ (nnrs_stmt_eval _ ?σ ?ψc (?l ++ (_, ?d) :: ?ψd) ?s)
                                                        _ ] => specialize (H l σ ψc ψd d)
                                                               ; disect_tac H stac

                    | [H:forall l es ec ed d, _ -> lift2P _ (nnrs_stmt_eval _ _ _ _ ?s) _
                                                          
                                              |- lift2P _ (match nnrs_stmt_eval _ ?σ ?ψc (?l ++ (_, ?d) :: ?ψd) ?s with
                                                           | Some _ => _
                                                           | None => _
                                                           end) _ ] => specialize (H l σ ψc ψd d)
                                                                       ; disect_tac H stac
                    | [H:forall l es ec ed d, _ -> lift2P _ (nnrs_stmt_eval _ _ _ _ ?s) _
                                                          
                                              |- lift2P _ (match nnrs_stmt_eval _ ?σ ?ψc (?x::?l ++ (_, ?d) :: ?ψd) ?s with
                                                           | Some _ => _
                                                           | None => _
                                                           end) _ ] => specialize (H (x::l) σ ψc ψd d); simpl in H
                                                                       ; disect_tac H stac
                    | [H:forall l es ec ed d, _ -> lift2P _ (nnrs_stmt_eval _ _ _ _ ?s) _
                                                          
                                              |- lift2P _ (nnrs_stmt_eval _ ?σ (?l ++ (_, ?d) :: ?ψc) ?ψd ?s)
                                                        _ ] => specialize (H l σ ψc ψd d)
                                                               ; disect_tac H stac

                    | [H:forall l es ec ed d, _ -> lift2P _ (nnrs_stmt_eval _ _ _ _ ?s) _
                                                          
                                              |- lift2P _ (match nnrs_stmt_eval _ ?σ (?l ++ (_, ?d) :: ?ψc) ?ψd ?s with
                                                           | Some _ => _
                                                           | None => _
                                                           end) _ ] => specialize (H l σ ψc ψd d)
                                                                       ; disect_tac H stac
                    | [H:forall l es ec ed d, _ -> lift2P _ (nnrs_stmt_eval _ _ _ _ ?s) _
                                                          
                                              |- lift2P _ (match nnrs_stmt_eval _ ?σ (?x::?l ++ (_, ?d) :: ?ψc) ?ψd ?s with
                                                           | Some _ => _
                                                           | None => _
                                                           end) _ ] => specialize (H (x::l) σ ψc ψd d); simpl in H
                                                                       ; disect_tac H stac

                                                                                    
                    | [H : ~ In _ (remove equiv_dec _ _) |- _ ] =>
                      apply not_in_remove_impl_not_in in H; [| congruence]
                    | [H : In _ (remove equiv_dec _ _) -> False |- _ ] =>
                      apply not_in_remove_impl_not_in in H; [| congruence]
                    | [H1: ?x = Some ?y,
                           H2: ?x = Some ?z |- _ ] =>
                      rewrite H1 in H2; invcs H2
                    | [|- ?x = ?y \/ _ ] => destruct (x == y); unfold equiv, complement in *
                                            ; [left; trivial | right]
                    end
              ; try subst; simpl in *; intros
              ; try congruence
      .
      Ltac unused_inv_tac := repeat progress (try rename_inv_tac1 ltac:( unused_inv_tac ; intuition unused_inv_tac); try rewrite nnrs_expr_eval_unused_env by tauto).

      Lemma nnrs_stmt_eval_unused_env c l σ ψc ψd s v d:
        (In v (domain l) \/
         ~ In v (nnrs_stmt_free_env_vars s)) ->
        lift2P
          (fun '(σ₁', ψc₁', ψd₁') '(σ₂', ψc₂', ψd₂') =>
             (forall l' d' σ'',
                 domain l' = domain l ->
                 σ₁' = l' ++ (v,d')::σ'' ->
                 σ₂' = l' ++ σ''
                 /\ ψc₁' = ψc₂'
                 /\ ψd₁' = ψd₂'
                 /\ d = d')
          )
          (nnrs_stmt_eval c (l++(v,d)::σ) ψc ψd s)
          (nnrs_stmt_eval c (l++σ) ψc ψd s).
      Proof.
        revert l σ ψc ψd d.
        nnrs_stmt_cases (induction s) Case
        ; simpl; intros l σ ψc ψd d inn
        ; repeat rewrite in_app_iff in inn
        ; unused_inv_tac.
        - Case "NNRSFor"%string.
          revert l σ ψc ψd d inn
          ; induction l0
          ; intros l σ ψc ψd d inn; simpl.
          + unused_inv_tac.
          + unused_inv_tac.
            specialize (IHl0 l σ m m0 d inn).
            unused_inv_tac.
      Qed.

      Lemma nnrs_stmt_eval_unused_mdenv c l σ ψc ψd s v d:
        (In v (domain l) \/
         ~ In v (nnrs_stmt_free_mdenv_vars s)) ->
        lift2P
          (fun '(σ₁', ψc₁', ψd₁') '(σ₂', ψc₂', ψd₂') =>
             (forall l' d' ψd'',
                 domain l' = domain l ->
                 ψd₁' = l' ++ (v,d')::ψd'' ->
                 σ₁' = σ₂'
                 /\ ψc₁' = ψc₂'
                 /\ ψd₂' = l' ++ ψd''
                 /\ d = d')
          )
          (nnrs_stmt_eval c σ ψc (l++(v,d)::ψd)   s)
          (nnrs_stmt_eval c σ  ψc (l++ψd) s).
      Proof.
        revert l σ ψc ψd d.
        nnrs_stmt_cases (induction s) Case
        ; simpl; intros l σ ψc ψd d inn
        ; repeat rewrite in_app_iff in inn
        ; unused_inv_tac.
        - Case "NNRSAssign"%string.
          repeat rewrite lookup_app.
          case_eq (lookup string_dec l v0); intros.
          + repeat split; trivial.
            assert (In v0 (domain l)) by (eapply lookup_in_domain; eauto).
            rewrite update_app_in in H1 by trivial.
            rewrite update_app_in by trivial.
            apply app_inv_head_domain in H1.
            * destruct H1 as [? eqq].
              invcs eqq; trivial.
            * rewrite domain_update_first; trivial.
            * generalize (lookup_in_domain _ _ H); intros.
              rewrite update_app_in in H1 by trivial.
              apply app_inv_head_domain in H1
              ; [| rewrite domain_update_first; trivial].
              destruct H1 as [eqq1 eqq2].
              invcs eqq2; trivial.
          + apply lookup_none_nin in H.
            repeat rewrite update_app_nin by trivial.
            simpl.
            destruct (string_dec v0 v)
            ; [subst; tauto | ].
            match_destr; try reflexivity.
            simpl.
            repeat split; trivial.
            apply app_inv_head_domain in H1.
            * destruct H1 as [? eqq].
              invcs eqq; trivial.
            * congruence.
            *  apply app_inv_head_domain in H1; trivial.
               destruct H1 as [eqq1 eqq2].
               invcs eqq2; trivial.
        - Case "NNRSFor"%string.
          revert l σ ψc ψd d inn
          ; induction l0
          ; intros l σ ψc ψd d inn; simpl.
          + unused_inv_tac.
          + unused_inv_tac.
            specialize (IHl0 x1 σ m x2 o).
            cut_to IHl0; unused_inv_tac.
            unfold lift2P in IHl0.
            repeat match_option_in IHl0.
            unused_inv_tac.
      Qed.

      Lemma nnrs_stmt_eval_unused_mcenv c l σ ψc ψd s v d:
        (In v (domain l) \/
         ~ In v (nnrs_stmt_free_mcenv_vars s)) ->
        lift2P
          (fun '(σ₁', ψc₁', ψd₁') '(σ₂', ψc₂', ψd₂') =>
             (forall l' d' ψc'',
                 domain l' = domain l ->
                 ψc₁' = l' ++ (v,d')::ψc'' ->
                 σ₁' = σ₂'
                 /\ ψc₂' = l' ++ ψc''
                 /\ ψd₁' = ψd₂'
                 /\ d = d')
          )
          (nnrs_stmt_eval c σ (l++(v,d)::ψc) ψd s)
          (nnrs_stmt_eval c σ (l++ψc) ψd s).
      Proof.
        revert l σ ψc ψd d.
        nnrs_stmt_cases (induction s) Case
        ; simpl; intros l σ ψc ψd d inn
        ; repeat rewrite in_app_iff in inn
        ; unused_inv_tac.
        - Case "NNRSPush"%string.
          repeat rewrite lookup_app.
          case_eq (lookup string_dec l v0); intros.
          + repeat split; trivial.
            assert (In v0 (domain l)) by (eapply lookup_in_domain; eauto).
            rewrite update_app_in in H1 by trivial.
            rewrite update_app_in by trivial.
            apply app_inv_head_domain in H1.
            * destruct H1 as [? eqq].
              invcs eqq; trivial.
            * rewrite domain_update_first; trivial.
            * generalize (lookup_in_domain _ _ H); intros.
              rewrite update_app_in in H1 by trivial.
              apply app_inv_head_domain in H1
              ; [| rewrite domain_update_first; trivial].
              destruct H1 as [eqq1 eqq2].
              invcs eqq2; trivial.
          + apply lookup_none_nin in H.
            simpl.
            repeat rewrite update_app_nin by trivial.
            simpl.
            destruct (string_dec v0 v)
            ; [subst; tauto | ].
            match_destr; try reflexivity.
            simpl.
            repeat split; trivial.
            rewrite update_app_nin by trivial.
            rewrite update_app_nin in H1 by trivial.
            simpl in H1.
            destruct (string_dec v0 v); try congruence.
            apply app_inv_head_domain in H1; trivial.
            * destruct H1 as [? eqq].
              simpl in *; subst.
              invcs eqq; trivial.
            * rewrite update_app_nin in H1 by trivial.
              apply app_inv_head_domain in H1; trivial.
              destruct H1 as [eqq1 eqq2].
              simpl in eqq2.
              match_destr_in eqq2; try congruence.
        - Case "NNRSFor"%string.
          revert l σ ψc ψd d inn
          ; induction l0
          ; intros l σ ψc ψd d inn; simpl.
          + unused_inv_tac.
          + unused_inv_tac.
            specialize (IHl0 x1 σ x2 m0 l1).
            cut_to IHl0; unused_inv_tac.
            unfold lift2P in IHl0.
            repeat match_option_in IHl0.
            unused_inv_tac.
      Qed.
      
    End unused.
    
  End eval_eqs.

End NNRSEval.

Arguments nnrs_stmt_eval_env_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.
Arguments nnrs_stmt_eval_env_domain_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.
Arguments nnrs_stmt_eval_mcenv_domain_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.
Arguments nnrs_stmt_eval_mdenv_domain_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.

Arguments nnrs_stmt_eval_domain_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.