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

(** NNRCimpish is a variant of the named nested relational calculus
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
Require Import NNRCimpish.
Require Import NNRCimpishVars.

Section NNRCimpishEval.
  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  Local Open Scope nnrc_impish.
  Local Open Scope string.

  (** ** Evaluation Semantics *)
  Section Evaluation.

    (** Evaluation takes a NNRCimpish expression and an environment. It
          returns an optional value. When [None] is returned, it
          denotes an error. An error is always propagated. *)

    Fixpoint nnrc_impish_expr_eval
             (σc:bindings) (σ:pd_bindings) (e:nnrc_impish_expr)
    : option data
      := match e with
         | NNRCimpishGetConstant v =>
           edot σc v

         | NNRCimpishVar v =>
           olift id (lookup equiv_dec σ v)

         | NNRCimpishConst d =>
           Some (normalize_data h d)

         | NNRCimpishBinop bop e₁ e₂ =>
           olift2 (fun d₁ d₂ => binary_op_eval h bop d₁ d₂)
                  (nnrc_impish_expr_eval σc σ e₁)
                  (nnrc_impish_expr_eval σc σ e₂)

         | NNRCimpishUnop uop e =>
           olift (fun d => unary_op_eval h uop d)
                 (nnrc_impish_expr_eval σc σ e)

         | NNRCimpishGroupBy g sl e =>
           match nnrc_impish_expr_eval σc σ e with
           | Some (dcoll dl) => lift dcoll (group_by_nested_eval_table g sl dl)
           | _ => None
           end
         end.

    Fixpoint nnrc_impish_stmt_eval
             (σc:bindings) (σ:pd_bindings) (ψc:mc_bindings) (ψd:md_bindings)
             (s:nnrc_impish_stmt) : option (pd_bindings*mc_bindings*md_bindings)
      := match s with
         | NNRCimpishSeq s₁ s₂ =>
           match nnrc_impish_stmt_eval σc σ ψc ψd s₁ with
           | Some (σ₁, ψc₁, ψd₁) => nnrc_impish_stmt_eval σc σ₁ ψc₁ ψd₁ s₂
           | None => None
           end

         | NNRCimpishLet v e s₀ =>
           match nnrc_impish_expr_eval σc σ e with
           | Some d =>
             match nnrc_impish_stmt_eval σc ((v,Some d)::σ) ψc ψd s₀ with
             | Some (_::σ₁, ψc₁, ψd₁) => Some (σ₁, ψc₁,ψd₁)
             | _ => None
             end
           | None => None
           end

         | NNRCimpishLetMut v s₁ s₂ =>
           match nnrc_impish_stmt_eval σc σ ψc ((v,None)::ψd) s₁ with
           | Some (σ₁, ψc₁, (_,d)::ψd₁) =>
             match nnrc_impish_stmt_eval σc ((v,d)::σ₁) ψc₁ ψd₁ s₂ with
             | Some (_::σ₂, ψc₂, ψd₂) => Some (σ₂, ψc₂,ψd₂)
             | _ => None
             end
           | _ => None
           end

         | NNRCimpishLetMutColl v s₁ s₂ =>
           match nnrc_impish_stmt_eval σc σ ((v,nil)::ψc) ψd s₁ with
           | Some (σ₁, ((_,dl)::ψc₁), ψd₁) =>
             match nnrc_impish_stmt_eval σc ((v,Some (dcoll dl))::σ₁) ψc₁ ψd₁ s₂ with
             | Some ((_::σ₂), ψc₂, ψd₂) => Some (σ₂,ψc₂,ψd₂)
             | _ => None
             end
           | _ => None
           end

         | NNRCimpishAssign v e =>
           match nnrc_impish_expr_eval σc σ e, lookup string_dec ψd v with
           | Some d, Some _ => Some (σ, ψc, update_first string_dec ψd v (Some d))
           | _, _ => None
           end

         | NNRCimpishPush v e =>
           match nnrc_impish_expr_eval σc σ e, lookup string_dec ψc v with
           | Some d, Some dl => Some (σ, update_first string_dec ψc v (dl++d::nil)%list, ψd)
           | _, _ => None
           end

         | NNRCimpishFor v e s₀ =>
           match nnrc_impish_expr_eval σc σ e with
           | Some (dcoll c1) =>
             let fix for_fun (dl:list data) σ₁ ψc₁ ψd₁ :=
                 match dl with
                 | nil => Some (σ₁, ψc₁, ψd₁)
                 | d::dl' =>
                   match nnrc_impish_stmt_eval σc ((v,Some d)::σ₁) ψc₁ ψd₁ s₀ with
                   | Some (_::σ₂, ψc₂, ψd₂) => for_fun dl' σ₂ ψc₂ ψd₂
                   | _ => None
                   end
                 end in
             for_fun c1 σ ψc ψd
           | _ => None
           end

         | NNRCimpishIf e s₁ s₂ =>
           match nnrc_impish_expr_eval σc σ e  with
           | Some (dbool true) => nnrc_impish_stmt_eval σc σ ψc ψd s₁
           | Some (dbool false) => nnrc_impish_stmt_eval σc σ ψc ψd s₂
           | _ => None
           end

         | NNRCimpishEither e x₁ s₁ x₂ s₂ =>
           match nnrc_impish_expr_eval σc σ e with
           | Some (dleft d) =>
             match nnrc_impish_stmt_eval σc ((x₁,Some d)::σ) ψc ψd s₁ with
             | Some (_::σ₂, ψc₂, ψd₂) => Some (σ₂, ψc₂, ψd₂)
             | _ => None
             end
           | Some (dright d) =>
             match nnrc_impish_stmt_eval σc ((x₂,Some d)::σ) ψc ψd s₂ with
             | Some (_::σ₂, ψc₂, ψd₂) => Some (σ₂, ψc₂, ψd₂)
             | _ => None
             end
           | _ => None
           end
         end.

    Definition nnrc_impish_eval σc (q:nnrc_impish) : option (option data) :=
      let (s, ret) := q in
      match nnrc_impish_stmt_eval σc nil nil ((ret, None)::nil) s with
      | Some (_, _, (_,o)::_) => Some o
      | _ => None
      end.

    Definition nnrc_impish_eval_top σc (q:nnrc_impish) :=
      olift id (nnrc_impish_eval (rec_sort σc) q).

  End Evaluation.

  Section Core.
    Program Definition nnrc_impish_core_eval σc (q:nnrc_impish_core)
      := nnrc_impish_eval σc q.

    Program Definition nnrc_impish_core_eval_top σc (q:nnrc_impish_core)
      :=  olift id (nnrc_impish_core_eval (rec_sort σc) q).
    
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


    Lemma nnrc_impish_stmt_eval_env_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrc_impish_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) ->
      σ₁ = σ₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrc_impish_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRCimpishSeq".
        apply IHs1 in eqq.
        apply IHs2 in sem.
        congruence.
      - Case "NNRCimpishLet".
        invcs sem.
        specialize (IHs _ _ _ _ _ _ eqq0).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRCimpishLetMut".
        invcs sem.
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs2; invcs IHs2; trivial.
        eauto.
      - Case "NNRCimpishLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs2; invcs IHs2.
        congruence.
      - Case "NNRCimpishAssign".
        invcs sem; trivial.
      - Case "NNRCimpishPush".
        invcs sem; trivial.
      - Case  "NNRCimpishFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem.
        induction l; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂  sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ _ _ _ _ H0).
        specialize (IHs _ _ _ _ _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRCimpishIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRCimpishEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ _ _ _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ _ _ _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.
    
    Lemma nnrc_impish_stmt_eval_env_domain_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrc_impish_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) -> domain σ₁ = domain σ₂.
    Proof.
      intros eqq.
      generalize (nnrc_impish_stmt_eval_env_stack eqq); intros.
      congruence.
    Qed.

    Lemma nnrc_impish_stmt_eval_mcenv_domain_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrc_impish_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) -> domain ψc₁ = domain ψc₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrc_impish_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRCimpishSeq".
        transitivity (domain m0); eauto.
      - Case "NNRCimpishLet".
        invcs sem.
        specialize (IHs _ _ _ _ _ _ eqq0).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRCimpishLetMut".
        invcs sem.
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        etransitivity; eauto.
      - Case "NNRCimpishLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs1; invcs IHs1.
        congruence.
      - Case "NNRCimpishAssign".
        invcs sem; trivial.
      - Case "NNRCimpishPush".
        invcs sem.
        rewrite domain_update_first; trivial.
      - Case  "NNRCimpishFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem.
        induction l; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂  sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ _ _ _ _ H0).
        specialize (IHs _ _ _ _ _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRCimpishIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRCimpishEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ _ _ _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ _ _ _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrc_impish_stmt_eval_mdenv_domain_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrc_impish_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) -> domain ψd₁ = domain ψd₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrc_impish_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRCimpishSeq".
        transitivity (domain m); eauto.
      - Case "NNRCimpishLet".
        invcs sem.
        specialize (IHs _ _ _ _ _ _ eqq0).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRCimpishLetMut".
        invcs sem.
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs1; invcs IHs1; trivial.
        etransitivity; eauto.
      - Case "NNRCimpishLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs1; invcs IHs1.
        congruence.
      - Case "NNRCimpishAssign".
        invcs sem.
        rewrite domain_update_first; trivial.
      - Case "NNRCimpishPush".
        invcs sem; trivial.
      - Case  "NNRCimpishFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem.
        induction l; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂  sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ _ _ _ _ H0).
        specialize (IHs _ _ _ _ _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRCimpishIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRCimpishEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ _ _ _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ _ _ _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrc_impish_expr_eval_same σc pd₁ pd₂ s :
      lookup_equiv_on (nnrc_impish_expr_free_vars s) pd₁ pd₂ ->
      nnrc_impish_expr_eval σc pd₁ s = nnrc_impish_expr_eval σc pd₂ s.
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

    Lemma nnrc_impish_expr_eval_group_by_unfold σc σ g sl e :
      nnrc_impish_expr_eval σc σ (NNRCimpishGroupBy g sl e) = 
      match nnrc_impish_expr_eval σc σ e with
      | Some (dcoll dl) => lift dcoll (group_by_nested_eval_table g sl dl)
      | _ => None
      end.
    Proof.
      reflexivity.
    Qed.

  End props.

End NNRCimpishEval.

Arguments nnrc_impish_stmt_eval_env_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.
Arguments nnrc_impish_stmt_eval_env_domain_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.
Arguments nnrc_impish_stmt_eval_mcenv_domain_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.
Arguments nnrc_impish_stmt_eval_mdenv_domain_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.