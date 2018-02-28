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

(** NNRCimp is a variant of the named nested relational calculus
     (NNRC) that is meant to be more imperative in feel.  It is used
     as an intermediate language between NNRC and more imperative /
     statement oriented backends *)

Section NNRCimpEval.
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
  Require Import NNRCimp.
  Require Import NNRCimpVars.

  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  Local Open Scope nnrc_imp.
  Local Open Scope string.

  (** ** Evaluation Semantics *)
  Section Evaluation.

    (** Evaluation takes a NNRCimp expression and an environment. It
          returns an optional value. When [None] is returned, it
          denotes an error. An error is always propagated. *)

    Fixpoint nnrc_imp_expr_eval
             (σc:bindings) (σ:pd_bindings) (e:nnrc_imp_expr)
      : option data
      := match e with
         | NNRCimpGetConstant v =>
           edot σc v

         | NNRCimpVar v =>
           olift id (lookup equiv_dec σ v)

         | NNRCimpConst d =>
           Some (normalize_data h d)

         | NNRCimpBinop bop e₁ e₂ =>
           olift2 (fun d₁ d₂ => binary_op_eval h bop d₁ d₂)
                  (nnrc_imp_expr_eval σc σ e₁)
                  (nnrc_imp_expr_eval σc σ e₂)

         | NNRCimpUnop uop e =>
           olift (fun d => unary_op_eval h uop d)
                 (nnrc_imp_expr_eval σc σ e)

         | NNRCimpGroupBy g sl e =>
           match nnrc_imp_expr_eval σc σ e with
           | Some (dcoll dl) => lift dcoll (group_by_nested_eval_table g sl dl)
           | _ => None
           end
         end.

    Fixpoint nnrc_imp_stmt_eval
             (σc:bindings) (σ:pd_bindings) (ψc:mc_bindings) (ψd:md_bindings)
             (s:nnrc_imp_stmt) : option (pd_bindings*mc_bindings*md_bindings)
      := match s with
         | NNRCimpSeq s₁ s₂ =>
           match nnrc_imp_stmt_eval σc σ ψc ψd s₁ with
           | Some (σ₁, ψc₁, ψd₁) => nnrc_imp_stmt_eval σc σ₁ ψc₁ ψd₁ s₂
           | None => None
           end

         | NNRCimpLet v e s₀ =>
           match nnrc_imp_expr_eval σc σ e with
           | Some d =>
             match nnrc_imp_stmt_eval σc ((v,Some d)::σ) ψc ψd s₀ with
             | Some (_::σ₁, ψc₁, ψd₁) => Some (σ₁, ψc₁,ψd₁)
             | _ => None
             end
           | None => None
           end

         | NNRCimpLetMut v s₁ s₂ =>
           match nnrc_imp_stmt_eval σc σ ψc ((v,None)::ψd) s₁ with
           | Some (σ₁, ψc₁, (_,d)::ψd₁) =>
             match nnrc_imp_stmt_eval σc ((v,d)::σ₁) ψc₁ ψd₁ s₂ with
             | Some (_::σ₂, ψc₂, ψd₂) => Some (σ₂, ψc₂,ψd₂)
             | _ => None
             end
           | _ => None
           end

         | NNRCimpLetMutColl v s₁ s₂ =>
           match nnrc_imp_stmt_eval σc σ ((v,nil)::ψc) ψd s₁ with
           | Some (σ₁, ((_,dl)::ψc₁), ψd₁) =>
             match nnrc_imp_stmt_eval σc ((v,Some (dcoll dl))::σ₁) ψc₁ ψd₁ s₂ with
             | Some ((_::σ₂), ψc₂, ψd₂) => Some (σ₂,ψc₂,ψd₂)
             | _ => None
             end
           | _ => None
           end

         | NNRCimpAssign v e =>
           match nnrc_imp_expr_eval σc σ e, lookup string_dec ψd v with
           | Some d, Some _ => Some (σ, ψc, update_first string_dec ψd v (Some d))
           | _, _ => None
           end

         | NNRCimpPush v e =>
           match nnrc_imp_expr_eval σc σ e, lookup string_dec ψc v with
           | Some d, Some dl => Some (σ, update_first string_dec ψc v (d::dl), ψd)
           | _, _ => None
           end

         | NNRCimpFor v e s₀ =>
           match nnrc_imp_expr_eval σc σ e with
           | Some (dcoll c1) =>
             let fix for_fun (dl:list data) σ₁ ψc₁ ψd₁ :=
                 match dl with
                 | nil => Some (σ₁, ψc₁, ψd₁)
                 | d::dl' =>
                   match nnrc_imp_stmt_eval σc ((v,Some d)::σ₁) ψc₁ ψd₁ s₀ with
                   | Some (_::σ₂, ψc₂, ψd₂) => for_fun dl' σ₂ ψc₂ ψd₂
                   | _ => None
                   end
                 end in
             for_fun c1 σ ψc ψd
           | _ => None
           end

         | NNRCimpIf e s₁ s₂ =>
           match nnrc_imp_expr_eval σc σ e  with
           | Some (dbool true) => nnrc_imp_stmt_eval σc σ ψc ψd s₁
           | Some (dbool false) => nnrc_imp_stmt_eval σc σ ψc ψd s₂
           | _ => None
           end

         | NNRCimpEither e x₁ s₁ x₂ s₂ =>
           match nnrc_imp_expr_eval σc σ e with
           | Some (dleft d) =>
             match nnrc_imp_stmt_eval σc ((x₁,Some d)::σ) ψc ψd s₁ with
             | Some (_::σ₂, ψc₂, ψd₂) => Some (σ₂, ψc₂, ψd₂)
             | _ => None
             end
           | Some (dright d) =>
             match nnrc_imp_stmt_eval σc ((x₂,Some d)::σ) ψc ψd s₂ with
             | Some (_::σ₂, ψc₂, ψd₂) => Some (σ₂, ψc₂, ψd₂)
             | _ => None
             end
           | _ => None
           end
         end.

    Definition nnrc_imp_eval_top (q:nnrc_imp) (σc:bindings) : option data
      :=
        let (s, ret) := q in
        match nnrc_imp_stmt_eval σc ((ret, None)::nil) nil nil s with
        | Some ((_, Some dd)::_, _, _) => Some dd
        | _ => None
        end.

  End Evaluation.

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

    Lemma nnrc_imp_stmt_eval_env_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrc_imp_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) -> domain σ₁ = domain σ₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrc_imp_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRCimpSeq".
        transitivity (domain p); eauto.
      - Case "NNRCimpLet".
        invcs sem.
        specialize (IHs _ _ _ _ _ _ eqq0).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRCimpLetMut".
        invcs sem.
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs2; invcs IHs2; trivial.
        eauto.
      - Case "NNRCimpLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs2; invcs IHs2.
        congruence.
      - Case "NNRCimpAssign".
        invcs sem; trivial.
      - Case "NNRCimpPush".
        invcs sem; trivial.
      - Case  "NNRCimpFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem.
        induction l; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂  sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ _ _ _ _ H0).
        specialize (IHs _ _ _ _ _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRCimpIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRCimpEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ _ _ _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ _ _ _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrc_imp_stmt_eval_mcenv_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrc_imp_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) -> domain ψc₁ = domain ψc₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrc_imp_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRCimpSeq".
        transitivity (domain m0); eauto.
      - Case "NNRCimpLet".
        invcs sem.
        specialize (IHs _ _ _ _ _ _ eqq0).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRCimpLetMut".
        invcs sem.
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        etransitivity; eauto.
      - Case "NNRCimpLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs1; invcs IHs1.
        congruence.
      - Case "NNRCimpAssign".
        invcs sem; trivial.
      - Case "NNRCimpPush".
        invcs sem.
        rewrite domain_update_first; trivial.
      - Case  "NNRCimpFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem.
        induction l; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂  sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ _ _ _ _ H0).
        specialize (IHs _ _ _ _ _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRCimpIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRCimpEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ _ _ _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ _ _ _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrc_imp_stmt_eval_mdenv_stack {s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂} :
      nnrc_imp_stmt_eval σc σ₁ ψc₁ ψd₁ s = Some (σ₂ , ψc₂, ψd₂ ) -> domain ψd₁ = domain ψd₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrc_imp_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRCimpSeq".
        transitivity (domain m); eauto.
      - Case "NNRCimpLet".
        invcs sem.
        specialize (IHs _ _ _ _ _ _ eqq0).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRCimpLetMut".
        invcs sem.
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs1; invcs IHs1; trivial.
        etransitivity; eauto.
      - Case "NNRCimpLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ _ _ eqq0).
        simpl in IHs1; invcs IHs1.
        congruence.
      - Case "NNRCimpAssign".
        invcs sem.
        rewrite domain_update_first; trivial.
      - Case "NNRCimpPush".
        invcs sem; trivial.
      - Case  "NNRCimpFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem.
        induction l; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂  sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ _ _ _ _ H0).
        specialize (IHs _ _ _ _ _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRCimpIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRCimpEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ _ _ _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ _ _ _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrc_imp_expr_eval_same σc pd₁ pd₂ s :
      lookup_equiv_on (nnrc_imp_expr_free_vars s) pd₁ pd₂ ->
      nnrc_imp_expr_eval σc pd₁ s = nnrc_imp_expr_eval σc pd₂ s.
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
    
  End props.

End NNRCimpEval.

Arguments nnrc_imp_stmt_eval_env_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.
Arguments nnrc_imp_stmt_eval_mcenv_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.
Arguments nnrc_imp_stmt_eval_mdenv_stack {fruntime h s σc σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.