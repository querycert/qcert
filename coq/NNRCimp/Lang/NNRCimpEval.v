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

  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).
  Context (σc:list (string*data)).

  Local Open Scope nnrc_imp.
  Local Open Scope string.

  (** ** Evaluation Semantics *)
  Section Evaluation.

    (** Evaluation takes a NNRCimp expression and an environment. It
          returns an optional value. When [None] is returned, it
          denotes an error. An error is always propagated. *)

    Fixpoint nnrc_imp_expr_eval
             (σ:pd_bindings) (e:nnrc_imp_expr)
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
                  (nnrc_imp_expr_eval σ e₁)
                  (nnrc_imp_expr_eval σ e₂)

         | NNRCimpUnop uop e =>
           olift (fun d => unary_op_eval h uop d)
                 (nnrc_imp_expr_eval σ e)

         | NNRCimpGroupBy g sl e =>
           match nnrc_imp_expr_eval σ e with
           | Some (dcoll dl) => lift dcoll (group_by_nested_eval_table g sl dl)
           | _ => None
           end
         end.

    Fixpoint nnrc_imp_stmt_eval
             (σ:pd_bindings) (ψ:mc_bindings)
             (s:nnrc_imp_stmt) : option (pd_bindings*mc_bindings)
      := match s with
         | NNRCimpSeq s₁ s₂ =>
           match nnrc_imp_stmt_eval σ ψ s₁ with
           | Some (σ₁, ψ₁) => nnrc_imp_stmt_eval σ₁ ψ₁ s₂
           | None => None
           end

         | NNRCimpLetMut v (Some e) s₀ =>
           match nnrc_imp_expr_eval σ e with
           | Some d =>
             match nnrc_imp_stmt_eval ((v,Some d)::σ) ψ s₀ with
             | Some (_::σ₁, ψ₁) => Some (σ₁, ψ₁)
             | _ => None
             end
           | None => None
           end

         | NNRCimpLetMut v None s₀ =>
           match nnrc_imp_stmt_eval ((v,None)::σ) ψ s₀ with
           | Some (_::σ₁, ψ₁) => Some (σ₁, ψ₁)
           | _ => None
           end

         | NNRCimpBuildCollFor v s₁ s₂ =>
           match nnrc_imp_stmt_eval σ ((v,nil)::ψ) s₁ with
           | Some (σ₁, ((_,dl)::ψ₁)) =>
             match nnrc_imp_stmt_eval ((v,Some (dcoll dl))::σ₁) ψ₁ s₂ with
             | Some ((_::σ₂),ψ₂) => Some (σ₂,ψ₂)
             | _ => None
             end
           | _ => None
           end

         | NNRCimpPush v e =>
           match nnrc_imp_expr_eval σ e, lookup string_dec ψ v with
           | Some d, Some dl => Some (σ, update_first string_dec ψ v (d::dl))
           | _, _ => None
           end

         | NNRCimpAssign v e =>
           match nnrc_imp_expr_eval σ e, lookup string_dec σ v with
           | Some d, Some _ => Some (update_first string_dec σ v (Some d), ψ)
           | _, _ => None
           end

         | NNRCimpFor v e s₀ =>
           match nnrc_imp_expr_eval σ e with
           | Some (dcoll c1) =>
             let fix for_fun (dl:list data) σ₁ ψ₁ :=
                 match dl with
                 | nil => Some (σ₁, ψ₁)
                 | d::dl' =>
                   match nnrc_imp_stmt_eval ((v,Some d)::σ₁) ψ₁ s₀ with
                   | Some (_::σ₂, ψ₂) => for_fun dl' σ₂ ψ₂
                   | _ => None
                   end
                 end in
             for_fun c1 σ ψ
           | _ => None
           end

         | NNRCimpIf e s₁ s₂ =>
           match nnrc_imp_expr_eval σ e  with
           | Some (dbool true) => nnrc_imp_stmt_eval σ ψ s₁
           | Some (dbool false) => nnrc_imp_stmt_eval σ ψ s₂
           | _ => None
           end

         | NNRCimpEither e x₁ s₁ x₂ s₂ =>
           match nnrc_imp_expr_eval σ e with
           | Some (dleft d) =>
             match nnrc_imp_stmt_eval ((x₁,Some d)::σ) ψ s₁ with
             | Some (_::σ₂, ψ₂) => Some (σ₂, ψ₂)
             | _ => None
             end
           | Some (dright d) =>
             match nnrc_imp_stmt_eval ((x₂,Some d)::σ) ψ s₂ with
             | Some (_::σ₂, ψ₂) => Some (σ₂, ψ₂)
             | _ => None
             end
           | _ => None
           end
         end.

    Definition nnrc_imp_eval_top (q:nnrc_imp) : option data
      :=
        let (s, ret) := q in
        match nnrc_imp_stmt_eval ((ret, None)::nil) nil s with
        | Some ((_, Some dd)::_, _) => Some dd
        | _ => None
        end.

  End Evaluation.

  Section props.

    Ltac destr H :=
      let eqq := fresh "eqq" in
      first [(match_case_in H;
              [intros [??] eqq | intros eqq]; rewrite eqq in H; try discriminate)
            | (match_case_in H;
               [intros ? eqq | intros eqq]; rewrite eqq in H; try discriminate)
            | (match_case_in H;
               [intros eqq | intros ? ? eqq]; try rewrite eqq in H; try discriminate)
            | (match_case_in H;
               [intros eqq | intros ? eqq]; try rewrite eqq in H; try discriminate)
            ]; subst.

    Lemma nnrc_imp_stmt_eval_env_stack {s σ₁ ψ₁ σ₂ ψ₂} :
      nnrc_imp_stmt_eval σ₁ ψ₁ s = Some (σ₂ , ψ₂ ) -> domain σ₁ = domain σ₂.
    Proof.
      revert σ₁ ψ₁ σ₂ ψ₂.
      nnrc_imp_stmt_cases (induction s) Case; intros σ₁ ψ₁ σ₂ ψ₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRCimpSeq".
        transitivity (domain p); eauto.
      - Case "NNRCimpLetMut".
        invcs sem.
        specialize (IHs _ _ _ _ eqq0).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRCimpLetMut".
        invcs sem.
        specialize (IHs _ _ _ _ eqq).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRCimpBuildCollFor".
        destruct p0; repeat destr sem.
        specialize (IHs1 _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ eqq0).
        simpl in IHs2; invcs IHs2.
        congruence.
      - Case "NNRCimpPush".
        invcs sem; trivial.
      - Case "NNRCimpAssign".
        invcs sem.
        rewrite domain_update_first; trivial.
      - Case  "NNRCimpFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ ψ₁ σ₂ ψ₂ sem.
        induction l; intros σ₁ ψ₁ σ₂ ψ₂ sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ _ _ H0).
        specialize (IHs _ _ _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRCimpIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRCimpEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrc_imp_stmt_eval_mcenv_stack {s σ₁ ψ₁ σ₂ ψ₂} :
      nnrc_imp_stmt_eval σ₁ ψ₁ s = Some (σ₂ , ψ₂ ) -> domain ψ₁ = domain ψ₂.
    Proof.
      revert σ₁ ψ₁ σ₂ ψ₂.
      nnrc_imp_stmt_cases (induction s) Case; intros σ₁ ψ₁ σ₂ ψ₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRCimpSeq".
        transitivity (domain m); eauto.
      - Case "NNRCimpLetMut".
        invcs sem.
        specialize (IHs _ _ _ _ eqq0).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRCimpLetMut".
        invcs sem.
        specialize (IHs _ _ _ _ eqq).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRCimpBuildCollFor".
        destruct p0; repeat destr sem.
        specialize (IHs1 _ _ _ _ eqq).
        specialize (IHs2 _ _ _ _ eqq0).
        simpl in IHs1; invcs IHs1.
        congruence.
      - Case "NNRCimpPush".
        invcs sem.
        rewrite domain_update_first; trivial.
      - Case "NNRCimpAssign".
        invcs sem; trivial.
      - Case  "NNRCimpFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ ψ₁ σ₂ ψ₂ sem.
        induction l; intros σ₁ ψ₁ σ₂ ψ₂ sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ _ _ H0).
        specialize (IHs _ _ _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRCimpIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRCimpEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ _ _ eqq0);
            simpl in IHs2; invcs IHs2; trivial.
    Qed.

  End props.

End NNRCimpEval.

Arguments nnrc_imp_stmt_eval_env_stack {fruntime h σc s σ₁ ψ₁ σ₂ ψ₂}.
Arguments nnrc_imp_stmt_eval_mcenv_stack {fruntime h σc s σ₁ ψ₁ σ₂ ψ₂}.