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

Section NNRCimpEval.

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
             (σc:bindings) (s:nnrc_imp_stmt) 
             (σ:pd_bindings) : option (pd_bindings)
      := match s with
         | NNRCimpSeq s₁ s₂ =>
           olift (nnrc_imp_stmt_eval σc s₂)
                 (nnrc_imp_stmt_eval σc s₁ σ)
                 
         | NNRCimpAssign v e =>
           match nnrc_imp_expr_eval σc σ e, lookup string_dec σ v with
           | Some d, Some _ => Some (update_first string_dec σ v (Some d))
           | _, _ => None
           end
             
         | NNRCimpLet v eo s₀ =>
           let evals := (fun init =>
                           match nnrc_imp_stmt_eval σc s₀ ((v,init)::σ) with
                           | Some (_::σ') => Some σ'
                           | _ => None
                           end) in
           match eo with
           | Some e => olift evals (lift Some (nnrc_imp_expr_eval σc σ e))
           | None => evals None
           end
             
         | NNRCimpFor v e s₀ =>
           match nnrc_imp_expr_eval σc σ e with
           | Some (dcoll c1) =>
             let fix for_fun (dl:list data) σ₁ :=
                 match dl with
                 | nil => Some σ₁
                 | d::dl' =>
                   match nnrc_imp_stmt_eval σc s₀ ((v,Some d)::σ₁) with
                   | Some (_::σ₂) => for_fun dl' σ₂ 
                   | _ => None
                   end
                 end in
             for_fun c1 σ 
           | _ => None
           end

         | NNRCimpIf e s₁ s₂ =>
           match nnrc_imp_expr_eval σc σ e  with
           | Some (dbool true) => nnrc_imp_stmt_eval σc s₁ σ
           | Some (dbool false) => nnrc_imp_stmt_eval σc s₂ σ
           | _ => None
           end

         | NNRCimpEither e x₁ s₁ x₂ s₂ =>
           match nnrc_imp_expr_eval σc σ e with
           | Some (dleft d) =>
             match nnrc_imp_stmt_eval σc s₁ ((x₁,Some d)::σ) with
             | Some (_::σ₂) => Some σ₂
             | _ => None
             end
           | Some (dright d) =>
             match nnrc_imp_stmt_eval σc s₂ ((x₂,Some d)::σ) with
             | Some (_::σ₂) => Some σ₂
             | _ => None
             end
           | _ => None
           end
         end.

    Definition nnrc_imp_eval σc (q:nnrc_imp) : option (option data) :=
      let (s, ret) := q in
      match nnrc_imp_stmt_eval σc s ((ret, None)::nil) with
      | Some ((_,o)::_) => Some o
      | _ => None
      end.

    Definition nnrc_imp_eval_top σc (q:nnrc_imp) :=
      olift id (nnrc_imp_eval (rec_sort σc) q).

  End Evaluation.

  Section Core.
    Program Definition nnrc_imp_core_eval σc (q:nnrc_imp_core)
      := nnrc_imp_eval σc q.

    Program Definition nnrc_imp_core_eval_top σc (q:nnrc_imp_core)
      :=  olift id (nnrc_imp_core_eval (rec_sort σc) q).
    
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

    Lemma nnrc_imp_stmt_eval_env_domain_stack {s σc σ₁ σ₂} :
      nnrc_imp_stmt_eval σc s σ₁ = Some σ₂ -> domain σ₁ = domain σ₂.
    Proof.
      revert σ₁ σ₂.
      nnrc_imp_stmt_cases (induction s) Case; intros σ₁ σ₂ sem; simpl in sem; repeat destr sem.
      - Case "NNRCimpSeq".
        apply some_olift in sem.
        destruct sem as [σ' ? ?].
        transitivity (domain σ'); eauto.
      - Case "NNRCimpAssign".
        invcs sem.
        rewrite domain_update_first; trivial.
      - Case "NNRCimpLet".
        apply some_olift in sem.
        destruct sem as [d eqq1 eqq2 ].
        match_option_in eqq2.
        destruct p; try discriminate.
        invcs eqq2.
        specialize (IHs _ _ eqq).
        simpl in IHs; invcs IHs; trivial.
      - Case "NNRCimpLet".
        invcs sem.
        specialize (IHs _ _ eqq).
        simpl in IHs; invcs IHs; trivial.
      - Case  "NNRCimpFor".
        destruct d; try discriminate.
        clear eqq.
        revert σ₁ σ₂ sem.
        induction l; intros σ₁ σ₂  sem; invcs sem; trivial.
        repeat destr H0.
        specialize (IHl _ _ H0).
        specialize (IHs _ _ eqq).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRCimpIf".
        destruct d; try discriminate.
        destruct b; eauto.
      - Case "NNRCimpEither".
        destruct d; try discriminate;
          repeat destr sem; invcs sem.
        + specialize (IHs1 _ _ eqq0);
            simpl in IHs1; invcs IHs1; trivial.
        + specialize (IHs2 _ _ eqq0);
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

    Lemma nnrc_imp_expr_eval_group_by_unfold σc σ g sl e :
      nnrc_imp_expr_eval σc σ (NNRCimpGroupBy g sl e) = 
      match nnrc_imp_expr_eval σc σ e with
      | Some (dcoll dl) => lift dcoll (group_by_nested_eval_table g sl dl)
      | _ => None
      end.
    Proof.
      reflexivity.
    Qed.

    Global Instance nnrc_imp_expr_eval_proper 
      : Proper (eq ==> lookup_equiv ==> eq ==> eq) nnrc_imp_expr_eval.
    Proof.
      intros ?????????; subst.
      apply nnrc_imp_expr_eval_same.
      apply lookup_equiv_on_lookup_equiv; trivial.
    Qed.

  End props.

End NNRCimpEval.

Arguments nnrc_imp_stmt_eval_env_domain_stack {fruntime h s σc σ₁ σ₂}.
