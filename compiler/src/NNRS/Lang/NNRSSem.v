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

Section NNRSSem.
  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  (* NB: normal variables and (unfrozen) mutable collection variables have *different namespaces*
         Thus, when translating to another language without this distinction, care must be avoided to avoid
          accidentally introducing shadowing.
   *)

  Local Open Scope nnrs.
  Local Open Scope string.

  Section Denotation.
    Context (σc:list (string*data)).

    Reserved Notation  "[ σ ⊢ e ⇓ d ]".

    Inductive nnrs_expr_sem : pd_bindings -> nnrs_expr -> data -> Prop :=
    | sem_NNRSGetConstant : forall v σ d,
        edot σc v = Some d ->                 (**r   [Γc(v) = d] *)
        [ σ ⊢ NNRSGetConstant v ⇓ d ]

    | sem_NNRSVar : forall v σ d,
        lookup equiv_dec σ v = Some (Some d) ->              (**r   [Γ(v) = d] *)
        [ σ ⊢ NNRSVar v ⇓ d ]

    | sem_NNRSConst : forall d₁ σ d₂,
        normalize_data h d₁ = d₂ ->                     (**r   [norm(d₁) = d₂] *)
        [ σ ⊢ NNRSConst d₁ ⇓ d₂ ]

    | sem_NNRSBinop : forall bop e₁ e₂ σ d₁ d₂ d,
        [ σ ⊢ e₁ ⇓ d₁ ] ->
        [ σ ⊢ e₂ ⇓ d₂ ] ->
        binary_op_eval h bop d₁ d₂ = Some d ->
        [ σ ⊢ NNRSBinop bop e₁ e₂ ⇓ d ]

    | sem_NNRSUnop : forall uop e σ d₁ d,
        [ σ ⊢ e ⇓ d₁ ] ->
        unary_op_eval h uop d₁ = Some d ->
        [ σ ⊢ NNRSUnop uop e ⇓ d ]

    | sem_NNRSGroupBy : forall g sl e σ d₁ d₂ ,
        [ σ ⊢ e ⇓ (dcoll d₁) ] ->
        group_by_nested_eval_table g sl d₁ = Some d₂ ->
        [ σ ⊢ NNRSGroupBy g sl e ⇓ (dcoll d₂) ]

    where
    "[ σ ⊢ e ⇓ d ]" := (nnrs_expr_sem σ e d) : nnrs
    .

    Reserved Notation  "[ s₁ , σ₁ , ψc₁ , ψd₁ ⇓ σ₂ , ψc₂ , ψd₂ ]".
    Reserved Notation "[ s , σ₁ , ψc₁ , ψd₁ ⇓[ v <- dl ] σ₂ , ψc₂ , ψd₂ ]".

    Inductive nnrs_stmt_sem : nnrs_stmt -> pd_bindings -> mc_bindings -> md_bindings -> pd_bindings -> mc_bindings -> md_bindings -> Prop :=
    | sem_NNRSSeq s₁ s₂ σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ σ₃ ψc₃ ψd₃ :
        [ s₁, σ₁ , ψc₁ , ψd₁ ⇓ σ₂ , ψc₂ , ψd₂ ] ->
        [ s₂, σ₂ , ψc₂ , ψd₂ ⇓ σ₃ , ψc₃, ψd₃ ] ->
        [ NNRSSeq s₁ s₂, σ₁ , ψc₁ , ψd₁ ⇓ σ₃ , ψc₃, ψd₃ ]

    | sem_NNRSLet v e s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ d dd :
        [ σ₁ ⊢ e ⇓ d ] ->
        [ s, (v,Some d)::σ₁, ψc₁ , ψd₁ ⇓ (v,dd)::σ₂ , ψc₂ , ψd₂ ] ->
        [ NNRSLet v e s, σ₁ , ψc₁ , ψd₁ ⇓ σ₂ , ψc₂ , ψd₂ ]

    | sem_NNRSLetMut v s₁ s₂ σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ σ₃ ψc₃ ψd₃ d dd :
        [ s₁, σ₁ , ψc₁ , (v,None)::ψd₁ ⇓ σ₂ , ψc₂ , (v,d)::ψd₂ ] ->
        [ s₂, (v,d)::σ₂ , ψc₂ , ψd₂ ⇓ (v,dd)::σ₃ , ψc₃, ψd₃ ] ->
        [ NNRSLetMut v s₁ s₂, σ₁,ψc₁, ψd₁ ⇓ σ₃ , ψc₃, ψd₃ ]

    | sem_NNRSLetMutColl v s₁ s₂ σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ σ₃ ψc₃ ψd₃ d dd :
        [ s₁, σ₁ , (v,nil)::ψc₁ , ψd₁ ⇓ σ₂ , (v,d)::ψc₂ , ψd₂ ] ->
        [ s₂, (v,Some (dcoll d))::σ₂ , ψc₂ , ψd₂ ⇓ (v,dd)::σ₃ , ψc₃, ψd₃ ] ->
        [ NNRSLetMutColl v s₁ s₂, σ₁,ψc₁, ψd₁ ⇓ σ₃ , ψc₃, ψd₃ ]

    | sem_NNRSAssign v e σ ψc ψd dold d :
        lookup string_dec ψd v = Some dold ->
        [ σ ⊢ e ⇓ d ] ->
        [ NNRSAssign v e, σ , ψc , ψd ⇓ σ, ψc, update_first string_dec ψd v (Some d)]

    | sem_NNRSPush v e σ ψc ψd mc d :
        lookup string_dec ψc v = Some mc ->
        [ σ ⊢ e ⇓ d ] ->
        [ NNRSPush v e, σ , ψc , ψd ⇓ σ , update_first string_dec ψc v (mc++d::nil)%list, ψd]

    | sem_NNRSFor v e s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ dl :
        [ σ₁ ⊢ e ⇓ (dcoll dl) ] ->
        [ s, σ₁ , ψc₁ , ψd₁ ⇓[v<-dl] σ₂, ψc₂ , ψd₂] ->
        [ NNRSFor v e s, σ₁ , ψc₁ , ψd₁ ⇓ σ₂, ψc₂ , ψd₂]

    | sem_NNRSIfTrue e s₁ s₂ σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ :
        [ σ₁ ⊢ e ⇓ (dbool true) ] ->
        [ s₁, σ₁ , ψc₁ , ψd₁ ⇓ σ₂, ψc₂ , ψd₂] ->
        [ NNRSIf e s₁ s₂, σ₁ , ψc₁ , ψd₁ ⇓ σ₂, ψc₂ , ψd₂]

    | sem_NNRSIfFalse e s₁ s₂ σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ :
        [ σ₁ ⊢ e ⇓ (dbool false) ] ->
        [ s₂, σ₁ , ψc₁ , ψd₁ ⇓ σ₂, ψc₂ , ψd₂] ->
        [ NNRSIf e s₁ s₂, σ₁ , ψc₁ , ψd₁ ⇓ σ₂, ψc₂ , ψd₂]

    | sem_NNRSEitherLeft e x₁ s₁ x₂ s₂ σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ d dd :
        [ σ₁ ⊢ e ⇓ (dleft d) ] ->
        [ s₁, (x₁,Some d)::σ₁ , ψc₁ , ψd₁ ⇓ (x₁,dd)::σ₂, ψc₂ , ψd₂] ->
        [ NNRSEither e x₁ s₁ x₂ s₂, σ₁ , ψc₁ , ψd₁ ⇓ σ₂, ψc₂ , ψd₂]

    | sem_NNRSEitherRight e x₁ s₁ x₂ s₂ σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ d dd :
        [ σ₁ ⊢ e ⇓ (dright d) ] ->
        [ s₂, (x₂,Some d)::σ₁ , ψc₁ , ψd₁ ⇓ (x₂,dd)::σ₂, ψc₂ , ψd₂] ->
        [ NNRSEither e x₁ s₁ x₂ s₂, σ₁ , ψc₁ , ψd₁ ⇓ σ₂, ψc₂ , ψd₂]

    with nnrs_stmt_sem_iter: var -> list data -> nnrs_stmt -> pd_bindings -> mc_bindings -> md_bindings -> pd_bindings -> mc_bindings  -> md_bindings -> Prop :=
         | sem_NNRSIter_nil v s σ ψc ψd :
             [ s, σ , ψc, ψd ⇓[v<-nil] σ, ψc, ψd]
         | sem_NNRSIter_cons v s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ σ₃ ψc₃ ψd₃ d dl dd:
             [ s, (v,Some d)::σ₁, ψc₁ , ψd₁ ⇓ (v,dd)::σ₂, ψc₂ , ψd₂] ->
             [ s, σ₂ , ψc₂ , ψd₂ ⇓[v<-dl] σ₃, ψc₃, ψd₃] ->
             [ s, σ₁ , ψc₁ , ψd₁ ⇓[v<-d::dl] σ₃, ψc₃, ψd₃]
    where
    "[ s , σ₁ , ψc₁ , ψd₁ ⇓ σ₂ , ψc₂ , ψd₂ ]" := (nnrs_stmt_sem s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ ) : nnrs
                                                                                                  and "[ s , σ₁ , ψc₁ , ψd₁ ⇓[ v <- dl ] σ₂ , ψc₂ , ψd₂ ]" := (nnrs_stmt_sem_iter v dl s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ ) : nnrs.

    Notation "[ s , σ₁ , ψc₁ , ψd₁ ⇓ σ₂ , ψc₂ , ψd₂ ]" := (nnrs_stmt_sem s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ ) : nnrs.
    Notation "[ s , σ₁ , ψc₁ , ψd₁ ⇓[ v <- dl ] σ₂ , ψc₂ , ψd₂ ]" := (nnrs_stmt_sem_iter v dl s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ ) : nnrs.

  End Denotation.

  Reserved Notation "[ σc ⊢ q ⇓ d  ]".

  Notation "[ σc ; σ ⊢ e ⇓ d ]" := (nnrs_expr_sem σc σ e d) : nnrs.
  Notation "[ σc ⊢ s , σ₁ , ψc₁ , ψd₁ ⇓ σ₂ , ψc₂ , ψd₂ ]" := (nnrs_stmt_sem σc s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ ) : nnrs.
  Notation "[ σc ⊢ s , σ₁ , ψc₁ , ψd₁ ⇓[ v <- dl ] σ₂ , ψc₂ , ψd₂ ]" := (nnrs_stmt_sem_iter σc v dl s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ ) : nnrs.

  Inductive nnrs_sem : bindings -> nnrs -> option data -> Prop
    :=
    | sem_NNRS (σc:bindings) (q: nnrs) o :
        [ σc ⊢ (fst q), nil , nil, ((snd q),None)::nil ⇓ nil, nil, ((snd q), o)::nil ] ->
        [ σc ⊢ q ⇓ o  ]
  where
  "[ σc ⊢ q ⇓ o  ]" := (nnrs_sem σc q o ) : nnrs.

  Definition nnrs_sem_top (σc:bindings) (q:nnrs) (d:data) : Prop
    := [ (rec_sort σc) ⊢ q ⇓ Some d  ].

  Notation "[ σc ⊢ q ⇓ d  ]" := (nnrs_sem σc q d ) : nnrs.

  Section Core.
    Program Definition nnrs_core_sem σc (q:nnrs_core) (d:option data) : Prop
      := nnrs_sem σc q d.

    Notation "[ σc ⊢ q ⇓ᶜ d  ]" := (nnrs_core_sem σc q d ) : nnrs.

    Definition nnrs_core_sem_top (σc:bindings) (q:nnrs_core) (d:data) : Prop
      := [ (rec_sort σc) ⊢ q ⇓ᶜ Some d  ].

  End Core.

  Section props.

    Context (σc:list (string*data)).
    
    Lemma nnrs_stmt_sem_env_stack {s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}:
      [ σc ⊢ s, σ₁ , ψc₁ , ψd₁ ⇓ σ₂ , ψc₂ , ψd₂ ] -> domain σ₁ = domain σ₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrs_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; invcs sem.
      - Case "NNRSSeq".
        transitivity (domain σ₂0); eauto.
      - Case "NNRSLet".
        specialize (IHs _ _ _ _ _ _ H9).
        simpl in IHs; invcs IHs.
        trivial.
      - Case "NNRSLetMut".
        specialize (IHs1 _ _ _ _ _ _ H8).
        specialize (IHs2 _ _ _ _ _ _ H9).
        simpl in IHs2; invcs IHs2.
        congruence.
      - Case "NNRSLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ H8).
        specialize (IHs2 _ _ _ _ _ _ H9).
        simpl in IHs2; invcs IHs2.
        congruence.
      - Case "NNRSAssign".
        trivial.
      - Case "NNRSPush".
        trivial.
      - Case  "NNRSFor".
        clear H8.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ H9.
        induction dl; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; invcs sem; trivial.
        specialize (IHdl _ _ _ _ _ _ H10).
        specialize (IHs _ _ _ _ _ _ H2).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRSIf".
        eauto.
      - Case "NNRSIf".
        eauto.
      - Case "NNRSEither".
        specialize (IHs1 _ _ _ _ _ _ H11).
        simpl in IHs1; invcs IHs1; trivial.
      - Case "NNRSEither".
        specialize (IHs2 _ _ _ _ _ _ H11).
        simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrs_stmt_sem_mcenv_stack {s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}:
      [ σc ⊢ s, σ₁ , ψc₁ , ψd₁ ⇓ σ₂ , ψc₂ , ψd₂ ] -> domain ψc₁ = domain ψc₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrs_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; invcs sem.
      - Case "NNRSSeq".
        transitivity (domain ψc₂0); eauto.
      - Case "NNRSLet".
        specialize (IHs _ _ _ _ _ _ H9).
        simpl in IHs; invcs IHs.
        trivial.
      - Case "NNRSLetMut".
        specialize (IHs1 _ _ _ _ _ _ H8).
        specialize (IHs2 _ _ _ _ _ _ H9).
        simpl in IHs2; invcs IHs2.
        congruence.
      - Case "NNRSLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ H8).
        specialize (IHs2 _ _ _ _ _ _ H9).
        simpl in IHs1; invcs IHs1.
        congruence.
      - Case "NNRSAssign".
        trivial.
      - Case "NNRSPush".
        rewrite domain_update_first; trivial.
      - Case  "NNRSFor".
        clear H8.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ H9.
        induction dl; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; invcs sem; trivial.
        specialize (IHdl _ _ _ _ _ _ H10).
        specialize (IHs _ _ _ _ _ _ H2).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRSIf".
        eauto.
      - Case "NNRSIf".
        eauto.
      - Case "NNRSEither".
        specialize (IHs1 _ _ _ _ _ _ H11).
        simpl in IHs1; invcs IHs1; trivial.
      - Case "NNRSEither".
        specialize (IHs2 _ _ _ _ _ _ H11).
        simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrs_stmt_sem_mdenv_stack {s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}:
      [ σc ⊢ s, σ₁ , ψc₁ , ψd₁ ⇓ σ₂ , ψc₂ , ψd₂ ] -> domain ψd₁ = domain ψd₂.
    Proof.
      revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂.
      nnrs_stmt_cases (induction s) Case; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; invcs sem.
      - Case "NNRSSeq".
        transitivity (domain ψd₂0); eauto.
      - Case "NNRSLet".
        specialize (IHs _ _ _ _ _ _ H9).
        simpl in IHs; invcs IHs.
        trivial.
      - Case "NNRSLetMut".
        specialize (IHs1 _ _ _ _ _ _ H8).
        specialize (IHs2 _ _ _ _ _ _ H9).
        simpl in IHs1; invcs IHs1.
        congruence.
      - Case "NNRSLetMutColl".
        specialize (IHs1 _ _ _ _ _ _ H8).
        specialize (IHs2 _ _ _ _ _ _ H9).
        simpl in IHs1; invcs IHs1.
        congruence.
      - Case "NNRSAssign".
        rewrite domain_update_first; trivial.
      - Case "NNRSPush".
        trivial.
      - Case  "NNRSFor".
        clear H8.
        revert σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ H9.
        induction dl; intros σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ sem; invcs sem; trivial.
        specialize (IHdl _ _ _ _ _ _ H10).
        specialize (IHs _ _ _ _ _ _ H2).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRSIf".
        eauto.
      - Case "NNRSIf".
        eauto.
      - Case "NNRSEither".
        specialize (IHs1 _ _ _ _ _ _ H11).
        simpl in IHs1; invcs IHs1; trivial.
      - Case "NNRSEither".
        specialize (IHs2 _ _ _ _ _ _ H11).
        simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrs_stmt_sem_env_cons_same
          {s v₁ od₁ σ₁ ψc₁ ψd₁ v₂ od₂ σ₂ ψc₂ ψd₂} :
      [ σc ⊢ s, (v₁, od₁) :: σ₁, ψc₁ , ψd₁ ⇓ (v₂, od₂) :: σ₂, ψc₂ , ψd₂] ->
      [ σc ⊢ s, (v₁, od₁) :: σ₁, ψc₁ , ψd₁ ⇓ (v₁, od₂) :: σ₂, ψc₂ , ψd₂].
    Proof.
      intros sem.
      generalize (nnrs_stmt_sem_env_stack sem).
      simpl; intros eqq; invcs eqq.
      trivial.
    Qed.

    Lemma nnrs_stmt_sem_mcenv_cons_same
          {s v₁ od₁ σ₁ ψc₁ ψd₁ v₂ od₂ σ₂ ψc₂ ψd₂} :
      [ σc ⊢ s,  σ₁, (v₁, od₁)::ψc₁ , ψd₁ ⇓ σ₂, (v₂, od₂) :: ψc₂ , ψd₂] ->
      [ σc ⊢ s, σ₁, (v₁, od₁)::ψc₁ , ψd₁ ⇓ σ₂, (v₁, od₂)::ψc₂ , ψd₂].
    Proof.
      intros sem.
      generalize (nnrs_stmt_sem_mcenv_stack sem).
      simpl; intros eqq; invcs eqq.
      trivial.
    Qed.

    Lemma nnrs_stmt_sem_mdenv_cons_same
          {s v₁ od₁ σ₁ ψc₁ ψd₁ v₂ od₂ σ₂ ψc₂ ψd₂} :
      [ σc ⊢ s,  σ₁, ψc₁ , (v₁, od₁)::ψd₁ ⇓ σ₂, ψc₂ , (v₂, od₂) :: ψd₂] ->
      [ σc ⊢ s, σ₁, ψc₁ , (v₁, od₁)::ψd₁ ⇓ σ₂, ψc₂ ,  (v₁, od₂)::ψd₂].
    Proof.
      intros sem.
      generalize (nnrs_stmt_sem_mdenv_stack sem).
      simpl; intros eqq; invcs eqq.
      trivial.
    Qed.

  End props.

End NNRSSem.

Notation "[ h , σc ; σ ⊢ e ⇓ d ]" := (nnrs_expr_sem h σc σ e d) : nnrs.
Notation "[ h , σc ⊢ s , σ₁ , ψc₁ , ψd₁ ⇓ σ₂ , ψc₂ , ψd₂ ]" := (nnrs_stmt_sem h σc s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ ) : nnrs.
Notation "[ h , σc ⊢ s , σ₁ , ψc₁ , ψd₁ ⇓[ v <- dl ] σ₂ , ψc₂ , ψd₂ ]" := (nnrs_stmt_sem_iter h σc v dl s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂ ) : nnrs.
Notation "[ h , σc ⊢ q ⇓ d  ]" := (nnrs_sem h σc q d ) : nnrs.

Notation "[ h , σc ⊢ q ⇓ᶜ d  ]" := (nnrs_core_sem h σc q d ) : nnrs.

Arguments nnrs_stmt_sem_env_stack {fruntime h σc s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.
Arguments nnrs_stmt_sem_mcenv_stack {fruntime h σc s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.
Arguments nnrs_stmt_sem_mdenv_stack {fruntime h σc s σ₁ ψc₁ ψd₁ σ₂ ψc₂ ψd₂}.

Arguments nnrs_stmt_sem_env_cons_same {fruntime h σc s v₁ od₁ σ₁ ψc₁ ψd₁ v₂ od₂ σ₂ ψc₂ ψd₂}.
Arguments nnrs_stmt_sem_mcenv_cons_same {fruntime h σc s v₁ od₁ σ₁ ψc₁ ψd₁ v₂ od₂ σ₂ ψc₂ ψd₂}.
Arguments nnrs_stmt_sem_mdenv_cons_same {fruntime h σc s v₁ od₁ σ₁ ψc₁ ψd₁ v₂ od₂ σ₂ ψc₂ ψd₂}.
