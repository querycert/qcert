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

Section NNRSimpSem.

  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  Local Open Scope nnrs_imp.
  Local Open Scope string.

  Section Denotation.
    Context (σc:list (string*data)).

    Reserved Notation  "[ σ ⊢ e ⇓ d ]".

    Inductive nnrs_imp_expr_sem : pd_bindings -> nnrs_imp_expr -> data -> Prop :=
    | sem_NNRSimpGetConstant : forall v σ d,
        edot σc v = Some d ->                 (**r   [Γc(v) = d] *)
        [ σ ⊢ NNRSimpGetConstant v ⇓ d ]

    | sem_NNRSimpVar : forall v σ d,
        lookup equiv_dec σ v = Some (Some d) ->              (**r   [Γ(v) = d] *)
        [ σ ⊢ NNRSimpVar v ⇓ d ]

    | sem_NNRSimpConst : forall d₁ σ d₂,
        normalize_data h d₁ = d₂ ->                     (**r   [norm(d₁) = d₂] *)
        [ σ ⊢ NNRSimpConst d₁ ⇓ d₂ ]

    | sem_NNRSimpBinop : forall bop e₁ e₂ σ d₁ d₂ d,
        [ σ ⊢ e₁ ⇓ d₁ ] ->
        [ σ ⊢ e₂ ⇓ d₂ ] ->
        binary_op_eval h bop d₁ d₂ = Some d ->
        [ σ ⊢ NNRSimpBinop bop e₁ e₂ ⇓ d ]

    | sem_NNRSimpUnop : forall uop e σ d₁ d,
        [ σ ⊢ e ⇓ d₁ ] ->
        unary_op_eval h uop d₁ = Some d ->
        [ σ ⊢ NNRSimpUnop uop e ⇓ d ]

    | sem_NNRSimpGroupBy : forall g sl e σ d₁ d₂ ,
        [ σ ⊢ e ⇓ (dcoll d₁) ] ->
        group_by_nested_eval_table g sl d₁ = Some d₂ ->
        [ σ ⊢ NNRSimpGroupBy g sl e ⇓ (dcoll d₂) ]

    where
    "[ σ ⊢ e ⇓ d ]" := (nnrs_imp_expr_sem σ e d) : nnrs_imp
    .

    Reserved Notation  "[ s₁ , σ₁ ⇓ σ₂  ]".
    Reserved Notation "[ s , σ₁ ⇓[ v <- dl ] σ₂ ]".
    
    Inductive nnrs_imp_stmt_sem : nnrs_imp_stmt -> pd_bindings -> pd_bindings -> Prop :=
    | sem_NNRSimpSkip σ  :
        [ NNRSimpSkip, σ ⇓ σ ]

    | sem_NNRSimpSeq s₁ s₂ σ₁ σ₂ σ₃  :
        [ s₁, σ₁ ⇓ σ₂ ] ->
        [ s₂, σ₂ ⇓ σ₃  ] ->
        [ NNRSimpSeq s₁ s₂, σ₁ ⇓ σ₃ ]

    | sem_NNRSimpAssign v e σ d :
        In v (domain σ) ->
        [ σ ⊢ e ⇓ d ] ->
        [ NNRSimpAssign v e, σ ⇓ update_first string_dec σ v (Some d)]

    | sem_NNRSimpLetNone v s σ₁ σ₂ dd :
        [ s, (v,None)::σ₁ ⇓ (v,dd)::σ₂ ] ->
        [ NNRSimpLet v None s, σ₁ ⇓ σ₂  ]

    | sem_NNRSimpLetSome v e s σ₁ σ₂ d dd :
        [ σ₁ ⊢ e ⇓ d ] ->
        [ s, (v,Some d)::σ₁ ⇓ (v,dd)::σ₂ ] ->
        [ NNRSimpLet v (Some e) s, σ₁  ⇓ σ₂ ]

    | sem_NNRSimpFor v e s σ₁ σ₂ dl :
        [ σ₁ ⊢ e ⇓ (dcoll dl) ] ->
        [ s, σ₁ ⇓[v<-dl] σ₂ ] ->
        [ NNRSimpFor v e s, σ₁ ⇓ σ₂ ]

    | sem_NNRSimpIfTrue e s₁ s₂ σ₁ σ₂ :
        [ σ₁ ⊢ e ⇓ (dbool true) ] ->
        [ s₁, σ₁ ⇓ σ₂ ] ->
        [ NNRSimpIf e s₁ s₂, σ₁ ⇓ σ₂ ]

    | sem_NNRSimpIfFalse e s₁ s₂ σ₁ σ₂ :
        [ σ₁ ⊢ e ⇓ (dbool false) ] ->
        [ s₂, σ₁ ⇓ σ₂ ] ->
        [ NNRSimpIf e s₁ s₂, σ₁ ⇓ σ₂ ]

    | sem_NNRSimpEitherLeft e x₁ s₁ x₂ s₂ σ₁ σ₂ d dd :
        [ σ₁ ⊢ e ⇓ (dleft d) ] ->
        [ s₁, (x₁,Some d)::σ₁ ⇓ (x₁,dd)::σ₂ ] ->
        [ NNRSimpEither e x₁ s₁ x₂ s₂, σ₁ ⇓ σ₂]

    | sem_NNRSimpEitherRight e x₁ s₁ x₂ s₂ σ₁ σ₂ d dd :
        [ σ₁ ⊢ e ⇓ (dright d) ] ->
        [ s₂, (x₂,Some d)::σ₁ ⇓ (x₂,dd)::σ₂ ] ->
        [ NNRSimpEither e x₁ s₁ x₂ s₂, σ₁ ⇓ σ₂ ]

    with nnrs_imp_stmt_sem_iter: var -> list data -> nnrs_imp_stmt -> pd_bindings -> pd_bindings ->  Prop :=
         | sem_NNRSimpIter_nil v s σ :
             [ s, σ ⇓[v<-nil] σ ]
         | sem_NNRSimpIter_cons v s σ₁ σ₂ σ₃ d dl dd:
             [ s, (v,Some d)::σ₁ ⇓ (v,dd)::σ₂] ->
             [ s, σ₂ ⇓[v<-dl] σ₃ ] ->
             [ s, σ₁ ⇓[v<-d::dl] σ₃ ]
    where
    "[ s , σ₁  ⇓ σ₂ ]" := (nnrs_imp_stmt_sem s σ₁ σ₂) : nnrs_imp
                                                         and "[ s , σ₁ ⇓[ v <- dl ] σ₂  ]" := (nnrs_imp_stmt_sem_iter v dl s σ₁ σ₂ ) : nnrs_imp.

    Notation "[ s , σ₁ ⇓ σ₂ ]" := (nnrs_imp_stmt_sem s σ₁ σ₂ ) : nnrs_imp.
    Notation "[ s , σ₁ ⇓[ v <- dl ] σ₂  ]" := (nnrs_imp_stmt_sem_iter v dl s σ₁ σ₂) : nnrs_imp.

  End Denotation.

  Reserved Notation "[ σc ⊢ q ⇓ d  ]".

  Notation "[ σc ; σ ⊢ e ⇓ d ]" := (nnrs_imp_expr_sem σc σ e d) : nnrs_imp.
  Notation "[ σc ⊢ s , σ₁ ⇓ σ₂ ]" := (nnrs_imp_stmt_sem σc s σ₁ σ₂ ) : nnrs_imp.
  Notation "[ σc ⊢ s , σ₁ ⇓[ v <- dl ] σ₂ ]" := (nnrs_imp_stmt_sem_iter σc v dl s σ₁ σ₂) : nnrs_imp.

  Inductive nnrs_imp_sem : bindings -> nnrs_imp -> option data -> Prop
    :=
    | sem_NNRSimp (σc:bindings) (q: nnrs_imp) o :
        [ σc ⊢ (fst q), ((snd q),None)::nil ⇓ ((snd q), o)::nil ] ->
        [ σc ⊢ q ⇓ o  ]
  where
  "[ σc ⊢ q ⇓ o  ]" := (nnrs_imp_sem σc q o ) : nnrs_imp.

  Definition nnrs_imp_sem_top (σc:bindings) (q:nnrs_imp) (d:data) : Prop
    := [ (rec_sort σc) ⊢ q ⇓ Some d  ].

  Notation "[ σc ⊢ q ⇓ d  ]" := (nnrs_imp_sem σc q d ) : nnrs_imp.

  Section Core.
    Program Definition nnrs_imp_core_sem σc (q:nnrs_imp_core) (d:option data) : Prop
      := nnrs_imp_sem σc q d.

    Notation "[ σc ⊢ q ⇓ᶜ d  ]" := (nnrs_imp_core_sem σc q d ) : nnrs_imp.

    Definition nnrs_imp_core_sem_top (σc:bindings) (q:nnrs_imp_core) (d:data) : Prop
      := [ (rec_sort σc) ⊢ q ⇓ᶜ Some d  ].

  End Core.

  Section props.

    Context (σc:list (string*data)).
    
    Lemma nnrs_imp_stmt_sem_env_stack {s σ₁ σ₂ }:
      [ σc ⊢ s, σ₁ ⇓ σ₂  ] -> domain σ₁ = domain σ₂.
    Proof.
      revert σ₁ σ₂.
      nnrs_imp_stmt_cases (induction s) Case; intros σ₁ σ₂ sem; invcs sem.
      - Case "NNRSimpSkip".
        trivial.
      - Case "NNRSimpSeq".
        transitivity (domain σ₂0); eauto.
      - Case "NNRSimpAssign".
        rewrite domain_update_first; trivial.
      - Case "NNRSimpLet".
        specialize (IHs _ _ H4).
        simpl in IHs; invcs IHs.
        trivial.
      - Case "NNRSimpLet".
        specialize (IHs _ _ H5).
        simpl in IHs; invcs IHs.
        trivial.
      - Case  "NNRSimpFor".
        clear H4.
        revert σ₁ σ₂ H5.
        induction dl; intros σ₁ σ₂ sem; invcs sem; trivial.
        specialize (IHdl  _ _ H6).
        specialize (IHs _ _ H2).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRSimpIf".
        eauto.
      - Case "NNRSimpIf".
        eauto.
      - Case "NNRSimpEither".
        specialize (IHs1 _ _ H7).
        simpl in IHs1; invcs IHs1; trivial.
      - Case "NNRSimpEither".
        specialize (IHs2 _ _ H7).
        simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrs_imp_stmt_sem_env_cons_same
          {s v₁ od₁ σ₁ v₂ od₂ σ₂ } :
      [ σc ⊢ s, (v₁, od₁) :: σ₁ ⇓ (v₂, od₂) :: σ₂] ->
      [ σc ⊢ s, (v₁, od₁) :: σ₁ ⇓ (v₁, od₂) :: σ₂ ].
    Proof.
      intros sem.
      generalize (nnrs_imp_stmt_sem_env_stack sem).
      simpl; intros eqq; invcs eqq.
      trivial.
    Qed.

  End props.

End NNRSimpSem.

Notation "[ h , σc ; σ ⊢ e ⇓ d ]" := (nnrs_imp_expr_sem h σc σ e d) : nnrs_imp.
Notation "[ h , σc ⊢ s , σ₁ ⇓ σ₂ ]" := (nnrs_imp_stmt_sem h σc s σ₁ σ₂ ) : nnrs_imp.
Notation "[ h , σc ⊢ s , σ₁ ⇓[ v <- dl ] σ₂ ]" := (nnrs_imp_stmt_sem_iter h σc v dl s σ₁ σ₂) : nnrs_imp.
Notation "[ h , σc ⊢ q ⇓ d  ]" := (nnrs_imp_sem h σc q d ) : nnrs_imp.

Notation "[ h , σc ⊢ q ⇓ᶜ d  ]" := (nnrs_imp_core_sem h σc q d ) : nnrs_imp.

Arguments nnrs_imp_stmt_sem_env_stack {fruntime h σc s σ₁ σ₂}.
Arguments nnrs_imp_stmt_sem_env_cons_same {fruntime h σc s v₁ od₁ σ₁ v₂ od₂ σ₂}.
