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

Section NNRCimpSem.

  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  Local Open Scope nnrc_imp.
  Local Open Scope string.

  Section Denotation.
    Context (σc:list (string*data)).

    Reserved Notation  "[ σ ⊢ e ⇓ d ]".

    Inductive nnrc_imp_expr_sem : pd_bindings -> nnrc_imp_expr -> data -> Prop :=
    | sem_NNRCimpGetConstant : forall v σ d,
        edot σc v = Some d ->                 (**r   [Γc(v) = d] *)
        [ σ ⊢ NNRCimpGetConstant v ⇓ d ]

    | sem_NNRCimpVar : forall v σ d,
        lookup equiv_dec σ v = Some (Some d) ->              (**r   [Γ(v) = d] *)
        [ σ ⊢ NNRCimpVar v ⇓ d ]

    | sem_NNRCimpConst : forall d₁ σ d₂,
        normalize_data h d₁ = d₂ ->                     (**r   [norm(d₁) = d₂] *)
        [ σ ⊢ NNRCimpConst d₁ ⇓ d₂ ]

    | sem_NNRCimpBinop : forall bop e₁ e₂ σ d₁ d₂ d,
        [ σ ⊢ e₁ ⇓ d₁ ] ->
        [ σ ⊢ e₂ ⇓ d₂ ] ->
        binary_op_eval h bop d₁ d₂ = Some d ->
        [ σ ⊢ NNRCimpBinop bop e₁ e₂ ⇓ d ]

    | sem_NNRCimpUnop : forall uop e σ d₁ d,
        [ σ ⊢ e ⇓ d₁ ] ->
        unary_op_eval h uop d₁ = Some d ->
        [ σ ⊢ NNRCimpUnop uop e ⇓ d ]

    | sem_NNRCimpGroupBy : forall g sl e σ d₁ d₂ ,
        [ σ ⊢ e ⇓ (dcoll d₁) ] ->
        group_by_nested_eval_table g sl d₁ = Some d₂ ->
        [ σ ⊢ NNRCimpGroupBy g sl e ⇓ (dcoll d₂) ]

    where
    "[ σ ⊢ e ⇓ d ]" := (nnrc_imp_expr_sem σ e d) : nnrc_imp
    .

    Reserved Notation  "[ s₁ , σ₁ ⇓ σ₂  ]".
    Reserved Notation "[ s , σ₁ ⇓[ v <- dl ] σ₂ ]".
    
    Inductive nnrc_imp_stmt_sem : nnrc_imp_stmt -> pd_bindings -> pd_bindings -> Prop :=
    | sem_NNRCimpSeq s₁ s₂ σ₁ σ₂ σ₃  :
        [ s₁, σ₁ ⇓ σ₂ ] ->
        [ s₂, σ₂ ⇓ σ₃  ] ->
        [ NNRCimpSeq s₁ s₂, σ₁ ⇓ σ₃ ]

    | sem_NNRCimpAssign v e σ d :
        In v (domain σ) ->
        [ σ ⊢ e ⇓ d ] ->
        [ NNRCimpAssign v e, σ ⇓ update_first string_dec σ v (Some d)]

    | sem_NNRCimpLetNone v s σ₁ σ₂ dd :
        [ s, (v,None)::σ₁ ⇓ (v,dd)::σ₂ ] ->
        [ NNRCimpLet v None s, σ₁ ⇓ σ₂  ]

    | sem_NNRCimpLetSome v e s σ₁ σ₂ d dd :
        [ σ₁ ⊢ e ⇓ d ] ->
        [ s, (v,Some d)::σ₁ ⇓ (v,dd)::σ₂ ] ->
        [ NNRCimpLet v (Some e) s, σ₁  ⇓ σ₂ ]

    | sem_NNRCimpFor v e s σ₁ σ₂ dl :
        [ σ₁ ⊢ e ⇓ (dcoll dl) ] ->
        [ s, σ₁ ⇓[v<-dl] σ₂ ] ->
        [ NNRCimpFor v e s, σ₁ ⇓ σ₂ ]

    | sem_NNRCimpIfTrue e s₁ s₂ σ₁ σ₂ :
        [ σ₁ ⊢ e ⇓ (dbool true) ] ->
        [ s₁, σ₁ ⇓ σ₂ ] ->
        [ NNRCimpIf e s₁ s₂, σ₁ ⇓ σ₂ ]

    | sem_NNRCimpIfFalse e s₁ s₂ σ₁ σ₂ :
        [ σ₁ ⊢ e ⇓ (dbool false) ] ->
        [ s₂, σ₁ ⇓ σ₂ ] ->
        [ NNRCimpIf e s₁ s₂, σ₁ ⇓ σ₂ ]

    | sem_NNRCimpEitherLeft e x₁ s₁ x₂ s₂ σ₁ σ₂ d dd :
        [ σ₁ ⊢ e ⇓ (dleft d) ] ->
        [ s₁, (x₁,Some d)::σ₁ ⇓ (x₁,dd)::σ₂ ] ->
        [ NNRCimpEither e x₁ s₁ x₂ s₂, σ₁ ⇓ σ₂]

    | sem_NNRCimpEitherRight e x₁ s₁ x₂ s₂ σ₁ σ₂ d dd :
        [ σ₁ ⊢ e ⇓ (dright d) ] ->
        [ s₂, (x₂,Some d)::σ₁ ⇓ (x₂,dd)::σ₂ ] ->
        [ NNRCimpEither e x₁ s₁ x₂ s₂, σ₁ ⇓ σ₂ ]

    with nnrc_imp_stmt_sem_iter: var -> list data -> nnrc_imp_stmt -> pd_bindings -> pd_bindings ->  Prop :=
         | sem_NNRCimpIter_nil v s σ :
             [ s, σ ⇓[v<-nil] σ ]
         | sem_NNRCimpIter_cons v s σ₁ σ₂ σ₃ d dl dd:
             [ s, (v,Some d)::σ₁ ⇓ (v,dd)::σ₂] ->
             [ s, σ₂ ⇓[v<-dl] σ₃ ] ->
             [ s, σ₁ ⇓[v<-d::dl] σ₃ ]
    where
    "[ s , σ₁  ⇓ σ₂ ]" := (nnrc_imp_stmt_sem s σ₁ σ₂) : nnrc_imp
                                                         and "[ s , σ₁ ⇓[ v <- dl ] σ₂  ]" := (nnrc_imp_stmt_sem_iter v dl s σ₁ σ₂ ) : nnrc_imp.

    Notation "[ s , σ₁ ⇓ σ₂ ]" := (nnrc_imp_stmt_sem s σ₁ σ₂ ) : nnrc_imp.
    Notation "[ s , σ₁ ⇓[ v <- dl ] σ₂  ]" := (nnrc_imp_stmt_sem_iter v dl s σ₁ σ₂) : nnrc_imp.

  End Denotation.

  Reserved Notation "[ σc ⊢ q ⇓ d  ]".

  Notation "[ σc ; σ ⊢ e ⇓ d ]" := (nnrc_imp_expr_sem σc σ e d) : nnrc_imp.
  Notation "[ σc ⊢ s , σ₁ ⇓ σ₂ ]" := (nnrc_imp_stmt_sem σc s σ₁ σ₂ ) : nnrc_imp.
  Notation "[ σc ⊢ s , σ₁ ⇓[ v <- dl ] σ₂ ]" := (nnrc_imp_stmt_sem_iter σc v dl s σ₁ σ₂) : nnrc_imp.

  Inductive nnrc_imp_sem : bindings -> nnrc_imp -> option data -> Prop
    :=
    | sem_NNRCimp (σc:bindings) (q: nnrc_imp) o :
        [ σc ⊢ (fst q), ((snd q),None)::nil ⇓ ((snd q), o)::nil ] ->
        [ σc ⊢ q ⇓ o  ]
  where
  "[ σc ⊢ q ⇓ o  ]" := (nnrc_imp_sem σc q o ) : nnrc_imp.

  Definition nnrc_imp_sem_top (σc:bindings) (q:nnrc_imp) (d:data) : Prop
    := [ (rec_sort σc) ⊢ q ⇓ Some d  ].

  Notation "[ σc ⊢ q ⇓ d  ]" := (nnrc_imp_sem σc q d ) : nnrc_imp.

  Section Core.
    Program Definition nnrc_imp_core_sem σc (q:nnrc_imp_core) (d:option data) : Prop
      := nnrc_imp_sem σc q d.

    Notation "[ σc ⊢ q ⇓ᶜ d  ]" := (nnrc_imp_core_sem σc q d ) : nnrc_imp.

    Definition nnrc_imp_core_sem_top (σc:bindings) (q:nnrc_imp_core) (d:data) : Prop
      := [ (rec_sort σc) ⊢ q ⇓ᶜ Some d  ].

  End Core.

  Section props.

    Context (σc:list (string*data)).
    
    Lemma nnrc_imp_stmt_sem_env_stack {s σ₁ σ₂ }:
      [ σc ⊢ s, σ₁ ⇓ σ₂  ] -> domain σ₁ = domain σ₂.
    Proof.
      revert σ₁ σ₂.
      nnrc_imp_stmt_cases (induction s) Case; intros σ₁ σ₂ sem; invcs sem.
      - Case "NNRCimpSeq".
        transitivity (domain σ₂0); eauto.
      - Case "NNRCimpAssign".
        rewrite domain_update_first; trivial.
      - Case "NNRCimpLet".
        specialize (IHs _ _ H4).
        simpl in IHs; invcs IHs.
        trivial.
      - Case "NNRCimpLet".
        specialize (IHs _ _ H5).
        simpl in IHs; invcs IHs.
        trivial.
      - Case  "NNRCimpFor".
        clear H4.
        revert σ₁ σ₂ H5.
        induction dl; intros σ₁ σ₂ sem; invcs sem; trivial.
        specialize (IHdl  _ _ H6).
        specialize (IHs _ _ H2).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRCimpIf".
        eauto.
      - Case "NNRCimpIf".
        eauto.
      - Case "NNRCimpEither".
        specialize (IHs1 _ _ H7).
        simpl in IHs1; invcs IHs1; trivial.
      - Case "NNRCimpEither".
        specialize (IHs2 _ _ H7).
        simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrc_imp_stmt_sem_env_cons_same
          {s v₁ od₁ σ₁ v₂ od₂ σ₂ } :
      [ σc ⊢ s, (v₁, od₁) :: σ₁ ⇓ (v₂, od₂) :: σ₂] ->
      [ σc ⊢ s, (v₁, od₁) :: σ₁ ⇓ (v₁, od₂) :: σ₂ ].
    Proof.
      intros sem.
      generalize (nnrc_imp_stmt_sem_env_stack sem).
      simpl; intros eqq; invcs eqq.
      trivial.
    Qed.

  End props.

End NNRCimpSem.

Notation "[ h , σc ; σ ⊢ e ⇓ d ]" := (nnrc_imp_expr_sem h σc σ e d) : nnrc_imp.
Notation "[ h , σc ⊢ s , σ₁ ⇓ σ₂ ]" := (nnrc_imp_stmt_sem h σc s σ₁ σ₂ ) : nnrc_imp.
Notation "[ h , σc ⊢ s , σ₁ ⇓[ v <- dl ] σ₂ ]" := (nnrc_imp_stmt_sem_iter h σc v dl s σ₁ σ₂) : nnrc_imp.
Notation "[ h , σc ⊢ q ⇓ d  ]" := (nnrc_imp_sem h σc q d ) : nnrc_imp.

Notation "[ h , σc ⊢ q ⇓ᶜ d  ]" := (nnrc_imp_core_sem h σc q d ) : nnrc_imp.

Arguments nnrc_imp_stmt_sem_env_stack {fruntime h σc s σ₁ σ₂}.
Arguments nnrc_imp_stmt_sem_env_cons_same {fruntime h σc s v₁ od₁ σ₁ v₂ od₂ σ₂}.
