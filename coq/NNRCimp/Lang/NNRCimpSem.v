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

Section NNRCimpSem.
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

  (* NB: normal variables and (unfrozen) mutable collection variables have *different namespaces*
         Thus, when translating to another language without this distinction, care must be avoided to avoid 
          accidentally introducing shadowing.
   *)

  Local Open Scope nnrc_imp.
  Local Open Scope string.

  Section Denotation.

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
        [ σ ⊢ NNRCimpBinop bop e₁ e₂ ⇓ d ]
          
    | sem_NNRCimpUnop : forall uop e σ d₁ d,
        [ σ ⊢ e ⇓ d₁ ] ->
        nnrc_imp_expr_sem σ e d₁ ->             
        unary_op_eval h uop d₁ = Some d ->     
        [ σ ⊢ NNRCimpUnop uop e ⇓ d ]

    | sem_NNRCimpGroupBy : forall g sl e σ d₁ d₂ ,
        [ σ ⊢ e ⇓ (dcoll d₁) ] ->
        group_by_nested_eval_table g sl d₁ = Some d₂ -> 
        [ σ ⊢ NNRCimpGroupBy g sl e ⇓ (dcoll d₂) ]
          
    where
    "[ σ ⊢ e ⇓ d ]" := (nnrc_imp_expr_sem σ e d) : nnrc_imp
    .
    
    Reserved Notation  "[ σ₁ , ψ₁ ⊢ s₁ ⇓ σ₂ , ψ₂ ]". 
    Reserved Notation "[ σ₁ , ψ₁ ⊢ s ⇓[ v <- dl ] σ₂ , ψ₂ ]".

    Inductive nnrc_imp_stmt_sem : pd_bindings -> mc_bindings -> nnrc_imp_stmt -> pd_bindings -> mc_bindings -> Prop :=
    | sem_NNRCimpSeq s₁ s₂ σ₁ ψ₁ σ₂ ψ₂ σ₃ ψ₃  :
        [ σ₁ , ψ₁ ⊢ s₁ ⇓ σ₂ , ψ₂ ] ->
        [ σ₂ , ψ₂ ⊢ s₂ ⇓ σ₃ , ψ₃ ] ->
        [ σ₁ , ψ₁ ⊢ NNRCimpSeq s₁ s₂ ⇓ σ₃ , ψ₃ ]
          
    | sem_NNRCimpLetMutInitialized v e s σ₁ ψ₁ σ₂ ψ₂ d dd :
        [ σ₁ ⊢ e ⇓ d ] ->
        [ (v,Some d)::σ₁, ψ₁ ⊢ s ⇓ (v,dd)::σ₂ , ψ₂ ] ->
        [ σ₁ , ψ₁ ⊢ NNRCimpLetMut v (Some e) s ⇓ σ₂ , ψ₂ ]
          
    | sem_NNRCimpLetMutUninitialized v s σ₁ ψ₁ σ₂ ψ₂ dd :
        [ (v,None)::σ₁, ψ₁ ⊢ s ⇓ (v,dd)::σ₂ , ψ₂ ] ->
        [ σ₁ , ψ₁ ⊢ NNRCimpLetMut v None s ⇓ σ₂ , ψ₂ ]
          
    | sem_NNRCimpBuildCollFor v s₁ s₂ σ₁ ψ₁ σ₂ ψ₂ σ₃ ψ₃ d dd :
        [ σ₁ , (v,nil)::ψ₁ ⊢ s₁ ⇓ σ₂ , (v,d)::ψ₂ ] ->
        [ (v,Some (dcoll d))::σ₂ , ψ₂ ⊢ s₂ ⇓ (v,dd)::σ₃ , ψ₃ ] ->
        [ σ₁ , ψ₁ ⊢ NNRCimpBuildCollFor v s₁ s₂ ⇓ σ₃ , ψ₃ ]
          
    | sem_NNRCimpPush v e σ ψ mc d :
        lookup string_dec ψ v = Some mc ->
        [ σ ⊢ e ⇓ d ] ->
        [ σ , ψ ⊢ NNRCimpPush v e ⇓ σ , update_first string_dec ψ v (d::mc)]
          
    | sem_NNRCimpAssign v e σ ψ dold d :
        lookup string_dec σ v = Some dold ->
        [ σ ⊢ e ⇓ d ] ->
        [ σ , ψ ⊢ NNRCimpAssign v e ⇓ update_first string_dec σ v (Some d), ψ]
          
    | sem_NNRCimpFor v e s σ₁ ψ₁ σ₂ ψ₂ dl :
        [ σ₁ ⊢ e ⇓ (dcoll dl) ] ->
        [ σ₁ , ψ₁ ⊢ s ⇓[v<-dl] σ₂, ψ₂] ->
        [ σ₁ , ψ₁ ⊢ NNRCimpFor v e s ⇓ σ₂, ψ₂]
          
    | sem_NNRCimpIfTrue e s₁ s₂ σ₁ ψ₁ σ₂ ψ₂ :
        [ σ₁ ⊢ e ⇓ (dbool true) ] ->
        [ σ₁ , ψ₁ ⊢ s₁ ⇓ σ₂, ψ₂] ->
        [ σ₁ , ψ₁ ⊢ NNRCimpIf e s₁ s₂ ⇓ σ₂, ψ₂]
          
    | sem_NNRCimpIfFalse e s₁ s₂ σ₁ ψ₁ σ₂ ψ₂ :
        [ σ₁ ⊢ e ⇓ (dbool false) ] ->
        [ σ₁ , ψ₁ ⊢ s₂ ⇓ σ₂, ψ₂] ->
        [ σ₁ , ψ₁ ⊢ NNRCimpIf e s₁ s₂ ⇓ σ₂, ψ₂]
          
    | sem_NNRCimpEitherLeft e x₁ s₁ x₂ s₂ σ₁ ψ₁ σ₂ ψ₂ d dd :
        [ σ₁ ⊢ e ⇓ (dleft d) ] ->
        [ (x₁,Some d)::σ₁ , ψ₁ ⊢ s₁ ⇓ (x₁,dd)::σ₂, ψ₂] ->
        [ σ₁ , ψ₁ ⊢ NNRCimpEither e x₁ s₁ x₂ s₂ ⇓ σ₂, ψ₂]
          
    | sem_NNRCimpEitherRight e x₁ s₁ x₂ s₂ σ₁ ψ₁ σ₂ ψ₂ d dd :
        [ σ₁ ⊢ e ⇓ (dleft d) ] ->
        [ (x₂,Some d)::σ₁ , ψ₁ ⊢ s₂ ⇓ (x₂,dd)::σ₂, ψ₂] ->
        [ σ₁ , ψ₁ ⊢ NNRCimpEither e x₁ s₁ x₂ s₂ ⇓ σ₂, ψ₂]
          
    with nnrc_imp_stmt_sem_iter: var -> list data -> pd_bindings -> mc_bindings -> nnrc_imp_stmt -> pd_bindings -> mc_bindings -> Prop :=
         | sem_NNRCimpIter_nil v s σ ψ :
             [ σ , ψ ⊢ s ⇓[v<-nil] σ, ψ]
         | sem_NNRCimpIter_cons v s σ₁ ψ₁ σ₂ ψ₂ σ₃ ψ₃ d dl dd:
             [ (v,Some d)::σ₁, ψ₁ ⊢ s ⇓ (v,dd)::σ₂, ψ₂] ->
             [ σ₂ , ψ₂ ⊢ s ⇓[v<-dl] σ₃, ψ₃] ->
             [ σ₁ , ψ₁ ⊢ s ⇓[v<-d::dl] σ₃, ψ₃]
    where
    "[ σ₁ , ψ₁ ⊢ s ⇓ σ₂ , ψ₂ ]" := (nnrc_imp_stmt_sem σ₁ ψ₁ s σ₂ ψ₂ ) : nnrc_imp
                                                                          and "[ σ₁ , ψ₁ ⊢ s ⇓[ v <- dl ] σ₂ , ψ₂ ]" := (nnrc_imp_stmt_sem_iter v dl σ₁ ψ₁ s σ₂ ψ₂ ) : nnrc_imp.

    Notation "[ σ₁ , ψ₁ ⊢ s ⇓ σ₂ , ψ₂ ]" := (nnrc_imp_stmt_sem σ₁ ψ₁ s σ₂ ψ₂ ) : nnrc_imp.
    Notation "[ σ₁ , ψ₁ ⊢ s ⇓[ v <- dl ] σ₂ , ψ₂ ]" := (nnrc_imp_stmt_sem_iter v dl σ₁ ψ₁ s σ₂ ψ₂ ) : nnrc_imp.

    Reserved Notation "[  s ⇓[ ret ] d  ]".

    Inductive nnrc_imp_stmt_sem_top_ret (ret:string) :
      nnrc_imp -> data -> Prop
      :=
      | sem_NNRCimpTopRet s d :
          [ (ret,None)::nil , nil ⊢ s ⇓ (ret, Some d)::nil, nil ] ->
          [   s ⇓[ ret ] d  ]
    where
    "[   s ⇓[ ret ] d  ]" := (nnrc_imp_stmt_sem_top_ret ret s d ) : nnrc_imp.

    Notation "[    s ⇓[ ret ] d  ]" := (nnrc_imp_stmt_sem_top_ret ret s d ) : nnrc_imp.

    Local Open Scope string.
    
  End Denotation.

  Notation "[ σ ⊢ e ⇓ d ]" := (nnrc_imp_expr_sem σ e d) : nnrc_imp.
  Notation "[ σ₁ , ψ₁ ⊢ s ⇓ σ₂ , ψ₂ ]" := (nnrc_imp_stmt_sem σ₁ ψ₁ s σ₂ ψ₂ ) : nnrc_imp.
  Notation "[ σ₁ , ψ₁ ⊢ s ⇓[ v <- dl ] σ₂ , ψ₂ ]" := (nnrc_imp_stmt_sem_iter v dl σ₁ ψ₁ s σ₂ ψ₂ ) : nnrc_imp.


  Section props.
    
    Lemma nnrc_imp_stmt_sem_env_stack s σ₁ ψ₁ σ₂ ψ₂ :
      [ σ₁ , ψ₁ ⊢ s ⇓ σ₂ , ψ₂ ] -> domain σ₁ = domain σ₂.
    Proof.
      revert σ₁ ψ₁ σ₂ ψ₂.
      nnrc_imp_stmt_cases (induction s) Case; intros σ₁ ψ₁ σ₂ ψ₂ sem; invcs sem.
      - Case "NNRCimpSeq".
        transitivity (domain σ₂0); eauto.
      - Case "NNRCimpLetMut".
        specialize (IHs _ _ _ _ H7).
        simpl in IHs; invcs IHs.
        trivial.
      - Case "NNRCimpLetMut".
        specialize (IHs _ _ _ _ H6).
        simpl in IHs; invcs IHs.
        trivial.
      - Case "NNRCimpBuildCollFor".
        specialize (IHs1 _ _ _ _ H6).
        specialize (IHs2 _ _ _ _ H7).
        simpl in IHs2; invcs IHs2.
        congruence.
      - Case "NNRCimpPush".
        trivial.
      - Case "NNRCimpAssign".
        rewrite domain_update_first; trivial.
      - Case  "NNRCimpFor".
        clear H6.
        revert σ₁ ψ₁ σ₂ ψ₂ H7.
        induction dl; intros σ₁ ψ₁ σ₂ ψ₂ sem; invcs sem; trivial.
        specialize (IHdl _ _ _ _ H8).
        specialize (IHs _ _ _ _ H2).
        simpl in IHs; invcs IHs.
        congruence.
      - Case "NNRCimpIf".
        eauto.
      - Case "NNRCimpIf".
        eauto.
      - Case "NNRCimpEither".
        specialize (IHs1 _ _ _ _ H9).
        simpl in IHs1; invcs IHs1; trivial.
      - Case "NNRCimpEither".
        specialize (IHs2 _ _ _ _ H9).
        simpl in IHs2; invcs IHs2; trivial.
    Qed.

    Lemma nnrc_imp_stmt_sem_mcenv_stack s σ₁ ψ₁ σ₂ ψ₂ :
      [ σ₁ , ψ₁ ⊢ s ⇓ σ₂ , ψ₂ ] -> domain ψ₁ = domain ψ₂.
    Proof.
      revert σ₁ ψ₁ σ₂ ψ₂.
      nnrc_imp_stmt_cases (induction s) Case; intros σ₁ ψ₁ σ₂ ψ₂ sem; invcs sem; eauto.
      - Case "NNRCimpSeq".
        transitivity (domain ψ₂0); eauto.
      - Case "NNRCimpBuildCollFor".
        specialize (IHs1 _ _ _ _ H6).
        specialize (IHs2 _ _ _ _ H7).
        simpl in IHs1; invcs IHs1.
        congruence.
      - Case "NNRCimpPush".
        rewrite domain_update_first; trivial.
      - Case  "NNRCimpFor".
        clear H6.
        revert σ₁ ψ₁ σ₂ ψ₂ H7.
        induction dl; intros σ₁ ψ₁ σ₂ ψ₂ sem; invcs sem; trivial.
        specialize (IHdl _ _ _ _ H8).
        specialize (IHs _ _ _ _ H2).
        congruence.
    Qed.

  End props.
  
End NNRCimpSem.
Notation "[ h , σc ; σ ⊢ e ⇓ d ]" := (nnrc_imp_expr_sem h σc σ e d) : nnrc_imp.
Notation "[ h , σc ; σ₁ , ψ₁ ⊢ s ⇓ σ₂ , ψ₂ ]" := (nnrc_imp_stmt_sem h σc σ₁ ψ₁ s σ₂ ψ₂ ) : nnrc_imp.
Notation "[ h , σc ; σ₁ , ψ₁ ⊢ s ⇓[ v <- dl ] σ₂ , ψ₂ ]" := (nnrc_imp_stmt_sem_iter h σc v dl σ₁ ψ₁ s σ₂ ψ₂ ) : nnrc_imp.
