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

(** cNNRC is the core named nested relational calculus. It serves as
the foundations for NNRC, an intermediate language that we use to
facilitate code generation to non-functional targets. *)

(** cNNRC is a small pure language without functions. Expressions in
cNNRC are evaluated within a global and a local environment. *)

(** Summary:
- Language: cNNRC (Core Named Nested Relational Calculus)
- Based on: "Polymorphic type inference for the named nested
  relational calculus." Jan Van den Bussche, and Stijn
  Vansummeren. ACM Transactions on Computational Logic (TOCL) 9.1
  (2007): 3.
- translating to cNNRC: NRA, cNRAEnv, NNRC
- translating from cNNRC: NNRC, CAMP *)

(** Compared to the version proposed by Van den Bussche and Vansummerren:
- We add a notion of global variables, distinct from local variables
- We add a let expression: [let x := e1 in e2]
- Conditional expressions allow arbitrary boolean conditions, not just equality, so
instead of: [e1 = e2 ? e3 : e4], we have: [e1 ? e2 : e3]
- We add a case expression for either values: [either e left v₁ : e₁ | right v₂ : e₂]
*)

Require Import String.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonRuntime.

Section cNNRC.
  Context {fruntime:foreign_runtime}.
  
  (** * Abstract Syntax *)

  Section Syntax.
  
    (** Note that the AST is shared between cNNRC and NNRC. However,
        semantics for extended operators are not defined for core
        NNRC. *)

    Inductive nnrc :=
    | NNRCGetConstant : var -> nnrc                           (**r global variable lookup ([$$v]) *)
    | NNRCVar : var -> nnrc                                   (**r local variable lookup ([$v])*)
    | NNRCConst : data -> nnrc                                (**r constant data ([d]) *)
    | NNRCBinop : binary_op -> nnrc -> nnrc -> nnrc           (**r binary operator ([e₁ ⊠ e₂]) *)
    | NNRCUnop : unary_op -> nnrc -> nnrc                     (**r unary operator ([⊞ e]) *)
    | NNRCLet : var -> nnrc -> nnrc -> nnrc                   (**r let expression ([let $v := e₁ in e₂]) *)
    | NNRCFor : var -> nnrc -> nnrc -> nnrc                   (**r for loop ([{ e₂ | $v in e₁ }]) *)
    | NNRCIf : nnrc -> nnrc -> nnrc -> nnrc                   (**r conditional ([e₁ ? e₂ : e₃]) *)
    | NNRCEither : nnrc -> var -> nnrc -> var -> nnrc -> nnrc (**r case expression ([either e left $v₁ : e₁ | right $v₂ : e₂]) *)
    | NNRCGroupBy : string -> list string -> nnrc -> nnrc.    (**r group by expression ([e groupby g fields]) -- only in full NNRC *)

    (** The [nnrcIsCore] predicate defines what fragment is part of
        this abstract syntax is in the core named nested relational
        calculus and which part is not. *)
  
    Fixpoint nnrcIsCore (e:nnrc) : Prop :=
      match e with
      | NNRCGetConstant _ => True
      | NNRCVar _ => True
      | NNRCConst _ => True
      | NNRCBinop _ e1 e2 => (nnrcIsCore e1) /\ (nnrcIsCore e2)
      | NNRCUnop _ e1 => (nnrcIsCore e1)
      | NNRCLet _ e1 e2 => (nnrcIsCore e1) /\ (nnrcIsCore e2)
      | NNRCFor _ e1 e2 => (nnrcIsCore e1) /\ (nnrcIsCore e2)
      | NNRCIf e1 e2 e3 => (nnrcIsCore e1) /\ (nnrcIsCore e2) /\ (nnrcIsCore e3)
      | NNRCEither e1 _ e2 _ e3 => (nnrcIsCore e1) /\ (nnrcIsCore e2) /\ (nnrcIsCore e3)
      | NNRCGroupBy _ _ _ => False
      end.

    (** cNNRC is defined as the expressions in that abstract syntax
        for which the [nnrcIsCore] predicate holds. *)
  
    Definition nnrc_core : Set := {e:nnrc | nnrcIsCore e}.

    Definition nnrc_core_to_nnrc (e:nnrc_core) : nnrc :=
      proj1_sig e.

    Definition lift_nnrc_core {A} (f:nnrc -> A) (e:nnrc_core) : A :=
      f (proj1_sig e).
    
    Tactic Notation "nnrc_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "NNRCGetConstants"%string
      | Case_aux c "NNRCVar"%string
      | Case_aux c "NNRCConst"%string
      | Case_aux c "NNRCBinop"%string
      | Case_aux c "NNRCUnop"%string
      | Case_aux c "NNRCLet"%string
      | Case_aux c "NNRCFor"%string
      | Case_aux c "NNRCIf"%string
      | Case_aux c "NNRCEither"%string
      | Case_aux c "NNRCGroupBy"%string].

    (** Equality between two NNRC expressions is decidable. *)
  
    Global Instance nnrc_eqdec : EqDec nnrc eq.
    Proof.
      change (forall x y : nnrc,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply binary_op_eqdec | apply unary_op_eqdec
                   | apply data_eqdec | apply string_eqdec].
      - decide equality; apply string_dec.
    Defined.

    Lemma nnrcIsCore_ext (e:nnrc) (pf1 pf2:nnrcIsCore e) : pf1 = pf2.
    Proof.
      induction e; simpl in *;
        try (destruct pf1; destruct pf2; trivial);
        try f_equal; auto.
      - destruct a; destruct a0.
        f_equal; auto.
      - destruct a; destruct a0.
        f_equal; auto.
    Qed.

    Lemma nnrc_core_ext e (pf1 pf2:nnrcIsCore e) : 
      exist _ e pf1 = exist _ e pf2.
    Proof.
      f_equal; apply nnrcIsCore_ext.
    Qed.

    Lemma nnrc_core_fequal (e1 e2:nnrc_core) :
      proj1_sig e1 = proj1_sig e2 -> e1 = e2.
    Proof.
      destruct e1; destruct e2; simpl; intros eqq.
      destruct eqq.
      apply nnrc_core_ext.
    Qed.

    Global Instance nnrc_core_eqdec : EqDec nnrc_core eq.
    Proof.
      intros x y.
      destruct x as [x xpf]; destruct y as [y ypf].
      destruct (x == y).
      - left. apply nnrc_core_fequal; simpl; trivial.
      - right. inversion 1; congruence.
    Defined.

  End Syntax.
  
  (** * Semantics *)

  (** For cNNRC, we provide two kinds of semantics: a denotational
  semantics, and an evaluation semantics. Both are shown to be
  equivalent. The denotational semantics is used for documentation
  purposes, as most of the rest of the code relies on evaluation as
  the primary semantics. *)
  
  Section Semantics.
    (** Part of the context is fixed for the rest of the development:
- [h] is the brand relation
- [constant_env] is the global environment *)

    Context (h:brand_relation_t).
    Context (constant_env:list (string*data)).

    (** ** Denotational Semantics *)

    (** The semantics is defined using the main judgment [Γc ; Γ ⊢〚e
    〛⇓ d] ([nnrc_core_sem]) where [Γc] is the global environment, [Γ]
    is the local environment, [e] the cNNRC expression and [d] the
    resulting value. *)
    
    (** Conditionals and matching expressions only evaluate one of
    their branches. The auxiliary judgment [Γc ; Γ ; v ; c₁ ⊢ 〚e〛φ ⇓ c₂]
    ([nnrc_core_sem_for]) is used in the definition of [for]
    expressions. *)
    
    Section Denotation.
      Inductive nnrc_core_sem: bindings -> nnrc -> data -> Prop :=
      | sem_cNNRCGetConstant : forall env v d,
          edot constant_env v = Some d ->                 (**r   [Γc(v) = d] *)
          nnrc_core_sem env (NNRCGetConstant v) d         (**r ⇒ [Γc ; Γ ⊢〚$$v〛⇓ d] *)
      | sem_cNNRCVar : forall env v d,
          lookup equiv_dec env v = Some d ->              (**r   [Γ(v) = d] *)
          nnrc_core_sem env (NNRCVar v) d                 (**r ⇒ [Γc ; Γ ⊢〚$v〛⇓ d] *)
      | sem_cNNRCConst : forall env d1 d2,
          normalize_data h d1 = d2 ->                     (**r   [norm(d₁) = d₂] *)
          nnrc_core_sem env (NNRCConst d1) d2             (**r ⇒ [Γc ; Γ ⊢〚d₁〛⇓ d₂] *)
      | sem_cNNRCBinop : forall bop env e1 e2 d1 d2 d3,
          nnrc_core_sem env e1 d1 ->                      (**r   [Γc ; Γ ⊢〚e₁〛⇓ d₁] *)
          nnrc_core_sem env e2 d2 ->                      (**r ∧ [Γc ; Γ ⊢〚e₂〛⇓ d₂] *)
          binary_op_eval h bop d1 d2 = Some d3 ->         (**r ∧ [d₁ ⊠ d₂ = d₃] *)
          nnrc_core_sem env (NNRCBinop bop e1 e2) d3      (**r ⇒ [Γc ; Γ ⊢〚e₁ ⊠ e₂〛⇓ d₃] *)
      | sem_cNNRCUnop : forall uop env e d1 d2,
          nnrc_core_sem env e d1 ->                       (**r   [Γc ; Γ ⊢〚e〛⇓ d₁] *)
          unary_op_eval h uop d1 = Some d2 ->             (**r ∧ [⊞ d₁ = d₂] *)
          nnrc_core_sem env (NNRCUnop uop e) d2           (**r ⇒ [Γc ; Γ ⊢〚⊞ e〛⇓ d₂] *)
      | sem_cNNRCLet : forall env e1 v e2 d1 d2,
          nnrc_core_sem env e1 d1 ->                      (**r   [Γc ; Γ ⊢〚e₁〛⇓ d₁] *)
          nnrc_core_sem ((v,d1)::env) e2 d2 ->            (**r ∧ [Γc ; (v,d₁),Γ ⊢〚e₂〛⇓ d₂] *)
          nnrc_core_sem env (NNRCLet v e1 e2) d2          (**r ⇒ [Γc ; Γ ⊢〚let 4v := e₁ in e₂〛⇓ d₂] *)
      | sem_cNNRCFor : forall env e1 v e2 c1 c2,
          nnrc_core_sem env e1 (dcoll c1) ->              (**r   [Γc ; Γ ⊢〚e₁〛= {c₁}] *)
          nnrc_core_sem_for v env e2 c1 c2 ->             (**r ∧ [Γc ; Γ ; v ; {c₁} ⊢〚e₂〛φ ⇓ {c₂}] *)
          nnrc_core_sem env (NNRCFor v e1 e2) (dcoll c2)  (**r ⇒ [Γc ; Γ ⊢ 〚{ e₂ | $v in e₁ }〛⇓ {c₂}] *)
      | sem_cNNRCIf_true : forall env e1 e2 e3 d,
          nnrc_core_sem env e1 (dbool true) ->            (**r   [Γc ; Γ ⊢〚e₁〛⇓ true] *)
          nnrc_core_sem env e2 d ->                       (**r ∧ [Γc ; Γ ⊢〚e₂〛⇓ d] *)
          nnrc_core_sem env (NNRCIf e1 e2 e3) d           (**r ⇒ [Γc ; Γ ⊢〚e₁ ? e₂ : e₃〛⇓ d] *)
      | sem_cNNRCIf_false : forall env e1 e2 e3 d,
          nnrc_core_sem env e1 (dbool false) ->           (**r   [Γc ; Γ ⊢〚e₁〛⇓ false] *)
          nnrc_core_sem env e3 d ->                       (**r ∧ [Γc ; Γ ⊢〚e₃〛⇓ d] *)
          nnrc_core_sem env (NNRCIf e1 e2 e3) d           (**r ⇒ [Γc ; Γ ⊢〚e₁ ? e₂ : e₃〛⇓ d] *)
      | sem_cNNRCEither_left : forall env e v1 e1 v2 e2 d d1,
          nnrc_core_sem env e (dleft d) ->                (**r   [Γc ; Γ ⊢〚e〛⇓ left d] *)
          nnrc_core_sem ((v1,d)::env) e1 d1 ->            (**r ∧ [Γc ; (v₁,d),Γ ⊢〚e₁〛⇓ d₁] *)
          nnrc_core_sem env (NNRCEither e v1 e1 v2 e2) d1 (**r ⇒ [Γc ; Γ ⊢〚either e left $v₁ : e₁ | right $v₂ : e₂〛⇓ d₁] *)
      | sem_cNNRCEither_right : forall env e v1 e1 v2 e2 d d2,
          nnrc_core_sem env e (dright d) ->               (**r   [Γc ; Γ ⊢〚e〛⇓ right d] *)
          nnrc_core_sem ((v2,d)::env) e2 d2 ->            (**r ∧ [Γc ; (v₂,d),Γ ⊢〚e₂〛⇓ d₂] *)
          nnrc_core_sem env (NNRCEither e v1 e1 v2 e2) d2 (**r ⇒ [Γc ; Γ ⊢〚either e left $v₁ : e₁ | right $v₂ : e₂〛⇓ d₂] *)
      with nnrc_core_sem_for: var -> bindings -> nnrc -> list data -> list data -> Prop :=
      | sem_cNNRCFor_empty v : forall env e,
          nnrc_core_sem_for v env e nil nil            (**r   [Γc ; Γ ; v ; {} ⊢〚e〛φ ⇓ {}] *)
      | sem_cNNRCFor_cons v : forall env e d1 c1 d2 c2,
          nnrc_core_sem ((v,d1)::env) e d2 ->          (**r   [Γc ; (v,d₁),Γ ⊢〚e₂〛⇓ d₂]  *)
          nnrc_core_sem_for v env e c1 c2 ->           (**r ∧ [Γc ; Γ ; v ; {c₁} ⊢〚e〛φ ⇓ {c₂}] *)
          nnrc_core_sem_for v env e (d1::c1) (d2::c2). (**r ⇒ [Γc ; Γ ; v ; {d₁::c₁} ⊢〚e〛φ ⇓ {d₂::c₂}] *)

    End Denotation.

    (** ** Evaluation Semantics *)
    Section Evaluation.

      (** Evaluation takes a cNNRC expression and an environment. It
          returns an optional value. When [None] is returned, it
          denotes an error. An error is always propagated. *)

      Fixpoint nnrc_core_eval (env:bindings) (e:nnrc) : option data :=
        match e with
        | NNRCGetConstant v =>
          edot constant_env v
        | NNRCVar v =>
          lookup equiv_dec env v
        | NNRCConst d =>
          Some (normalize_data h d)
        | NNRCBinop bop e1 e2 =>
          olift2 (fun d1 d2 => binary_op_eval h bop d1 d2)
                 (nnrc_core_eval env e1)
                 (nnrc_core_eval env e2)
        | NNRCUnop uop e =>
          olift (fun d1 => unary_op_eval h uop d1)
                (nnrc_core_eval env e)
        | NNRCLet v e1 e2 =>
          match nnrc_core_eval env e1 with
          | Some d1 => nnrc_core_eval ((v,d1)::env) e2
          | _ => None
          end
        | NNRCFor v e1 e2 =>
          match nnrc_core_eval env e1 with
          | Some (dcoll c1) =>
            let for_fun :=
                fun d1 => nnrc_core_eval ((v,d1)::env) e2
            in
            lift dcoll (lift_map for_fun c1)
          | _ => None
          end
        | NNRCIf e1 e2 e3 =>
          let cond_fun :=
              fun d =>
                match d with
                | dbool true =>
                  nnrc_core_eval env e2
                | dbool false =>
                  nnrc_core_eval env e3
                | _ => None
                end
          in olift cond_fun (nnrc_core_eval env e1)
        | NNRCEither e v1 e1 v2 e2 =>
          match nnrc_core_eval env e with
          | Some (dleft d) =>
            nnrc_core_eval ((v1,d)::env) e1
          | Some (dright d) =>
            nnrc_core_eval ((v2,d)::env) e2
          | _ => None
          end
        | NNRCGroupBy _ _ _ => None (**r Evaluation for GroupBy always fails for cNNRC *)
        end.

      (** cNNRC evaluation is only sensitive to the environment modulo
      lookup. *)
      Global Instance nnrc_core_eval_lookup_equiv_prop :
        Proper (lookup_equiv ==> eq ==> eq) nnrc_core_eval.
      Proof.
        unfold Proper, respectful, lookup_equiv; intros; subst.
        rename y0 into e.
        revert x y H.
        induction e; simpl; intros; trivial;
          try rewrite (IHe1 _ _ H); try rewrite (IHe2 _ _ H);
            try rewrite (IHe _ _ H); trivial.
        - match_destr.
          apply IHe2; intros.
          simpl; match_destr.
        - match_destr.
          destruct d; simpl; trivial.
          f_equal.
          apply lift_map_ext; intros.
          apply IHe2; intros.
          simpl; match_destr.
        - unfold olift.
          match_destr.
          destruct d; trivial.
          destruct b; eauto.
        - match_destr.
          destruct d; trivial.
          + apply IHe2; intros.
            simpl; match_destr.
          + apply IHe3; intros.
            simpl; match_destr.
      Qed.

    End Evaluation.

    (** * Correctness of evaluation *)
    
    (** The evaluation and denotational semantics are equivalent. *)
    
    Section EvaluationCorrect.
      (** Auxiliary lemma on [for] loops used in the correctness theorem *)

      Lemma nnrc_core_for_eval_correct v env e l1 l2:
        (lift_map (fun d1 : data => nnrc_core_eval ((v, d1) :: env) e) l1 = Some l2) ->
        (forall (env : bindings) (d : data),
            nnrc_core_eval env e = Some d -> nnrc_core_sem env e d) ->
        nnrc_core_sem_for v env e l1 l2.
      Proof.
        revert l2; induction l1; simpl; intros.
        - inversion H; subst; econstructor.
        - case_eq (nnrc_core_eval ((v, a) :: env) e); intros;
            rewrite H1 in *.
          + unfold lift in H.
            case_eq (lift_map (fun d1 : data => nnrc_core_eval ((v, d1) :: env) e) l1);
              intros; rewrite H2 in *; clear H2; [|congruence].
            inversion H; subst; clear H.
            specialize (IHl1 l eq_refl H0).
            econstructor.
            apply H0; auto.
            auto.
          + congruence.
      Qed.

      (** Evaluation is correct wrt. the cNNRC semantics. *)

      Lemma nnrc_core_eval_correct : forall e env d,
          nnrc_core_eval env e = Some d ->
          nnrc_core_sem env e d.
      Proof.
        induction e; simpl; intros.
        - constructor; trivial.
        - constructor; trivial.
        - constructor; inversion H; trivial.
        - specialize (IHe1 env); specialize (IHe2 env).
          case_eq (nnrc_core_eval env e1); intros; rewrite H0 in *.
          + case_eq (nnrc_core_eval env e2); intros; rewrite H1 in *.
            * specialize (IHe1 d0 eq_refl); specialize (IHe2 d1 eq_refl);
                econstructor; eauto.
            * simpl in H; congruence.
          + simpl in H; congruence.
        - specialize (IHe env).
          case_eq (nnrc_core_eval env e); intros; rewrite H0 in *.
          + specialize (IHe d0 eq_refl); econstructor; eauto.
          + simpl in H; congruence.
        - specialize (IHe1 env).
          case_eq (nnrc_core_eval env e1); intros; rewrite H0 in *.
          + case_eq (nnrc_core_eval ((v,d0)::env) e2); intros.
            * specialize (IHe2 ((v,d0)::env)).
              rewrite H1 in *; inversion H; subst; clear H.
              specialize (IHe2 d eq_refl);
                econstructor; eauto.
            * simpl in H; congruence.
          + simpl in H; congruence.
        - specialize (IHe1 env).
          case_eq (nnrc_core_eval env e1); intros; rewrite H0 in *.
          + destruct d0; simpl in H; try congruence.
            specialize (IHe1 (dcoll l) eq_refl).
            unfold lift in H.
            case_eq (lift_map (fun d1 : data => nnrc_core_eval ((v, d1) :: env) e2) l);
              intros; rewrite H1 in H; try congruence.
            inversion H; subst; clear H.
            econstructor; eauto.
            apply nnrc_core_for_eval_correct; eauto.
          + simpl in H; congruence.
        - specialize (IHe1 env); specialize (IHe2 env); specialize (IHe3 env).
          case_eq (nnrc_core_eval env e1); intros; rewrite H0 in *; simpl in H.
          destruct d0; simpl in H; try congruence.
          destruct b.
          (* condition true *)
          + case_eq (nnrc_core_eval env e2); intros; rewrite H1 in *.
            * specialize (IHe1 (dbool true) eq_refl); specialize (IHe2 d0 eq_refl);
                inversion H; subst; eapply sem_cNNRCIf_true; eauto.
            * simpl in H; congruence.
          (* condition false *)
          + case_eq (nnrc_core_eval env e3); intros; rewrite H1 in *.
            * specialize (IHe1 (dbool false) eq_refl); specialize (IHe3 d0 eq_refl);
                inversion H; subst; eapply sem_cNNRCIf_false; eauto.
            * simpl in H; congruence.
          + simpl in H; congruence.
        - specialize (IHe1 env).
          case_eq (nnrc_core_eval env e1); intros; rewrite H0 in *; simpl in H.
          destruct d0; simpl in H; try congruence.
          (* left case *)
          + specialize (IHe2 ((v,d0)::env)).
            * specialize (IHe1 (dleft d0) eq_refl); specialize (IHe2 d H);
                inversion H; subst; eapply sem_cNNRCEither_left; eauto.
          (* right case *)
          + specialize (IHe3 ((v0,d0)::env)).
            * specialize (IHe1 (dright d0) eq_refl); specialize (IHe3 d H);
                inversion H; subst; eapply sem_cNNRCEither_right; eauto.
          + simpl in H; congruence.
        - congruence.
      Qed.

      (** Auxiliary lemma on [for] loops used in the completeness theorem *)

      Lemma nnrc_core_for_eval_complete e v env c1 c2:
        (forall (env : bindings) (d : data),
            nnrc_core_sem env e d -> nnrc_core_eval env e = Some d) ->
        (nnrc_core_sem_for v env e c1 c2) ->
        lift dcoll (lift_map (fun d1 : data => nnrc_core_eval ((v, d1) :: env) e) c1) =
        Some (dcoll c2).
      Proof.
        intro Hcomp.
        revert c2; induction c1; intros; simpl in *.
        - inversion H; auto.
        - inversion H; subst.
          rewrite (Hcomp ((v,a)::env) d2); auto.
          unfold lift in *.
          specialize (IHc1 c3 H7).
          case_eq (lift_map (fun d1 : data => nnrc_core_eval ((v, d1) :: env) e) c1); intros;
            rewrite H0 in *; [|congruence].
          inversion IHc1; subst; auto.
      Qed.

      (** Evaluation is complete wrt. the cNNRC semantics. *)

      Lemma nnrc_core_eval_complete : forall e env d,
          nnrc_core_sem env e d ->
          nnrc_core_eval env e = Some d.
      Proof.
        induction e; intros.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl; auto.
        - inversion H; subst; simpl.
          rewrite (IHe1 env d1 H4);
            rewrite (IHe2 env d2 H6); simpl; auto.
        - inversion H; subst; simpl.
          rewrite (IHe env d1 H3); simpl; auto.
        - inversion H; subst; simpl.
          rewrite (IHe1 env d1 H5);
            rewrite (IHe2 ((v,d1)::env) d H6); simpl; auto.
        - inversion H; subst; simpl.
          rewrite (IHe1 env (dcoll c1) H5).
          apply nnrc_core_for_eval_complete; auto.
        - inversion H; subst; simpl; auto.
          (* condition true *)
          + rewrite (IHe1 env (dbool true) H5); simpl; auto.
          (* condition false *)
          + rewrite (IHe1 env (dbool false) H5); simpl; auto.
        - inversion H; subst; simpl; auto.
          (* left case *)
          + rewrite (IHe1 env (dleft d0) H7); simpl; auto.
          (* right case *)
          + rewrite (IHe1 env (dright d0) H7); simpl; auto.
        - inversion H.
      Qed.

      (** Main equivalence theorem. *)
      
      Theorem nnrc_core_eval_correct_and_complete : forall e env d,
          nnrc_core_eval env e = Some d <-> nnrc_core_sem env e d.
      Proof.
        split.
        apply nnrc_core_eval_correct.
        apply nnrc_core_eval_complete.
      Qed.

    End EvaluationCorrect.

  End Semantics.

  (** * Toplevel *)

  (** The Top-level evaluation function is used externally by the
      Q*cert compiler. It takes a cNNRC expression and an global
      environment as input. *)

  Section Top.
    Context (h:brand_relation_t).

    (** Top-level semantics is always with an initial empty environment *)
    Inductive nnrc_core_sem_top : nnrc_core -> bindings -> data -> Prop :=
    | sem_NNRCTop: forall e cenv d,
        nnrc_core_sem h cenv nil (proj1_sig e) d ->
        nnrc_core_sem_top e cenv d.

    Definition nnrc_core_eval_top (q:nnrc_core) (cenv:bindings) : option data :=
      lift_nnrc_core (nnrc_core_eval h (rec_sort cenv) nil) q.

    (** If top-level NNRC eval returns a value, this value is
        consistent with the semantics *)
    Theorem nnrc_core_eval_top_correct:
      forall cenv,
      rec_sort cenv = cenv -> (* This assumption should be part of constant_env *)
      forall (q:nnrc_core) (d:data),
        nnrc_core_eval_top q cenv = Some d ->
        nnrc_core_sem_top q cenv d.
    Proof.
      intros cenv HconstNorm q d.
      destruct q; simpl in *.
      econstructor; simpl.
      unfold nnrc_core_eval_top in H.
      unfold lift_nnrc_core in H; simpl in H.
      apply nnrc_core_eval_correct.
      rewrite HconstNorm in H.
      assumption.
    Qed.

  End Top.

End cNNRC.

(** * Notations *)

(* begin hide *)
Notation "‵‵ c" := (NNRCConst (dconst c))  (at level 0) : nnrc_scope.                           (* ‵ = \backprime *)
Notation "‵ c" := (NNRCConst c)  (at level 0) : nnrc_scope.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (NNRCConst (dcoll nil))  (at level 0) : nnrc_scope.                         (* ‵ = \backprime *)
Notation "‵[||]" := (NNRCConst (drec nil)) (at level 50) : nnrc_scope.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (NNRCBinop OpAnd r1 r2) (right associativity, at level 65): nnrc_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (NNRCBinop OpOr r1 r2) (right associativity, at level 70): nnrc_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (NNRCBinop OpEqual r1 r2) (right associativity, at level 70): nnrc_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (NNRCBinop OpLe r1 r2) (no associativity, at level 70): nnrc_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (NNRCBinop OpBagUnion r1 r2) (right associativity, at level 70): nnrc_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (NNRCBinop OpBagDiff r1 r2) (right associativity, at level 70): nnrc_scope.  (* − = \minus *)
Notation "r1 ⋂min r2" := (NNRCBinop OpBagMin r1 r2) (right associativity, at level 70): nnrc_scope. (* ♯ = \sharp *)
Notation "r1 ⋃max r2" := (NNRCBinop OpBagMax r1 r2) (right associativity, at level 70): nnrc_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((NNRCBinop OpRecConcat) p r) (at level 70) : nnrc_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((NNRCBinop OpRecMerge) p r) (at level 70) : nnrc_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (NNRCUnop OpNeg r1) (right associativity, at level 70): nnrc_scope.        (* ¬ = \neg *)
Notation "ε( r1 )" := (NNRCUnop OpDistinct r1) (right associativity, at level 70): nnrc_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (NNRCUnop OpCount r1) (right associativity, at level 70): nnrc_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (NNRCUnop OpFlatten d) (at level 50) : nnrc_scope.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((NNRCUnop OpBag) d)  (at level 50) : nnrc_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((NNRCUnop (OpRec s)) r) (at level 50) : nnrc_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((NNRCUnop (OpRecRemove s1)) r) (at level 50) : nnrc_scope.          (* ¬ = \neg and π = \pi *)
Notation "π[ s1 ]( r )" := ((NNRCUnop (OpRecProject s1)) r) (at level 50) : nnrc_scope.          (* π = \pi *)
Notation "p · r" := ((NNRCUnop (OpDot r)) p) (left associativity, at level 40): nnrc_scope.      (* · = \cdot *)

Notation "'$$' v" := (NNRCGetConstant v%string) (at level 50, format "'$$' v") : nnrc_scope.
Notation "'$' v" := (NNRCVar v%string) (at level 50, format "'$' v") : nnrc_scope.
Notation "{| e1 | '$' x ∈ e2 |}" := (NNRCFor x%string e2 e1) (at level 50, format "{|  e1  '/ ' |  '$' x  ∈  e2  |}") : nnrc_scope.   (* ∈ = \in *)
Notation "'let' '$' x ':=' e2 'in' e1" := (NNRCLet x%string e2 e1) (at level 50, format "'[hv' 'let'  '$' x  ':='  '[' e2 ']'  '/' 'in'  '[' e1 ']' ']'") : nnrc_scope.
Notation "e1 ? e2 : e3" := (NNRCIf e1 e2 e3) (at level 50, format "e1  '[hv' ?  e2 '/' :  e3 ']'") : nnrc_scope.

Notation "r1 ‵+ r2" := (NNRCBinop (OpNatBinary NatPlus) r1 r2) (right associativity, at level 65): nnrc_scope.
Notation "r1 ‵* r2" := (NNRCBinop (OpNatBinary NatMult) r1 r2) (right associativity, at level 65): nnrc_scope.
Notation "‵abs r" := (NNRCUnop (OpNatUnary NatAbs) r) (right associativity, at level 64): nnrc_scope.

Tactic Notation "nnrc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NNRCGetConstant"%string
  | Case_aux c "NNRCVar"%string
  | Case_aux c "NNRCConst"%string
  | Case_aux c "NNRCBinop"%string
  | Case_aux c "NNRCUnop"%string
  | Case_aux c "NNRCLet"%string
  | Case_aux c "NNRCFor"%string
  | Case_aux c "NNRCIf"%string
  | Case_aux c "NNRCEither"%string
  | Case_aux c "NNRCGroupBy"%string].
(* end hide *)

