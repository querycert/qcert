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
the foundations for NNRC, an intermediate language to facilitate code
generation for non-functional targets. *)

(** cNNRC is a small pure language without functions. Expressions in
cNNRC are evaluated within an environment. *)

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
- Conditional expression allow arbitrary boolean conditions, not just equality, so
instead of [e1 = e2 ? e3 : e4], we have [e1 ? e2 : e3]
- We add a matching expression for either values (left/right)
*)

Section cNNRC.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Morphisms.
  Require Import Utils.
  Require Import CommonRuntime.

  (** Named Nested Relational Calculus *)

  Context {fruntime:foreign_runtime}.
  
  (** * Abstract Syntax *)

  Section Syntax.
  
    (** Note that the AST is shared between cNNRC and NNRC. However,
        semantics for extended operators are not defined for core
        NNRC. *)

    Inductive nnrc :=
    | NNRCGetConstant : var -> nnrc                             (**r Global variable lookup *)
    | NNRCVar : var -> nnrc                                     (**r Variable lookup *)
    | NNRCConst : data -> nnrc                                  (**r Constant value *)
    | NNRCBinop : binOp -> nnrc -> nnrc -> nnrc                 (**r Binary operator *)
    | NNRCUnop : unaryOp -> nnrc -> nnrc                        (**r Unary operator *)
    | NNRCLet : var -> nnrc -> nnrc -> nnrc                     (**r Let expression *)
    | NNRCFor : var -> nnrc -> nnrc -> nnrc                     (**r For loop *)
    | NNRCIf : nnrc -> nnrc -> nnrc -> nnrc                     (**r Conditional *)
    | NNRCEither : nnrc -> var -> nnrc -> var -> nnrc -> nnrc   (**r Choice expression *)
    | NNRCGroupBy : string -> list string -> nnrc -> nnrc.      (**r Group by expression -- only in NNRC *)

    (** The nnrcIsCore predicate defines what fragment is part of this
        abstract syntax is in the core cNNRC and which part is not. *)
  
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

    (** cNNRC is defined as the dependent type of expressions in that
        abstract syntax such that the [nnrcIsCore] predicate holds. *)
  
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
        try solve [apply binOp_eqdec | apply unaryOp_eqdec
                   | apply data_eqdec | apply string_eqdec].
      - decide equality; apply string_dec.
    Defined.

  End Syntax.
  
  (** * Semantics *)

  (** For Core NNRC, we provide two kinds of semantics: a denotational semantics, and an evaluation semantics. Both are shown to be consistent. The denotational semantics is used for illustration purposes, as most of the rest of the code relies on evaluation as the primary semantics. *)
  
  Section Semantics.
    (** Part of the context is fixed for the rest of the development:
- [h] is the brand relation
- [constant_env] is the global environment *)

    Context (h:brand_relation_t).
    Context (constant_env:list (string*data)).

    (** ** Semantics *)
  
    Section DenotSemantics.
      Inductive nnrc_core_sem: bindings -> nnrc -> data -> Prop :=
      | sem_NNRCGetConstant: forall env c dres,
          edot constant_env c = Some dres ->
          nnrc_core_sem env (NNRCGetConstant c) dres
      | sem_NNRCVar: forall env c dres,
          lookup equiv_dec env c = Some dres ->
          nnrc_core_sem env (NNRCVar c) dres
      | sem_NNRCConst: forall env d,
          nnrc_core_sem env (NNRCConst d) (normalize_data h d)
      | sem_NNRCBinop: forall bop env e1 e2 d1 d2 dres,
          nnrc_core_sem env e1 d1 ->
          nnrc_core_sem env e2 d2 ->
          fun_of_binop h bop d1 d2 = Some dres ->
          nnrc_core_sem env (NNRCBinop bop e1 e2) dres
      | sem_NNRCUnop: forall uop env e d dres,
          nnrc_core_sem env e d ->
          fun_of_unaryop h uop d = Some dres ->
          nnrc_core_sem env (NNRCUnop uop e) dres
      | sem_NNRCLet: forall env e1 x e2 d1 dres,
          nnrc_core_sem env e1 d1 ->
          nnrc_core_sem ((x,d1)::env) e2 dres ->
          nnrc_core_sem env (NNRCLet x e1 e2) dres
      | sem_NNRCFor: forall env e1 x e2 c1 cres,
          nnrc_core_sem env e1 (dcoll c1) ->
          nnrc_core_sem_for x env e2 c1 cres ->
          nnrc_core_sem env (NNRCFor x e1 e2) (dcoll cres)
      | sem_NNRCIf_true: forall env e1 e2 e3 dres,
          nnrc_core_sem env e1 (dbool true) ->
          nnrc_core_sem env e2 dres ->
          nnrc_core_sem env (NNRCIf e1 e2 e3) dres
      | sem_NNRCIf_false: forall env e1 e2 e3 dres,
          nnrc_core_sem env e1 (dbool false) ->
          nnrc_core_sem env e3 dres ->
          nnrc_core_sem env (NNRCIf e1 e2 e3) dres
      | sem_NNRCEither_left: forall env e1 xl el xr er dl dres,
          nnrc_core_sem env e1 (dleft dl) ->
          nnrc_core_sem ((xl,dl)::env) el dres ->
          nnrc_core_sem env (NNRCEither e1 xl el xr er) dres
      | sem_NNRCEither_right: forall env e1 xl el xr er dr dres,
          nnrc_core_sem env e1 (dright dr) ->
          nnrc_core_sem ((xr,dr)::env) er dres ->
          nnrc_core_sem env (NNRCEither e1 xl el xr er) dres
      with nnrc_core_sem_for: var -> bindings -> nnrc -> list data -> list data -> Prop :=
           | sem_NNRCFor_empty x: forall env e,
               nnrc_core_sem_for x env e nil nil
           | sem_NNRCFor_cons x: forall env e d c dres cres,
               nnrc_core_sem ((x,d)::env) e dres ->
               nnrc_core_sem_for x env e c cres ->
               nnrc_core_sem_for x env e (d::c) (dres::cres).

    End DenotSemantics.

    (** * Evaluation Semantics *)
    Section EvalSemantics.

      (** Evaluation takes a cNNRC expression and an environment. It
          returns an optional value. A [None] being returned indicate
          an error and is always propagated. *)

      Fixpoint nnrc_core_eval (env:bindings) (e:nnrc) : option data :=
        match e with
        | NNRCGetConstant x =>
          edot constant_env x
        | NNRCVar x =>
          lookup equiv_dec env x
        | NNRCConst d =>
          Some (normalize_data h d)
        | NNRCBinop bop e1 e2 =>
          olift2 (fun d1 d2 => fun_of_binop h bop d1 d2)
                 (nnrc_core_eval env e1)
                 (nnrc_core_eval env e2)
        | NNRCUnop uop e1 =>
          olift (fun d1 => fun_of_unaryop h uop d1)
                (nnrc_core_eval env e1)
        | NNRCLet x e1 e2 =>
          match nnrc_core_eval env e1 with
          | Some d => nnrc_core_eval ((x,d)::env) e2
          | _ => None
          end
        | NNRCFor x e1 e2 =>
          match nnrc_core_eval env e1 with
          | Some (dcoll c1) =>
            let inner_eval d1 :=
                let env' := (x,d1) :: env in nnrc_core_eval env' e2
            in
            lift dcoll (rmap inner_eval c1)
          | _ => None
          end
        | NNRCIf e1 e2 e3 =>
          let aux_if d :=
              match d with
              | dbool b =>
                if b then nnrc_core_eval env e2 else nnrc_core_eval env e3
              | _ => None
              end
          in olift aux_if (nnrc_core_eval env e1)
        | NNRCEither ed xl el xr er =>
          match nnrc_core_eval env ed with
          | Some (dleft dl) =>
            nnrc_core_eval ((xl,dl)::env) el
          | Some (dright dr) =>
            nnrc_core_eval ((xr,dr)::env) er
          | _ => None
          end
        | NNRCGroupBy _ _ _ => None (**r Evaluation for GroupBy always fails for cNNRC *)
        end.

      (** cNNRC evaluation is only sensitive to the environment up to lookup. *)
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
          apply rmap_ext; intros.
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

    End EvalSemantics.

    Section EvalCorrect.
      (** Auxiliary lemma for the semantics of [for] loops *)
      Lemma nnrc_core_for_eval_correct v env e l lres:
        (rmap (fun d1 : data => nnrc_core_eval ((v, d1) :: env) e) l = Some lres) ->
        (forall (env : bindings) (dres : data),
            nnrc_core_eval env e = Some dres -> nnrc_core_sem env e dres) ->
        nnrc_core_sem_for v env e l lres.
      Proof.
        revert lres; induction l; simpl; intros.
        - inversion H; subst; econstructor.
        - case_eq (nnrc_core_eval ((v, a) :: env) e); intros;
            rewrite H1 in *.
          + unfold lift in H.
            case_eq (rmap (fun d1 : data => nnrc_core_eval ((v, d1) :: env) e) l);
              intros; rewrite H2 in *; clear H2; [|congruence].
            inversion H; subst; clear H.
            specialize (IHl l0 eq_refl H0).
            econstructor.
            apply H0; auto.
            auto.
          + congruence.
      Qed.

      (** If NNRC eval returns a value, this value is consistent with the semantics *)
      Lemma nnrc_core_eval_correct : forall e env dres,
          nnrc_core_eval env e = Some dres ->
          nnrc_core_sem env e dres.
      Proof.
        induction e; simpl; intros.
        - constructor; trivial.
        - constructor; trivial.
        - inversion H; constructor.
        - specialize (IHe1 env); specialize (IHe2 env).
          case_eq (nnrc_core_eval env e1); intros; rewrite H0 in *.
          + case_eq (nnrc_core_eval env e2); intros; rewrite H1 in *.
            * specialize (IHe1 d eq_refl); specialize (IHe2 d0 eq_refl);
                econstructor; eauto.
            * simpl in H; congruence.
          + simpl in H; congruence.
        - specialize (IHe env).
          case_eq (nnrc_core_eval env e); intros; rewrite H0 in *.
          + specialize (IHe d eq_refl); econstructor; eauto.
          + simpl in H; congruence.
        - specialize (IHe1 env).
          case_eq (nnrc_core_eval env e1); intros; rewrite H0 in *.
          + case_eq (nnrc_core_eval ((v,d)::env) e2); intros.
            * specialize (IHe2 ((v,d)::env)).
              rewrite H1 in *; inversion H; subst; clear H.
              specialize (IHe2 dres eq_refl);
                econstructor; eauto.
            * simpl in H; congruence.
          + simpl in H; congruence.
        - specialize (IHe1 env).
          case_eq (nnrc_core_eval env e1); intros; rewrite H0 in *.
          + destruct d; simpl in H; try congruence.
            specialize (IHe1 (dcoll l) eq_refl).
            unfold lift in H.
            case_eq (rmap (fun d1 : data => nnrc_core_eval ((v, d1) :: env) e2) l);
              intros; rewrite H1 in H; try congruence.
            inversion H; subst; clear H.
            econstructor; eauto.
            apply nnrc_core_for_eval_correct; eauto.
          + simpl in H; congruence.
        - specialize (IHe1 env); specialize (IHe2 env); specialize (IHe3 env).
          case_eq (nnrc_core_eval env e1); intros; rewrite H0 in *; simpl in H.
          destruct d; simpl in H; try congruence.
          destruct b.
          (* condition true *)
          + case_eq (nnrc_core_eval env e2); intros; rewrite H1 in *.
            * specialize (IHe1 (dbool true) eq_refl); specialize (IHe2 d eq_refl);
                inversion H; subst; eapply sem_NNRCIf_true; eauto.
            * simpl in H; congruence.
          (* condition false *)
          + case_eq (nnrc_core_eval env e3); intros; rewrite H1 in *.
            * specialize (IHe1 (dbool false) eq_refl); specialize (IHe3 d eq_refl);
                inversion H; subst; eapply sem_NNRCIf_false; eauto.
            * simpl in H; congruence.
          + simpl in H; congruence.
        - specialize (IHe1 env).
          case_eq (nnrc_core_eval env e1); intros; rewrite H0 in *; simpl in H.
          destruct d; simpl in H; try congruence.
          (* left case *)
          + specialize (IHe2 ((v,d)::env)).
            * specialize (IHe1 (dleft d) eq_refl); specialize (IHe2 dres H);
                inversion H; subst; eapply sem_NNRCEither_left; eauto.
          (* right case *)
          + specialize (IHe3 ((v0,d)::env)).
            * specialize (IHe1 (dright d) eq_refl); specialize (IHe3 dres H);
                inversion H; subst; eapply sem_NNRCEither_right; eauto.
          + simpl in H; congruence.
        - congruence.
      Qed.

    End EvalCorrect.

  End Semantics.

  (** * Toplevel *)
  
  (** The Top-level evaluation function is used externally by the
      Q*cert compiler. It takes a cNNRC expression and an global
      environment as input. *)

  Section Top.
    Context (h:brand_relation_t).

    (** Top-level semantics is always with an initial empty environment *)
    Inductive nnrc_core_top_sem : nnrc_core -> bindings -> data -> Prop :=
    | sem_NNRCTop: forall e cenv dres,
        nnrc_core_sem h cenv nil (proj1_sig e) dres ->
        nnrc_core_top_sem e cenv dres.

    Definition nnrc_core_eval_top (q:nnrc_core) (cenv:bindings) : option data :=
      lift_nnrc_core (nnrc_core_eval h (rec_sort cenv) nil) q.

    (** If top-level NNRC eval returns a value, this value is
        consistent with the semantics *)
    Theorem nnrc_core_eval_top_correct:
      forall cenv,
      rec_sort cenv = cenv -> (* This assumption should be part of constant_env *)
      forall (q:nnrc_core) (dres:data),
        nnrc_core_eval_top q cenv = Some dres ->
        nnrc_core_top_sem q cenv dres.
    Proof.
      intros cenv HconstNorm q dres.
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

Notation "r1 ∧ r2" := (NNRCBinop AAnd r1 r2) (right associativity, at level 65): nnrc_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (NNRCBinop AOr r1 r2) (right associativity, at level 70): nnrc_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (NNRCBinop AEq r1 r2) (right associativity, at level 70): nnrc_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (NNRCBinop ALt r1 r2) (no associativity, at level 70): nnrc_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (NNRCBinop AUnion r1 r2) (right associativity, at level 70): nnrc_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (NNRCBinop AMinus r1 r2) (right associativity, at level 70): nnrc_scope.  (* − = \minus *)
Notation "r1 ⋂min r2" := (NNRCBinop AMin r1 r2) (right associativity, at level 70): nnrc_scope. (* ♯ = \sharp *)
Notation "r1 ⋃max r2" := (NNRCBinop AMax r1 r2) (right associativity, at level 70): nnrc_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((NNRCBinop AConcat) p r) (at level 70) : nnrc_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((NNRCBinop AMergeConcat) p r) (at level 70) : nnrc_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (NNRCUnop ANeg r1) (right associativity, at level 70): nnrc_scope.        (* ¬ = \neg *)
Notation "ε( r1 )" := (NNRCUnop ADistinct r1) (right associativity, at level 70): nnrc_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (NNRCUnop ACount r1) (right associativity, at level 70): nnrc_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (NNRCUnop AFlatten d) (at level 50) : nnrc_scope.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((NNRCUnop AColl) d)  (at level 50) : nnrc_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((NNRCUnop (ARec s)) r) (at level 50) : nnrc_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((NNRCUnop (ARecRemove s1)) r) (at level 50) : nnrc_scope.          (* ¬ = \neg and π = \pi *)
Notation "π[ s1 ]( r )" := ((NNRCUnop (ARecProject s1)) r) (at level 50) : nnrc_scope.          (* π = \pi *)
Notation "p · r" := ((NNRCUnop (ADot r)) p) (left associativity, at level 40): nnrc_scope.      (* · = \cdot *)

Notation "'$$' v" := (NNRCVar v%string) (at level 50, format "'$$' v") : nnrc_scope.
Notation "{| e1 | '$$' x ∈ e2 |}" := (NNRCFor x%string e2 e1) (at level 50, format "{|  e1  '/ ' |  '$$' x  ∈  e2  |}") : nnrc_scope.   (* ∈ = \in *)
Notation "'LET' '$$' x ':=' e2 'IN' e1" := (NNRCLet x%string e2 e1) (at level 50, format "'[hv' 'LET'  '$$' x  ':='  '[' e2 ']'  '/' 'IN'  '[' e1 ']' ']'") : nnrc_scope.
Notation "e1 ? e2 : e3" := (NNRCIf e1 e2 e3) (at level 50, format "e1  '[hv' ?  e2 '/' :  e3 ']'") : nnrc_scope.

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

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
