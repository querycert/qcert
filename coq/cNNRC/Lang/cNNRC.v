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

Section cNNRC.

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Morphisms.
  Require Import Utils.
  Require Import BasicRuntime.

  (** Named Nested Relational Calculus *)

  Context {fruntime:foreign_runtime}.
  
  (** * Abstract Syntax *)
  
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

  (** * Evaluation Semantics *)

  Context (h:brand_relation_t).
  
  Section Semantics.
    Context (constant_env:list (string*data)).

    (** Evaluation takes a cNNRC expression and an environment. It
        returns an optional value. A [None] being returned indicate an
        error and is always propagated. *)

    Fixpoint nnrc_core_eval (env:bindings) (e:nnrc) : option data :=
      match e with
      | NNRCGetConstant x =>
        edot constant_env x
      | NNRCVar x =>
        lookup equiv_dec env x
      | NNRCConst d =>
        Some (normalize_data h d)
      | NNRCBinop bop e1 e2 =>
        olift2 (fun d1 d2 => fun_of_binop h bop d1 d2) (nnrc_core_eval env e1) (nnrc_core_eval env e2)
      | NNRCUnop uop e1 =>
        olift (fun d1 => fun_of_unaryop h uop d1) (nnrc_core_eval env e1)
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

    (** * Toplevel *)
  
    (** The Top-level evaluation function is used externally by the
        Q*cert compiler. It takes a cNNRC expression and an global
        environment as input. *)
  End Semantics.

  Section Top.
    Definition nnrc_core_eval_top (q:nnrc_core) (cenv:bindings) : option data :=
      lift_nnrc_core (nnrc_core_eval (rec_sort cenv) nil) q.
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
