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

Section cNNRC.

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Morphisms.

  Require Import Utils BasicRuntime.

  (** Named Nested Relational Calculus *)

  Context {fruntime:foreign_runtime}.
  
  Definition var := string.

  (** Note that the AST is shared between core NNRC and NNRC.
      However, semantics for extended operators are not defined for core NNRC. *)
  Inductive nnrc :=
  | NNRCVar : var -> nnrc
  | NNRCConst : data -> nnrc
  | NNRCBinop : binOp -> nnrc -> nnrc -> nnrc
  | NNRCUnop : unaryOp -> nnrc -> nnrc
  | NNRCLet : var -> nnrc -> nnrc -> nnrc
  | NNRCFor : var -> nnrc -> nnrc -> nnrc
  | NNRCIf : nnrc -> nnrc -> nnrc -> nnrc
  | NNRCEither : nnrc -> var -> nnrc -> var -> nnrc -> nnrc
  (* Extended *)
  | NNRCGroupBy : string -> list string -> nnrc -> nnrc.

  (** The nnrcIsCore predicate defines what fragment is part of the core NNRC
      and which part is not. *)
  Fixpoint nnrcIsCore (e:nnrc) : Prop :=
    match e with
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

  Tactic Notation "nnrc_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "NNRCVar"%string
    | Case_aux c "NNRCConst"%string
    | Case_aux c "NNRCBinop"%string
    | Case_aux c "NNRCUnop"%string
    | Case_aux c "NNRCLet"%string
    | Case_aux c "NNRCFor"%string
    | Case_aux c "NNRCIf"%string
    | Case_aux c "NNRCEither"%string
    | Case_aux c "NNRCGroupBy"%string].

  Global Instance nnrc_eqdec : EqDec nnrc eq.
  Proof.
    change (forall x y : nnrc,  {x = y} + {x <> y}).
    decide equality;
      try solve [apply binOp_eqdec | apply unaryOp_eqdec
                 | apply data_eqdec | apply string_eqdec].
    - decide equality; apply string_dec.
  Defined.

  Section core.
    Definition nnrc_core : Set := {e:nnrc | nnrcIsCore e}.

    Definition nnrc_core_to_nnrc (e:nnrc_core) : nnrc :=
      proj1_sig e.

    Definition lift_nnrc_core {A} (f:nnrc -> A) (e:nnrc_core) : A :=
      f (proj1_sig e).
    
  End core.
  
  (** Semantics of NNRC Core *)

  Context (h:brand_relation_t).

  Fixpoint nnrc_core_eval (env:bindings) (e:nnrc) : option data :=
    match e with
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
      | NNRCGroupBy _ _ _ => None (* Fails for core eval *)
    end.

  (* we are only sensitive to the environment up to lookup *)
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

End cNNRC.

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
  [ Case_aux c "NNRCVar"%string
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
