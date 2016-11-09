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

Section NNRC.

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Morphisms.

  Require Import Utils BasicRuntime.

  (** Named Nested Relational Calculus *)

  Context {fruntime:foreign_runtime}.
  
  Definition var := string.
  
  Inductive nrc :=
  | NRCVar : var -> nrc
  | NRCConst : data -> nrc
  | NRCBinop : binOp -> nrc -> nrc -> nrc
  | NRCUnop : unaryOp -> nrc -> nrc
  | NRCLet : var -> nrc -> nrc -> nrc
  | NRCFor : var -> nrc -> nrc -> nrc
  | NRCIf : nrc -> nrc -> nrc -> nrc
  | NRCEither : nrc -> var -> nrc -> var -> nrc -> nrc.

  Tactic Notation "nrc_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "NRCVar"%string
    | Case_aux c "NRCConst"%string
    | Case_aux c "NRCBinop"%string
    | Case_aux c "NRCUnop"%string
    | Case_aux c "NRCLet"%string
    | Case_aux c "NRCFor"%string
    | Case_aux c "NRCIf"%string
    | Case_aux c "NRCEither"%string].

  Global Instance nrc_eqdec : EqDec nrc eq.
  Proof.
    change (forall x y : nrc,  {x = y} + {x <> y}).
    decide equality;
      try solve [apply binOp_eqdec | apply unaryOp_eqdec
                 | apply data_eqdec | apply string_eqdec].
  Defined.

  (** Semantics of NNRC *)

  Context (h:brand_relation_t).

  Fixpoint nrc_eval (env:bindings) (e:nrc) : option data :=
    match e with
      | NRCVar x =>
        lookup equiv_dec env x
      | NRCConst d =>
         Some (normalize_data h d)
      | NRCBinop bop e1 e2 =>
        olift2 (fun d1 d2 => fun_of_binop h bop d1 d2) (nrc_eval env e1) (nrc_eval env e2)
      | NRCUnop uop e1 =>
        olift (fun d1 => fun_of_unaryop h uop d1) (nrc_eval env e1)
      | NRCLet x e1 e2 =>
        match nrc_eval env e1 with
        | Some d => nrc_eval ((x,d)::env) e2
        | _ => None
        end
      | NRCFor x e1 e2 =>
        match nrc_eval env e1 with
        | Some (dcoll c1) =>
          let inner_eval d1 :=
              let env' := (x,d1) :: env in nrc_eval env' e2
          in
          lift dcoll (rmap inner_eval c1)
        | _ => None
        end
      | NRCIf e1 e2 e3 =>
        let aux_if d :=
            match d with
            | dbool b =>
              if b then nrc_eval env e2 else nrc_eval env e3
            | _ => None
            end
        in olift aux_if (nrc_eval env e1)
      | NRCEither ed xl el xr er =>
        match nrc_eval env ed with
        | Some (dleft dl) =>
          nrc_eval ((xl,dl)::env) el
        | Some (dright dr) =>
          nrc_eval ((xr,dr)::env) er
        | _ => None
        end
    end.

  (* we are only sensitive to the environment up to lookup *)
  Global Instance nrc_eval_lookup_equiv_prop :
    Proper (lookup_equiv ==> eq ==> eq) nrc_eval.
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

End NNRC.

(* begin hide *)
Notation "‵‵ c" := (NRCConst (dconst c))  (at level 0) : nrc_scope.                           (* ‵ = \backprime *)
Notation "‵ c" := (NRCConst c)  (at level 0) : nrc_scope.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (NRCConst (dcoll nil))  (at level 0) : nrc_scope.                         (* ‵ = \backprime *)
Notation "‵[||]" := (NRCConst (drec nil)) (at level 50) : nrc_scope.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (NRCBinop AAnd r1 r2) (right associativity, at level 65): nrc_scope.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (NRCBinop AOr r1 r2) (right associativity, at level 70): nrc_scope.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (NRCBinop AEq r1 r2) (right associativity, at level 70): nrc_scope.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (NRCBinop ALt r1 r2) (no associativity, at level 70): nrc_scope.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (NRCBinop AUnion r1 r2) (right associativity, at level 70): nrc_scope.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (NRCBinop AMinus r1 r2) (right associativity, at level 70): nrc_scope.  (* − = \minus *)
Notation "r1 ⋂min r2" := (NRCBinop AMin r1 r2) (right associativity, at level 70): nrc_scope. (* ♯ = \sharp *)
Notation "r1 ⋃max r2" := (NRCBinop AMax r1 r2) (right associativity, at level 70): nrc_scope. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((NRCBinop AConcat) p r) (at level 70) : nrc_scope.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((NRCBinop AMergeConcat) p r) (at level 70) : nrc_scope.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (NRCUnop ANeg r1) (right associativity, at level 70): nrc_scope.        (* ¬ = \neg *)
Notation "ε( r1 )" := (NRCUnop ADistinct r1) (right associativity, at level 70): nrc_scope.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (NRCUnop ACount r1) (right associativity, at level 70): nrc_scope. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (NRCUnop AFlatten d) (at level 50) : nrc_scope.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((NRCUnop AColl) d)  (at level 50) : nrc_scope.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((NRCUnop (ARec s)) r) (at level 50) : nrc_scope.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((NRCUnop (ARecRemove s1)) r) (at level 50) : nrc_scope.          (* ¬ = \neg and π = \pi *)
Notation "π[ s1 ]( r )" := ((NRCUnop (ARecProject s1)) r) (at level 50) : nrc_scope.          (* π = \pi *)
Notation "p · r" := ((NRCUnop (ADot r)) p) (left associativity, at level 40): nrc_scope.      (* · = \cdot *)

Notation "'$$' v" := (NRCVar v%string) (at level 50, format "'$$' v") : nrc_scope.
Notation "{| e1 | '$$' x ∈ e2 |}" := (NRCFor x%string e2 e1) (at level 50, format "{|  e1  '/ ' |  '$$' x  ∈  e2  |}") : nrc_scope.   (* ∈ = \in *)
Notation "'LET' '$$' x ':=' e2 'IN' e1" := (NRCLet x%string e2 e1) (at level 50, format "'[hv' 'LET'  '$$' x  ':='  '[' e2 ']'  '/' 'IN'  '[' e1 ']' ']'") : nrc_scope.
Notation "e1 ? e2 : e3" := (NRCIf e1 e2 e3) (at level 50, format "e1  '[hv' ?  e2 '/' :  e3 ']'") : nrc_scope.

Tactic Notation "nrc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NRCVar"%string
  | Case_aux c "NRCConst"%string
  | Case_aux c "NRCBinop"%string
  | Case_aux c "NRCUnop"%string
  | Case_aux c "NRCLet"%string
  | Case_aux c "NRCFor"%string
  | Case_aux c "NRCIf"%string
  | Case_aux c "NRCEither"%string].

(* end hide *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
