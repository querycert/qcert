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
  
Section NNRSimp.

  Section Syntax.

    Context {fruntime:foreign_runtime}.

    Inductive nnrs_imp_expr :=
    | NNRSimpGetConstant : var -> nnrs_imp_expr                                   (**r global variable lookup ([$$v]) *)
    | NNRSimpVar : var -> nnrs_imp_expr                                           (**r local variable lookup ([$v])*)
    | NNRSimpConst : data -> nnrs_imp_expr                                        (**r constant data ([d]) *)
    | NNRSimpBinop : binary_op -> nnrs_imp_expr -> nnrs_imp_expr -> nnrs_imp_expr (**r binary operator ([e₁ ⊠ e₂]) *)
    | NNRSimpUnop : unary_op -> nnrs_imp_expr -> nnrs_imp_expr                    (**r unary operator ([⊞ e]) *)
    | NNRSimpGroupBy : string -> list string -> nnrs_imp_expr -> nnrs_imp_expr    (**r group by expression ([e groupby g fields]) -- only in full NNRC *)
    .

    Inductive nnrs_imp_stmt :=
    | NNRSimpSkip : nnrs_imp_stmt
    | NNRSimpSeq : nnrs_imp_stmt -> nnrs_imp_stmt -> nnrs_imp_stmt                    (**r sequence ([s₁; s₂]]) *)
    | NNRSimpAssign : var -> nnrs_imp_expr -> nnrs_imp_stmt                           (**r variable assignent ([$v := e]) *)
    | NNRSimpLet : var -> option nnrs_imp_expr -> nnrs_imp_stmt -> nnrs_imp_stmt (**r variable declaration ([var $v := e₁?; s₂]) *)
    | NNRSimpFor : var -> nnrs_imp_expr -> nnrs_imp_stmt -> nnrs_imp_stmt             (**r for loop ([for ($v in e₁) { s₂ }]) *)
    | NNRSimpIf : nnrs_imp_expr -> nnrs_imp_stmt -> nnrs_imp_stmt -> nnrs_imp_stmt    (**r conditional ([if e₁ { s₂ } else { s₃ }]) *)
    | NNRSimpEither : nnrs_imp_expr                                                   (**r case expression ([either e case left $v₁ { s₁ } case right $v₂ { s₂ }]) *)
                      -> var -> nnrs_imp_stmt
                      -> var -> nnrs_imp_stmt -> nnrs_imp_stmt
    .

    (** [nnrs_imp] is composed of the statement evaluating the query
        and the variable containing the result of the evaluation *)
    Definition nnrs_imp : Set := (nnrs_imp_stmt * var).

    (* Note: `Let x = e in s' should be equivalent to `for (x<-{e}) in s' *)
    (* which should be the same as `either (dleft e) (x->s) (_->_) ' *)
    
  End Syntax.

  Section dec.
    Context {fruntime:foreign_runtime}.

    Global Instance nnrs_imp_expr_eqdec : EqDec nnrs_imp_expr eq.
    Proof.
      change (forall x y : nnrs_imp_expr,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply binary_op_eqdec | apply unary_op_eqdec
                   | apply data_eqdec | apply string_eqdec].
      - decide equality; apply string_dec.
    Defined.

    Global Instance nnrs_imp_stmt_eqdec : EqDec nnrs_imp_stmt eq.
    Proof.
      change (forall x y : nnrs_imp_stmt,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply nnrs_imp_expr_eqdec | apply string_eqdec | apply option_eqdec].
    Defined.

    Global Instance nnrs_imp_eqdec : EqDec nnrs_imp eq.
    Proof.
      intros [s1 r1] [s2 r2].
      destruct (r1 == r2).
      - destruct (s1 == s2).
        + left; congruence.
        + right; congruence.
      - right; congruence.
    Defined.
  End dec.

  Section Core.

    Context {fruntime:foreign_runtime}.

    Fixpoint nnrs_imp_exprIsCore (e:nnrs_imp_expr) : Prop :=
      match e with
      | NNRSimpGetConstant _ => True
      | NNRSimpVar _ => True
      | NNRSimpConst _ => True
      | NNRSimpBinop _ e1 e2 => nnrs_imp_exprIsCore e1 /\ nnrs_imp_exprIsCore e2
      | NNRSimpUnop _ e1 => nnrs_imp_exprIsCore e1
      | NNRSimpGroupBy _ _ _ => False
      end.
    
    Fixpoint nnrs_imp_stmtIsCore (s:nnrs_imp_stmt) : Prop :=
      match s with
      | NNRSimpSkip => True
      | NNRSimpSeq s1 s2 =>
        nnrs_imp_stmtIsCore s1 /\ nnrs_imp_stmtIsCore s2
      | NNRSimpLet _ (Some e) s1 =>
        nnrs_imp_exprIsCore e /\ nnrs_imp_stmtIsCore s1
      | NNRSimpLet _ None s1 =>
        nnrs_imp_stmtIsCore s1
      | NNRSimpAssign _ e =>
        nnrs_imp_exprIsCore e
      | NNRSimpFor _ e s1 =>
        nnrs_imp_exprIsCore e /\ nnrs_imp_stmtIsCore s1
      | NNRSimpIf e s1 s2 =>
        nnrs_imp_exprIsCore e /\ nnrs_imp_stmtIsCore s1 /\ nnrs_imp_stmtIsCore s2
      | NNRSimpEither e _ s1 _ s2 =>
        nnrs_imp_exprIsCore e /\ nnrs_imp_stmtIsCore s1 /\ nnrs_imp_stmtIsCore s2
      end .

    Definition nnrs_impIsCore (sr:nnrs_imp) := nnrs_imp_stmtIsCore (fst sr).

    Definition nnrs_imp_core : Set := {sr:nnrs_imp | nnrs_impIsCore sr}.

    Definition nnrs_imp_core_to_nnrs_imp (sr:nnrs_imp_core) : nnrs_imp :=
      proj1_sig sr.

    Section ext.

      Lemma nnrs_imp_exprIsCore_ext (e:nnrs_imp_expr) (pf1 pf2:nnrs_imp_exprIsCore e) : pf1 = pf2.
      Proof.
        induction e; simpl in *;
          try (destruct pf1; destruct pf2; trivial);
          try f_equal; auto.
      Qed.

      Lemma nnrs_imp_stmtIsCore_ext (s:nnrs_imp_stmt) (pf1 pf2:nnrs_imp_stmtIsCore s) : pf1 = pf2.
      Proof.
        induction s; simpl in *;
          try (destruct o);
          try (destruct pf1; destruct pf2; trivial);
          try (destruct a; destruct a0);
          try f_equal; eauto;
            try eapply nnrs_imp_exprIsCore_ext; eauto
            ; try f_equal; eauto.
      Qed.

      Lemma nnrs_impIsCore_ext (e:nnrs_imp) (pf1 pf2:nnrs_impIsCore e) : pf1 = pf2.
      Proof.
        apply nnrs_imp_stmtIsCore_ext.
      Qed.

      Lemma nnrs_imp_core_ext e (pf1 pf2:nnrs_impIsCore e) :
        exist _ e pf1 = exist _ e pf2.
      Proof.
        f_equal; apply nnrs_impIsCore_ext.
      Qed.

      Lemma nnrs_imp_core_fequal (e1 e2:nnrs_imp_core) :
        proj1_sig e1 = proj1_sig e2 -> e1 = e2.
      Proof.
        destruct e1; destruct e2; simpl; intros eqq.
        destruct eqq.
        apply nnrs_imp_core_ext.
      Qed.

    End ext.
    
    Section dec.

      Lemma nnrs_imp_exprIsCore_dec (e:nnrs_imp_expr) :
        {nnrs_imp_exprIsCore e} + {~ nnrs_imp_exprIsCore e}.
      Proof.
        induction e; simpl; try eauto 3.
        destruct IHe1.
        - destruct IHe2; [left|right]; intuition.
        - right; intuition.
      Defined.

      Lemma nnrs_imp_stmtIsCore_dec (s:nnrs_imp_stmt) :
        {nnrs_imp_stmtIsCore s} + {~ nnrs_imp_stmtIsCore s}.
      Proof.
        induction s; simpl.
        - left; trivial.
        - destruct IHs1.
          + destruct IHs2; [left|right]; intuition.
          + right; intuition.
        - apply (nnrs_imp_exprIsCore_dec n).
        - destruct o.
          + destruct (nnrs_imp_exprIsCore_dec n).
            * destruct IHs; [left|right]; intuition.
            * right; intuition.
          + apply IHs.
        - destruct (nnrs_imp_exprIsCore_dec n).
          + destruct IHs; [left|right]; intuition.
          + right; intuition.
        - destruct (nnrs_imp_exprIsCore_dec n).
          + destruct IHs1.
            * destruct IHs2; [left|right]; intuition.
            * right; intuition.
          + right; intuition.
        - destruct (nnrs_imp_exprIsCore_dec n).
          + destruct IHs1.
            * destruct IHs2; [left|right]; intuition.
            * right; intuition.
          + right; intuition.
      Defined.

      Lemma nnrs_impIsCore_dec (sr:nnrs_imp) :
        {nnrs_impIsCore sr} + {~ nnrs_impIsCore sr}.
      Proof.
        apply nnrs_imp_stmtIsCore_dec.
      Defined.

      Global Instance nnrs_imp_core_eqdec : EqDec nnrs_imp_core eq.
      Proof.
        intros x y.
        destruct x as [x xpf]; destruct y as [y ypf].
        destruct (x == y).
        - left. apply nnrs_imp_core_fequal; simpl; trivial.
        - right. inversion 1; congruence.
      Defined.

    End dec.

End Core.

Section Env.
  Context {fruntime:foreign_runtime}.

  (* bindings that may or may not be initialized (defined) *)
  Definition pd_bindings := list (string*option data).

End Env.

End NNRSimp.

Tactic Notation "nnrs_imp_expr_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NNRSimpGetConstant"%string
  | Case_aux c "NNRSimpVar"%string
  | Case_aux c "NNRSimpConst"%string
  | Case_aux c "NNRSimpBinop"%string
  | Case_aux c "NNRSimpUnop"%string
  | Case_aux c "NNRSimpGroupBy"%string].

Tactic Notation "nnrs_imp_stmt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NNRSimpSkip"%string
  | Case_aux c "NNRSimpSeq"%string
  | Case_aux c "NNRSimpAssign"%string
  | Case_aux c "NNRSimpLet"%string
  | Case_aux c "NNRSimpFor"%string
  | Case_aux c "NNRSimpIf"%string
  | Case_aux c "NNRSimpEither"%string].

Delimit Scope nnrs_imp with nnrs_imp_scope.

(* begin hide *)
Notation "‵‵ c" := (NNRSimpConst (dconst c))  (at level 0) : nnrs_imp.                           (* ‵ = \backprime *)
Notation "‵ c" := (NNRSimpConst c)  (at level 0) : nnrs_imp.                                     (* ‵ = \backprime *)
Notation "‵{||}" := (NNRSimpConst (dcoll nil))  (at level 0) : nnrs_imp.                         (* ‵ = \backprime *)
Notation "‵[||]" := (NNRSimpConst (drec nil)) (at level 50) : nnrs_imp.                          (* ‵ = \backprime *)

Notation "r1 ∧ r2" := (NNRSimpBinop OpAnd r1 r2) (right associativity, at level 65): nnrs_imp.    (* ∧ = \wedge *)
Notation "r1 ∨ r2" := (NNRSimpBinop OpOr r1 r2) (right associativity, at level 70): nnrs_imp.     (* ∨ = \vee *)
Notation "r1 ≐ r2" := (NNRSimpBinop OpEqual r1 r2) (right associativity, at level 70): nnrs_imp.     (* ≐ = \doteq *)
Notation "r1 ≤ r2" := (NNRSimpBinop OpLe r1 r2) (no associativity, at level 70): nnrs_imp.     (* ≤ = \leq *)
Notation "r1 ⋃ r2" := (NNRSimpBinop OpBagUnion r1 r2) (right associativity, at level 70): nnrs_imp.  (* ⋃ = \bigcup *)
Notation "r1 − r2" := (NNRSimpBinop OpBagDiff r1 r2) (right associativity, at level 70): nnrs_imp.  (* − = \minus *)
Notation "r1 ⋂min r2" := (NNRSimpBinop OpBagMin r1 r2) (right associativity, at level 70): nnrs_imp. (* ♯ = \sharp *)
Notation "r1 ⋃max r2" := (NNRSimpBinop OpBagMax r1 r2) (right associativity, at level 70): nnrs_imp. (* ♯ = \sharp *)
Notation "p ⊕ r"   := ((NNRSimpBinop OpRecConcat) p r) (at level 70) : nnrs_imp.                     (* ⊕ = \oplus *)
Notation "p ⊗ r"   := ((NNRSimpBinop OpRecMerge) p r) (at level 70) : nnrs_imp.                (* ⊗ = \otimes *)

Notation "¬( r1 )" := (NNRSimpUnop OpNeg r1) (right associativity, at level 70): nnrs_imp.        (* ¬ = \neg *)
Notation "ε( r1 )" := (NNRSimpUnop OpDistinct r1) (right associativity, at level 70): nnrs_imp.   (* ε = \epsilon *)
Notation "♯count( r1 )" := (NNRSimpUnop OpCount r1) (right associativity, at level 70): nnrs_imp. (* ♯ = \sharp *)
Notation "♯flatten( d )" := (NNRSimpUnop OpFlatten d) (at level 50) : nnrs_imp.                   (* ♯ = \sharp *)
Notation "‵{| d |}" := ((NNRSimpUnop OpBag) d)  (at level 50) : nnrs_imp.                        (* ‵ = \backprime *)
Notation "‵[| ( s , r ) |]" := ((NNRSimpUnop (OpRec s)) r) (at level 50) : nnrs_imp.              (* ‵ = \backprime *)
Notation "¬π[ s1 ]( r )" := ((NNRSimpUnop (OpRecRemove s1)) r) (at level 50) : nnrs_imp.          (* ¬ = \neg and π = \pi *)
Notation "π[ s1 ]( r )" := ((NNRSimpUnop (OpRecProject s1)) r) (at level 50) : nnrs_imp.          (* π = \pi *)
Notation "p · r" := ((NNRSimpUnop (OpDot r)) p) (left associativity, at level 40): nnrs_imp.      (* · = \cdot *)

(*
Notation "'$$' v" := (NNRSimpGetConstant v%string) (at level 50, format "'$$' v") : nnrs_imp.
Notation "'$' v" := (NNRSimpVar v%string) (at level 50, format "'$' v") : nnrs_imp.
Notation "{| e1 | '$' x ∈ e2 |}" := (NNRSimpFor x%string e2 e1) (at level 50, format "{|  e1  '/ ' |  '$' x  ∈  e2  |}") : nnrs_imp.   (* ∈ = \in *)
Notation "'let' '$' x ':=' e2 'in' e1" := (NNRSimpLet x%string e2 e1) (at level 50, format "'[hv' 'let'  '$' x  ':='  '[' e2 ']'  '/' 'in'  '[' e1 ']' ']'") : nnrs_imp.
Notation "e1 ? e2 : e3" := (NNRSimpIf e1 e2 e3) (at level 50, format "e1  '[hv' ?  e2 '/' :  e3 ']'") : nnrs_imp.
 *)

Notation "r1 ‵+ r2" := (NNRSimpBinop (OpNatBinary NatPlus) r1 r2) (right associativity, at level 65): nnrs_imp.
Notation "r1 ‵* r2" := (NNRSimpBinop (OpNatBinary NatMult) r1 r2) (right associativity, at level 65): nnrs_imp.
Notation "‵abs r" := (NNRSimpUnop (OpNatUnary NatAbs) r) (right associativity, at level 64): nnrs_imp.
