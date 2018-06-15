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

Section NNRS.
  Section Syntax.

    Context {fruntime:foreign_runtime}.
    
    Inductive nnrs_expr :=
    | NNRSGetConstant : var -> nnrs_expr                                   (**r global variable lookup ([$$v]) *)
    | NNRSVar : var -> nnrs_expr                                           (**r local variable lookup ([$v])*)
    | NNRSConst : data -> nnrs_expr                                        (**r constant data ([d]) *)
    | NNRSBinop : binary_op -> nnrs_expr -> nnrs_expr -> nnrs_expr (**r binary operator ([e₁ ⊠ e₂]) *)
    | NNRSUnop : unary_op -> nnrs_expr -> nnrs_expr                    (**r unary operator ([⊞ e]) *)
    | NNRSGroupBy : string -> list string -> nnrs_expr -> nnrs_expr    (**r group by expression ([e groupby g fields]) -- only in full NNRC *)
    .

    Inductive nnrs_stmt :=
    | NNRSSeq : nnrs_stmt -> nnrs_stmt -> nnrs_stmt                    (**r sequence ([s₁; s₂]]) *)
    (* This creates a mutable data holder, and evaluates the first
       statement with it bound to the given variable.  It then freezes
       the variable (makes it contain normal data) and evaluates the second
       statement with the variable bound to the normal data version *)
    | NNRSLet : var -> nnrs_expr -> nnrs_stmt -> nnrs_stmt (**r variable declaration ([var $v := e₁; s₂]) *)
    | NNRSLetMut : var -> nnrs_stmt -> nnrs_stmt -> nnrs_stmt (**r variable declaration ([var $v; s₁; s₂]) *)
    (* This creates a mutable collection, and evaluates the first
       statement with it bound to the given variable.  It then freezes
       the collection (makes it a normal bag) and evaluates the second
       statement with the variable bound to the bag version *)
    | NNRSLetMutColl : var -> nnrs_stmt -> nnrs_stmt -> nnrs_stmt    (**r mutable collection declaration ([var $v := {}; s1 ; s2]) *)
    | NNRSAssign : var -> nnrs_expr -> nnrs_stmt                           (**r variable assignent ([$v := e]) *)
    (* pushes to a variable that holds a mutable collection *)
    | NNRSPush : var -> nnrs_expr -> nnrs_stmt                             (**r push item in mutable collection ([push e in $v]) *)
    | NNRSFor : var -> nnrs_expr -> nnrs_stmt -> nnrs_stmt             (**r for loop ([for ($v in e₁) { s₂ }]) *)
    | NNRSIf : nnrs_expr -> nnrs_stmt -> nnrs_stmt -> nnrs_stmt    (**r conditional ([if e₁ { s₂ } else { s₃ }]) *)
    | NNRSEither : nnrs_expr                                                   (**r case expression ([either e case left $v₁ { s₁ } case right $v₂ { s₂ }]) *)
                      -> var -> nnrs_stmt
                      -> var -> nnrs_stmt -> nnrs_stmt
    .

    (** [nnrs] is composed of the statement evaluating the query
        and the variable containing the result of the evaluation *)
    Definition nnrs : Set := (nnrs_stmt * var).

  End Syntax.

  Section dec.
    Context {fruntime:foreign_runtime}.

    Global Instance nnrs_expr_eqdec : EqDec nnrs_expr eq.
    Proof.
      change (forall x y : nnrs_expr,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply binary_op_eqdec | apply unary_op_eqdec
                   | apply data_eqdec | apply string_eqdec].
      - decide equality; apply string_dec.
    Defined.

    Global Instance nnrs_stmt_eqdec : EqDec nnrs_stmt eq.
    Proof.
      change (forall x y : nnrs_stmt,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply nnrs_expr_eqdec | apply string_eqdec].
    Defined.

    Global Instance nnrs_eqdec : EqDec nnrs eq.
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

    Fixpoint nnrs_exprIsCore (e:nnrs_expr) : Prop :=
      match e with
      | NNRSGetConstant _ => True
      | NNRSVar _ => True
      | NNRSConst _ => True
      | NNRSBinop _ e1 e2 => nnrs_exprIsCore e1 /\ nnrs_exprIsCore e2
      | NNRSUnop _ e1 => nnrs_exprIsCore e1
      | NNRSGroupBy _ _ _ => False
      end.

    Fixpoint nnrs_stmtIsCore (s:nnrs_stmt) : Prop :=
      match s with
      | NNRSSeq s1 s2 =>
        nnrs_stmtIsCore s1 /\ nnrs_stmtIsCore s2
      | NNRSLet _ e s1 =>
        nnrs_exprIsCore e /\ nnrs_stmtIsCore s1
      | NNRSLetMut _ s1 s2 =>
        nnrs_stmtIsCore s1 /\ nnrs_stmtIsCore s2
      | NNRSLetMutColl _ s1 s2 =>
        nnrs_stmtIsCore s1 /\ nnrs_stmtIsCore s2
      | NNRSAssign _ e =>
        nnrs_exprIsCore e
      | NNRSPush _ e =>
        nnrs_exprIsCore e
      | NNRSFor _ e s1 =>
        nnrs_exprIsCore e /\ nnrs_stmtIsCore s1
      | NNRSIf e s1 s2 =>
        nnrs_exprIsCore e /\ nnrs_stmtIsCore s1 /\ nnrs_stmtIsCore s2
      | NNRSEither e _ s1 _ s2 =>
        nnrs_exprIsCore e /\ nnrs_stmtIsCore s1 /\ nnrs_stmtIsCore s2
      end .

    Definition nnrsIsCore (sr:nnrs) := nnrs_stmtIsCore (fst sr).

    Definition nnrs_core : Set := {sr:nnrs | nnrsIsCore sr}.

    Definition nnrs_core_to_nnrs (sr:nnrs_core) : nnrs :=
      proj1_sig sr.

    Section ext.

      Lemma nnrs_exprIsCore_ext (e:nnrs_expr) (pf1 pf2:nnrs_exprIsCore e) : pf1 = pf2.
      Proof.
        induction e; simpl in *;
          try (destruct pf1; destruct pf2; trivial);
          try f_equal; auto.
      Qed.

      Lemma nnrs_stmtIsCore_ext (s:nnrs_stmt) (pf1 pf2:nnrs_stmtIsCore s) : pf1 = pf2.
      Proof.
        induction s; simpl in *;
          try (destruct pf1; destruct pf2; trivial);
          try (destruct a; destruct a0);
          try f_equal; eauto;
            try eapply nnrs_exprIsCore_ext; eauto
            ; try f_equal; eauto.
      Qed.

      Lemma nnrsIsCore_ext (e:nnrs) (pf1 pf2:nnrsIsCore e) : pf1 = pf2.
      Proof.
        apply nnrs_stmtIsCore_ext.
      Qed.

      Lemma nnrs_core_ext e (pf1 pf2:nnrsIsCore e) :
        exist _ e pf1 = exist _ e pf2.
      Proof.
        f_equal; apply nnrsIsCore_ext.
      Qed.

      Lemma nnrs_core_fequal (e1 e2:nnrs_core) :
        proj1_sig e1 = proj1_sig e2 -> e1 = e2.
      Proof.
        destruct e1; destruct e2; simpl; intros eqq.
        destruct eqq.
        apply nnrs_core_ext.
      Qed.

    End ext.
    
    Section dec.

      Lemma nnrs_exprIsCore_dec (e:nnrs_expr) :
        {nnrs_exprIsCore e} + {~ nnrs_exprIsCore e}.
      Proof.
        induction e; simpl; try eauto 3.
        destruct IHe1.
        - destruct IHe2; [left|right]; intuition.
        - right; intuition.
      Defined.

      Lemma nnrs_stmtIsCore_dec (s:nnrs_stmt) :
        {nnrs_stmtIsCore s} + {~ nnrs_stmtIsCore s}.
      Proof.
        induction s; simpl.
        - destruct IHs1.
          + destruct IHs2; [left|right]; intuition.
          + right; intuition.
        - destruct (nnrs_exprIsCore_dec n).
          + destruct IHs; [left|right]; intuition.
          + right; intuition.
        - destruct IHs1.
          + destruct IHs2; [left|right]; intuition.
          + right; intuition.
        - destruct IHs1.
          + destruct IHs2; [left|right]; intuition.
          + right; intuition.
        - apply (nnrs_exprIsCore_dec n).
        - apply (nnrs_exprIsCore_dec n).
        - destruct (nnrs_exprIsCore_dec n).
          + destruct IHs; [left|right]; intuition.
          + right; intuition.
        - destruct (nnrs_exprIsCore_dec n).
          + destruct IHs1.
            * destruct IHs2; [left|right]; intuition.
            * right; intuition.
          + right; intuition.
        - destruct (nnrs_exprIsCore_dec n).
          + destruct IHs1.
            * destruct IHs2; [left|right]; intuition.
            * right; intuition.
          + right; intuition.
      Defined.

      Lemma nnrsIsCore_dec (sr:nnrs) :
        {nnrsIsCore sr} + {~ nnrsIsCore sr}.
      Proof.
        apply nnrs_stmtIsCore_dec.
      Defined.

      Global Instance nnrs_core_eqdec : EqDec nnrs_core eq.
    Proof.
      intros x y.
      destruct x as [x xpf]; destruct y as [y ypf].
      destruct (x == y).
      - left. apply nnrs_core_fequal; simpl; trivial.
      - right. inversion 1; congruence.
    Defined.

    End dec.

End Core.

Section Env.
  Context {fruntime:foreign_runtime}.

  (* bindings that may or may not be initialized (defined) *)
  Definition pd_bindings := list (string*option data).
  Definition mc_bindings := list (string*list data).
  Definition md_bindings := list (string*option data).

End Env.

End NNRS.

Tactic Notation "nnrs_expr_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NNRSGetConstant"%string
  | Case_aux c "NNRSVar"%string
  | Case_aux c "NNRSConst"%string
  | Case_aux c "NNRSBinop"%string
  | Case_aux c "NNRSUnop"%string
  | Case_aux c "NNRSGroupBy"%string].

Tactic Notation "nnrs_stmt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NNRSSeq"%string
  | Case_aux c "NNRSLet"%string
  | Case_aux c "NNRSLetMut"%string
  | Case_aux c "NNRSLetMutColl"%string
  | Case_aux c "NNRSAssign"%string
  | Case_aux c "NNRSPush"%string
  | Case_aux c "NNRSFor"%string
  | Case_aux c "NNRSIf"%string
  | Case_aux c "NNRSEither"%string].

Delimit Scope nnrs with nnrs_scope.
