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

(** NNRCimpish is a variant of the named nested relational calculus
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

Section NNRCimpish.
  Section Syntax.

    Context {fruntime:foreign_runtime}.
    
    Inductive nnrc_impish_expr :=
    | NNRCimpishGetConstant : var -> nnrc_impish_expr                                   (**r global variable lookup ([$$v]) *)
    | NNRCimpishVar : var -> nnrc_impish_expr                                           (**r local variable lookup ([$v])*)
    | NNRCimpishConst : data -> nnrc_impish_expr                                        (**r constant data ([d]) *)
    | NNRCimpishBinop : binary_op -> nnrc_impish_expr -> nnrc_impish_expr -> nnrc_impish_expr (**r binary operator ([e₁ ⊠ e₂]) *)
    | NNRCimpishUnop : unary_op -> nnrc_impish_expr -> nnrc_impish_expr                    (**r unary operator ([⊞ e]) *)
    | NNRCimpishGroupBy : string -> list string -> nnrc_impish_expr -> nnrc_impish_expr    (**r group by expression ([e groupby g fields]) -- only in full NNRC *)
    .

    Inductive nnrc_impish_stmt :=
    | NNRCimpishSeq : nnrc_impish_stmt -> nnrc_impish_stmt -> nnrc_impish_stmt                    (**r sequence ([s₁; s₂]]) *)
    (* This creates a mutable data holder, and evaluates the first
       statement with it bound to the given variable.  It then freezes
       the variable (makes it contain normal data) and evaluates the second
       statement with the variable bound to the normal data version *)
    | NNRCimpishLet : var -> nnrc_impish_expr -> nnrc_impish_stmt -> nnrc_impish_stmt (**r variable declaration ([var $v := e₁; s₂]) *)
    | NNRCimpishLetMut : var -> nnrc_impish_stmt -> nnrc_impish_stmt -> nnrc_impish_stmt (**r variable declaration ([var $v; s₁; s₂]) *)
    (* This creates a mutable collection, and evaluates the first
       statement with it bound to the given variable.  It then freezes
       the collection (makes it a normal bag) and evaluates the second
       statement with the variable bound to the bag version *)
    | NNRCimpishLetMutColl : var -> nnrc_impish_stmt -> nnrc_impish_stmt -> nnrc_impish_stmt    (**r mutable collection declaration ([var $v := {}; s1 ; s2]) *)
    | NNRCimpishAssign : var -> nnrc_impish_expr -> nnrc_impish_stmt                           (**r variable assignent ([$v := e]) *)
    (* pushes to a variable that holds a mutable collection *)
    | NNRCimpishPush : var -> nnrc_impish_expr -> nnrc_impish_stmt                             (**r push item in mutable collection ([push e in $v]) *)
    | NNRCimpishFor : var -> nnrc_impish_expr -> nnrc_impish_stmt -> nnrc_impish_stmt             (**r for loop ([for ($v in e₁) { s₂ }]) *)
    | NNRCimpishIf : nnrc_impish_expr -> nnrc_impish_stmt -> nnrc_impish_stmt -> nnrc_impish_stmt    (**r conditional ([if e₁ { s₂ } else { s₃ }]) *)
    | NNRCimpishEither : nnrc_impish_expr                                                   (**r case expression ([either e case left $v₁ { s₁ } case right $v₂ { s₂ }]) *)
                      -> var -> nnrc_impish_stmt
                      -> var -> nnrc_impish_stmt -> nnrc_impish_stmt
    .

    (** [nnrc_impish] is composed of the statement evaluating the query
        and the variable containing the result of the evaluation *)
    Definition nnrc_impish : Set := (nnrc_impish_stmt * var).

  End Syntax.

  Section dec.
    Context {fruntime:foreign_runtime}.

    Global Instance nnrc_impish_expr_eqdec : EqDec nnrc_impish_expr eq.
    Proof.
      change (forall x y : nnrc_impish_expr,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply binary_op_eqdec | apply unary_op_eqdec
                   | apply data_eqdec | apply string_eqdec].
      - decide equality; apply string_dec.
    Defined.

    Global Instance nnrc_impish_stmt_eqdec : EqDec nnrc_impish_stmt eq.
    Proof.
      change (forall x y : nnrc_impish_stmt,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply nnrc_impish_expr_eqdec | apply string_eqdec].
    Defined.

    Global Instance nnrc_impish_eqdec : EqDec nnrc_impish eq.
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

    Fixpoint nnrc_impish_exprIsCore (e:nnrc_impish_expr) : Prop :=
      match e with
      | NNRCimpishGetConstant _ => True
      | NNRCimpishVar _ => True
      | NNRCimpishConst _ => True
      | NNRCimpishBinop _ e1 e2 => nnrc_impish_exprIsCore e1 /\ nnrc_impish_exprIsCore e2
      | NNRCimpishUnop _ e1 => nnrc_impish_exprIsCore e1
      | NNRCimpishGroupBy _ _ _ => False
      end.

    Fixpoint nnrc_impish_stmtIsCore (s:nnrc_impish_stmt) : Prop :=
      match s with
      | NNRCimpishSeq s1 s2 =>
        nnrc_impish_stmtIsCore s1 /\ nnrc_impish_stmtIsCore s2
      | NNRCimpishLet _ e s1 =>
        nnrc_impish_exprIsCore e /\ nnrc_impish_stmtIsCore s1
      | NNRCimpishLetMut _ s1 s2 =>
        nnrc_impish_stmtIsCore s1 /\ nnrc_impish_stmtIsCore s2
      | NNRCimpishLetMutColl _ s1 s2 =>
        nnrc_impish_stmtIsCore s1 /\ nnrc_impish_stmtIsCore s2
      | NNRCimpishAssign _ e =>
        nnrc_impish_exprIsCore e
      | NNRCimpishPush _ e =>
        nnrc_impish_exprIsCore e
      | NNRCimpishFor _ e s1 =>
        nnrc_impish_exprIsCore e /\ nnrc_impish_stmtIsCore s1
      | NNRCimpishIf e s1 s2 =>
        nnrc_impish_exprIsCore e /\ nnrc_impish_stmtIsCore s1 /\ nnrc_impish_stmtIsCore s2
      | NNRCimpishEither e _ s1 _ s2 =>
        nnrc_impish_exprIsCore e /\ nnrc_impish_stmtIsCore s1 /\ nnrc_impish_stmtIsCore s2
      end .

    Definition nnrc_impishIsCore (sr:nnrc_impish) := nnrc_impish_stmtIsCore (fst sr).

    Definition nnrc_impish_core : Set := {sr:nnrc_impish | nnrc_impishIsCore sr}.

    Definition nnrc_impish_core_to_nnrc_impish (sr:nnrc_impish_core) : nnrc_impish :=
      proj1_sig sr.

    Section ext.

      Lemma nnrc_impish_exprIsCore_ext (e:nnrc_impish_expr) (pf1 pf2:nnrc_impish_exprIsCore e) : pf1 = pf2.
      Proof.
        induction e; simpl in *;
          try (destruct pf1; destruct pf2; trivial);
          try f_equal; auto.
      Qed.

      Lemma nnrc_impish_stmtIsCore_ext (s:nnrc_impish_stmt) (pf1 pf2:nnrc_impish_stmtIsCore s) : pf1 = pf2.
      Proof.
        induction s; simpl in *;
          try (destruct pf1; destruct pf2; trivial);
          try (destruct a; destruct a0);
          try f_equal; eauto;
            try eapply nnrc_impish_exprIsCore_ext; eauto
            ; try f_equal; eauto.
      Qed.

      Lemma nnrc_impishIsCore_ext (e:nnrc_impish) (pf1 pf2:nnrc_impishIsCore e) : pf1 = pf2.
      Proof.
        apply nnrc_impish_stmtIsCore_ext.
      Qed.

      Lemma nnrc_impish_core_ext e (pf1 pf2:nnrc_impishIsCore e) :
        exist _ e pf1 = exist _ e pf2.
      Proof.
        f_equal; apply nnrc_impishIsCore_ext.
      Qed.

      Lemma nnrc_impish_core_fequal (e1 e2:nnrc_impish_core) :
        proj1_sig e1 = proj1_sig e2 -> e1 = e2.
      Proof.
        destruct e1; destruct e2; simpl; intros eqq.
        destruct eqq.
        apply nnrc_impish_core_ext.
      Qed.

    End ext.
    
    Section dec.

      Lemma nnrc_impish_exprIsCore_dec (e:nnrc_impish_expr) :
        {nnrc_impish_exprIsCore e} + {~ nnrc_impish_exprIsCore e}.
      Proof.
        induction e; simpl; try eauto 3.
        destruct IHe1.
        - destruct IHe2; [left|right]; intuition.
        - right; intuition.
      Defined.

      Lemma nnrc_impish_stmtIsCore_dec (s:nnrc_impish_stmt) :
        {nnrc_impish_stmtIsCore s} + {~ nnrc_impish_stmtIsCore s}.
      Proof.
        induction s; simpl.
        - destruct IHs1.
          + destruct IHs2; [left|right]; intuition.
          + right; intuition.
        - destruct (nnrc_impish_exprIsCore_dec n).
          + destruct IHs; [left|right]; intuition.
          + right; intuition.
        - destruct IHs1.
          + destruct IHs2; [left|right]; intuition.
          + right; intuition.
        - destruct IHs1.
          + destruct IHs2; [left|right]; intuition.
          + right; intuition.
        - apply (nnrc_impish_exprIsCore_dec n).
        - apply (nnrc_impish_exprIsCore_dec n).
        - destruct (nnrc_impish_exprIsCore_dec n).
          + destruct IHs; [left|right]; intuition.
          + right; intuition.
        - destruct (nnrc_impish_exprIsCore_dec n).
          + destruct IHs1.
            * destruct IHs2; [left|right]; intuition.
            * right; intuition.
          + right; intuition.
        - destruct (nnrc_impish_exprIsCore_dec n).
          + destruct IHs1.
            * destruct IHs2; [left|right]; intuition.
            * right; intuition.
          + right; intuition.
      Defined.

      Lemma nnrc_impishIsCore_dec (sr:nnrc_impish) :
        {nnrc_impishIsCore sr} + {~ nnrc_impishIsCore sr}.
      Proof.
        apply nnrc_impish_stmtIsCore_dec.
      Defined.

      Global Instance nnrc_impish_core_eqdec : EqDec nnrc_impish_core eq.
    Proof.
      intros x y.
      destruct x as [x xpf]; destruct y as [y ypf].
      destruct (x == y).
      - left. apply nnrc_impish_core_fequal; simpl; trivial.
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

End NNRCimpish.

Tactic Notation "nnrc_impish_expr_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NNRCimpishGetConstant"%string
  | Case_aux c "NNRCimpishVar"%string
  | Case_aux c "NNRCimpishConst"%string
  | Case_aux c "NNRCimpishBinop"%string
  | Case_aux c "NNRCimpishUnop"%string
  | Case_aux c "NNRCimpishGroupBy"%string].

Tactic Notation "nnrc_impish_stmt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NNRCimpishSeq"%string
  | Case_aux c "NNRCimpishLet"%string
  | Case_aux c "NNRCimpishLetMut"%string
  | Case_aux c "NNRCimpishLetMutColl"%string
  | Case_aux c "NNRCimpishAssign"%string
  | Case_aux c "NNRCimpishPush"%string
  | Case_aux c "NNRCimpishFor"%string
  | Case_aux c "NNRCimpishIf"%string
  | Case_aux c "NNRCimpishEither"%string].

Delimit Scope nnrc_impish with nnrc_impish_scope.
