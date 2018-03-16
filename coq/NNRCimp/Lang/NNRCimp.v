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

Section NNRCimp.
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

  Section Syntax.

    Context {fruntime:foreign_runtime}.
    
    Inductive nnrc_imp_expr :=
    | NNRCimpGetConstant : var -> nnrc_imp_expr                                   (**r global variable lookup ([$$v]) *)
    | NNRCimpVar : var -> nnrc_imp_expr                                           (**r local variable lookup ([$v])*)
    | NNRCimpConst : data -> nnrc_imp_expr                                        (**r constant data ([d]) *)
    | NNRCimpBinop : binary_op -> nnrc_imp_expr -> nnrc_imp_expr -> nnrc_imp_expr (**r binary operator ([e₁ ⊠ e₂]) *)
    | NNRCimpUnop : unary_op -> nnrc_imp_expr -> nnrc_imp_expr                    (**r unary operator ([⊞ e]) *)
    | NNRCimpGroupBy : string -> list string -> nnrc_imp_expr -> nnrc_imp_expr    (**r group by expression ([e groupby g fields]) -- only in full NNRC *)
    .

    Inductive nnrc_imp_stmt :=
    | NNRCimpSeq : nnrc_imp_stmt -> nnrc_imp_stmt -> nnrc_imp_stmt                    (**r sequence ([s₁; s₂]]) *)
    (* This creates a mutable data holder, and evaluates the first
       statement with it bound to the given variable.  It then freezes
       the variable (makes it contain normal data) and evaluates the second
       statement with the variable bound to the normal data version *)
    | NNRCimpLet : var -> nnrc_imp_expr -> nnrc_imp_stmt -> nnrc_imp_stmt (**r variable declaration ([var $v := e₁; s₂]) *)
    | NNRCimpLetMut : var -> nnrc_imp_stmt -> nnrc_imp_stmt -> nnrc_imp_stmt (**r variable declaration ([var $v; s₁; s₂]) *)
    (* This creates a mutable collection, and evaluates the first
       statement with it bound to the given variable.  It then freezes
       the collection (makes it a normal bag) and evaluates the second
       statement with the variable bound to the bag version *)
    | NNRCimpLetMutColl : var -> nnrc_imp_stmt -> nnrc_imp_stmt -> nnrc_imp_stmt    (**r mutable collection declaration ([var $v := {}; s1 ; s2]) *)
    | NNRCimpAssign : var -> nnrc_imp_expr -> nnrc_imp_stmt                           (**r variable assignent ([$v := e]) *)
    (* pushes to a variable that holds a mutable collection *)
    | NNRCimpPush : var -> nnrc_imp_expr -> nnrc_imp_stmt                             (**r push item in mutable collection ([push e in $v]) *)
    | NNRCimpFor : var -> nnrc_imp_expr -> nnrc_imp_stmt -> nnrc_imp_stmt             (**r for loop ([for ($v in e₁) { s₂ }]) *)
    | NNRCimpIf : nnrc_imp_expr -> nnrc_imp_stmt -> nnrc_imp_stmt -> nnrc_imp_stmt    (**r conditional ([if e₁ { s₂ } else { s₃ }]) *)
    | NNRCimpEither : nnrc_imp_expr                                                   (**r case expression ([either e case left $v₁ { s₁ } case right $v₂ { s₂ }]) *)
                      -> var -> nnrc_imp_stmt
                      -> var -> nnrc_imp_stmt -> nnrc_imp_stmt
    .

    (** [nnrc_imp] is composed of the statement evaluating the query
        and the variable containing the result of the evaluation *)
    Definition nnrc_imp : Set := (nnrc_imp_stmt * var).

  End Syntax.

  Section dec.
    Context {fruntime:foreign_runtime}.

    Global Instance nnrc_imp_expr_eqdec : EqDec nnrc_imp_expr eq.
    Proof.
      change (forall x y : nnrc_imp_expr,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply binary_op_eqdec | apply unary_op_eqdec
                   | apply data_eqdec | apply string_eqdec].
      - decide equality; apply string_dec.
    Defined.

    Global Instance nnrc_imp_stmt_eqdec : EqDec nnrc_imp_stmt eq.
    Proof.
      change (forall x y : nnrc_imp_stmt,  {x = y} + {x <> y}).
      decide equality;
        try solve [apply nnrc_imp_expr_eqdec | apply string_eqdec].
    Defined.

    Global Instance nnrc_imp_eqdec : EqDec nnrc_imp eq.
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

    Fixpoint nnrc_imp_exprIsCore (e:nnrc_imp_expr) : Prop :=
      match e with
      | NNRCimpGetConstant _ => True
      | NNRCimpVar _ => True
      | NNRCimpConst _ => True
      | NNRCimpBinop _ e1 e2 => nnrc_imp_exprIsCore e1 /\ nnrc_imp_exprIsCore e2
      | NNRCimpUnop _ e1 => nnrc_imp_exprIsCore e1
      | NNRCimpGroupBy _ _ _ => False
      end.

    Fixpoint nnrc_imp_stmtIsCore (s:nnrc_imp_stmt) : Prop :=
      match s with
      | NNRCimpSeq s1 s2 =>
        nnrc_imp_stmtIsCore s1 /\ nnrc_imp_stmtIsCore s2
      | NNRCimpLet _ e s1 =>
        nnrc_imp_exprIsCore e /\ nnrc_imp_stmtIsCore s1
      | NNRCimpLetMut _ s1 s2 =>
        nnrc_imp_stmtIsCore s1 /\ nnrc_imp_stmtIsCore s2
      | NNRCimpLetMutColl _ s1 s2 =>
        nnrc_imp_stmtIsCore s1 /\ nnrc_imp_stmtIsCore s2
      | NNRCimpAssign _ e =>
        nnrc_imp_exprIsCore e
      | NNRCimpPush _ e =>
        nnrc_imp_exprIsCore e
      | NNRCimpFor _ e s1 =>
        nnrc_imp_exprIsCore e /\ nnrc_imp_stmtIsCore s1
      | NNRCimpIf e s1 s2 =>
        nnrc_imp_exprIsCore e /\ nnrc_imp_stmtIsCore s1 /\ nnrc_imp_stmtIsCore s2
      | NNRCimpEither e _ s1 _ s2 =>
        nnrc_imp_exprIsCore e /\ nnrc_imp_stmtIsCore s1 /\ nnrc_imp_stmtIsCore s2
      end .

    Definition nnrc_impIsCore (sr:nnrc_imp) := nnrc_imp_stmtIsCore (fst sr).

    Definition nnrc_imp_core : Set := {sr:nnrc_imp | nnrc_impIsCore sr}.

    Definition nnrc_imp_core_to_nnrc_imp (sr:nnrc_imp_core) : nnrc_imp :=
      proj1_sig sr.

    Section ext.

      Lemma nnrc_imp_exprIsCore_ext (e:nnrc_imp_expr) (pf1 pf2:nnrc_imp_exprIsCore e) : pf1 = pf2.
      Proof.
        induction e; simpl in *;
          try (destruct pf1; destruct pf2; trivial);
          try f_equal; auto.
      Qed.

      Lemma nnrc_imp_stmtIsCore_ext (s:nnrc_imp_stmt) (pf1 pf2:nnrc_imp_stmtIsCore s) : pf1 = pf2.
      Proof.
        induction s; simpl in *;
          try (destruct pf1; destruct pf2; trivial);
          try (destruct a; destruct a0);
          try f_equal; eauto;
            try eapply nnrc_imp_exprIsCore_ext; eauto
            ; try f_equal; eauto.
      Qed.

      Lemma nnrc_impIsCore_ext (e:nnrc_imp) (pf1 pf2:nnrc_impIsCore e) : pf1 = pf2.
      Proof.
        apply nnrc_imp_stmtIsCore_ext.
      Qed.

      Lemma nnrc_imp_core_ext e (pf1 pf2:nnrc_impIsCore e) :
        exist _ e pf1 = exist _ e pf2.
      Proof.
        f_equal; apply nnrc_impIsCore_ext.
      Qed.

      Lemma nnrc_imp_core_fequal (e1 e2:nnrc_imp_core) :
        proj1_sig e1 = proj1_sig e2 -> e1 = e2.
      Proof.
        destruct e1; destruct e2; simpl; intros eqq.
        destruct eqq.
        apply nnrc_imp_core_ext.
      Qed.

    End ext.
    
    Section dec.

      Lemma nnrc_imp_exprIsCore_dec (e:nnrc_imp_expr) :
        {nnrc_imp_exprIsCore e} + {~ nnrc_imp_exprIsCore e}.
      Proof.
        induction e; simpl; try eauto 3.
        destruct IHe1.
        - destruct IHe2; [left|right]; intuition.
        - right; intuition.
      Defined.

      Lemma nnrc_imp_stmtIsCore_dec (s:nnrc_imp_stmt) :
        {nnrc_imp_stmtIsCore s} + {~ nnrc_imp_stmtIsCore s}.
      Proof.
        induction s; simpl.
        - destruct IHs1.
          + destruct IHs2; [left|right]; intuition.
          + right; intuition.
        - destruct (nnrc_imp_exprIsCore_dec n).
          + destruct IHs; [left|right]; intuition.
          + right; intuition.
        - destruct IHs1.
          + destruct IHs2; [left|right]; intuition.
          + right; intuition.
        - destruct IHs1.
          + destruct IHs2; [left|right]; intuition.
          + right; intuition.
        - apply (nnrc_imp_exprIsCore_dec n).
        - apply (nnrc_imp_exprIsCore_dec n).
        - destruct (nnrc_imp_exprIsCore_dec n).
          + destruct IHs; [left|right]; intuition.
          + right; intuition.
        - destruct (nnrc_imp_exprIsCore_dec n).
          + destruct IHs1.
            * destruct IHs2; [left|right]; intuition.
            * right; intuition.
          + right; intuition.
        - destruct (nnrc_imp_exprIsCore_dec n).
          + destruct IHs1.
            * destruct IHs2; [left|right]; intuition.
            * right; intuition.
          + right; intuition.
      Defined.

      Lemma nnrc_impIsCore_dec (sr:nnrc_imp) :
        {nnrc_impIsCore sr} + {~ nnrc_impIsCore sr}.
      Proof.
        apply nnrc_imp_stmtIsCore_dec.
      Defined.

      Global Instance nnrc_imp_core_eqdec : EqDec nnrc_imp_core eq.
    Proof.
      intros x y.
      destruct x as [x xpf]; destruct y as [y ypf].
      destruct (x == y).
      - left. apply nnrc_imp_core_fequal; simpl; trivial.
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

End NNRCimp.

Tactic Notation "nnrc_imp_expr_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NNRCimpGetConstant"%string
  | Case_aux c "NNRCimpVar"%string
  | Case_aux c "NNRCimpConst"%string
  | Case_aux c "NNRCimpBinop"%string
  | Case_aux c "NNRCimpUnop"%string
  | Case_aux c "NNRCimpGroupBy"%string].

Tactic Notation "nnrc_imp_stmt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NNRCimpSeq"%string
  | Case_aux c "NNRCimpLet"%string
  | Case_aux c "NNRCimpLetMut"%string
  | Case_aux c "NNRCimpLetMutColl"%string
  | Case_aux c "NNRCimpAssign"%string
  | Case_aux c "NNRCimpPush"%string
  | Case_aux c "NNRCimpFor"%string
  | Case_aux c "NNRCimpIf"%string
  | Case_aux c "NNRCimpEither"%string].

Delimit Scope nnrc_imp with nnrc_imp_scope.
