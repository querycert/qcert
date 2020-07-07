(*
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

(** Imp is a simple imperative intermediate language. *)

Require Import String.
Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Arith.
Require Import Max.
Require Import Bool.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.

Section Imp.

  Section Syntax.
    Context {Constant: Type}.
    Context {Op: Type}.
    Context {Runtime: Type}.

    Definition var := string.

    Unset Elimination Schemes.
  
    Inductive imp_expr :=
    | ImpExprError : string -> imp_expr                          (**r raises an error *)
    | ImpExprVar : var -> imp_expr                               (**r local variable lookup ([$v])*)
    | ImpExprConst : Constant -> imp_expr                        (**r constant data ([d]) *)
    | ImpExprOp : Op -> list imp_expr -> imp_expr                (**r operator ([e₁ ⊠ e₂]) *)
    | ImpExprRuntimeCall : Runtime -> list imp_expr -> imp_expr  (**r runtime function call *)
  (*| ImpExprIf : imp_expr -> imp_expr -> imp_expr -> imp_expr *)(* XXX Useful? Used in Qcert JS runtime *)
    .

    Inductive imp_stmt :=
    | ImpStmtBlock : list (var * option imp_expr) -> list imp_stmt -> imp_stmt (**r block ([[{let x=e₁; let x=e₂; s₁; s₂}]]) *)
    | ImpStmtAssign : var -> imp_expr -> imp_stmt                              (**r variable assignent ([$v := e]) *)
    | ImpStmtFor : var -> imp_expr -> imp_stmt -> imp_stmt                     (**r for loop ([for ($v in e₁) { s₂ }]) *)
    | ImpStmtForRange : var -> imp_expr -> imp_expr -> imp_stmt -> imp_stmt    (**r for loop ([for ($v = e₁ to e₂) { s₂ }]) *)
    | ImpStmtIf : imp_expr -> imp_stmt -> imp_stmt -> imp_stmt                 (**r conditional ([if e₁ { s₂ } else { s₃ }]) *)
    .

    Set Elimination Schemes.

    (* input variable + statements + returned variable *)
    Inductive imp_function :=
    | ImpFun : var -> imp_stmt -> var -> imp_function
    .

    (** [imp] is composed of a list of function declarations *)
    Inductive imp :=
    | ImpLib : list (string * imp_function) -> imp.

    Section RectInd.
      (** Induction principles used as backbone for inductive proofs on imp *)
      Definition imp_expr_rect (P : imp_expr -> Type)
                 (ferror : forall v : string, P (ImpExprError v))
                 (fvar : forall v : string, P (ImpExprVar v))
                 (fconst : forall d : Constant, P (ImpExprConst d))
                 (fop : forall op : Op, forall el : list imp_expr,
                       Forallt P el -> P (ImpExprOp op el))
                 (fruntime : forall rt : Runtime, forall el : list imp_expr,
                       Forallt P el -> P (ImpExprRuntimeCall rt el))
        :=
          fix F (e : imp_expr) : P e :=
            match e as e0 return (P e0) with
            | ImpExprError msg => ferror msg
            | ImpExprVar v => fvar v
            | ImpExprConst d => fconst d
            | ImpExprOp op el =>
              fop op el ((fix F2 (c : list imp_expr) : Forallt P c :=
                            match c as c0 with
                            | nil => Forallt_nil _
                            | cons d c0 => @Forallt_cons _ P d c0 (F d) (F2 c0)
                            end) el)
            | ImpExprRuntimeCall rt el =>
              fruntime rt el ((fix F3 (c : list imp_expr) : Forallt P c :=
                                 match c as c0 with
                                 | nil => Forallt_nil _
                                 | cons d c0 => @Forallt_cons _ P d c0 (F d) (F3 c0)
                                 end) el)
            end.

      Definition imp_expr_ind (P : imp_expr -> Prop)
                 (ferror : forall v : string, P (ImpExprError v))
                 (fvar : forall v : string, P (ImpExprVar v))
                 (fconst : forall d : Constant, P (ImpExprConst d))
                 (fop : forall op : Op, forall el : list imp_expr,
                       Forall P el -> P (ImpExprOp op el))
                 (fruntime : forall rt : Runtime, forall el : list imp_expr,
                       Forall P el -> P (ImpExprRuntimeCall rt el))
        :=
          fix F (e : imp_expr) : P e :=
            match e as e0 return (P e0) with
            | ImpExprError msg => ferror msg
            | ImpExprVar v => fvar v
            | ImpExprConst d => fconst d
            | ImpExprOp op el =>
              fop op el ((fix F1 (c : list imp_expr) : Forall P c :=
                            match c as c0 with
                            | nil => Forall_nil _
                            | cons d c0 => @Forall_cons _ P d c0 (F d) (F1 c0)
                            end) el)
            | ImpExprRuntimeCall rt el =>
              fruntime rt el ((fix F2 (c : list imp_expr) : Forall P c :=
                                 match c as c0 with
                                 | nil => Forall_nil _
                                 | cons d c0 => @Forall_cons _ P d c0 (F d) (F2 c0)
                                 end) el)
            end.

      Definition imp_expr_rec (P:imp_expr->Set) := imp_expr_rect P.

      Definition imp_stmt_rect (P : imp_stmt -> Type)
                 (fblock : forall el : list (var * option imp_expr), forall sl : list imp_stmt,
                       Forallt P sl -> P (ImpStmtBlock el sl))
                 (fassign : forall v : string, forall e : imp_expr, P (ImpStmtAssign v e))
                 (ffor : forall v : string, forall e : imp_expr, forall s : imp_stmt, P s -> P (ImpStmtFor v e s))
                 (fforrange : forall v : string, forall e1 e2 : imp_expr, forall s : imp_stmt, P s -> P (ImpStmtForRange v e1 e2 s))
                 (fif : forall e : imp_expr, forall s1 s2 : imp_stmt, P s1 -> P s2 -> P (ImpStmtIf e s1 s2))
        :=
          fix F (e : imp_stmt) : P e :=
            match e as e0 return (P e0) with
            | ImpStmtBlock el sl =>
              fblock el sl ((fix F1 (c : list imp_stmt) : Forallt P c :=
                               match c as c0 with
                               | nil => Forallt_nil _
                               | cons d c0 => @Forallt_cons _ P d c0 (F d) (F1 c0)
                               end) sl)
            | ImpStmtAssign v e => fassign v e
            | ImpStmtFor v e s => ffor v e s (F s)
            | ImpStmtForRange v e1 e2 s => fforrange v e1 e2 s (F s)
            | ImpStmtIf e s1 s2 => fif e s1 s2 (F s1) (F s2)
            end.

      Definition imp_stmt_ind (P : imp_stmt -> Prop)
                 (fblock : forall el : list (var * option imp_expr), forall sl : list imp_stmt,
                       Forall P sl -> P (ImpStmtBlock el sl))
                 (fassign : forall v : string, forall e : imp_expr, P (ImpStmtAssign v e))
                 (ffor : forall v : string, forall e : imp_expr, forall s : imp_stmt, P s -> P (ImpStmtFor v e s))
                 (fforrange : forall v : string, forall e1 e2 : imp_expr, forall s : imp_stmt, P s -> P (ImpStmtForRange v e1 e2 s))
                 (fif : forall e : imp_expr, forall s1 s2 : imp_stmt, P s1 -> P s2 -> P (ImpStmtIf e s1 s2))
        :=
          fix F (e : imp_stmt) : P e :=
            match e as e0 return (P e0) with
            | ImpStmtBlock el sl =>
              fblock el sl ((fix F1 (c : list imp_stmt) : Forall P c :=
                               match c as c0 with
                               | nil => Forall_nil _
                               | cons d c0 => @Forall_cons _ P d c0 (F d) (F1 c0)
                               end) sl)
            | ImpStmtAssign v e => fassign v e
            | ImpStmtFor v e s => ffor v e s (F s)
            | ImpStmtForRange v e1 e2 s => fforrange v e1 e2 s (F s)
            | ImpStmtIf e s1 s2 => fif e s1 s2 (F s1) (F s2)
            end.

      Definition imp_stmt_rec (P:imp_stmt->Set) := imp_stmt_rect P.

    End RectInd.

    Section dec.
      Context {Constant_eqdec: EqDec Constant eq}.
      Context {Op_eqdec: EqDec Op eq}.
      Context {Runtime_eqdec: EqDec Runtime eq}.

      Global Instance imp_expr_eqdec : EqDec imp_expr eq.
      Proof.
        change (forall x y : imp_expr,  {x = y} + {x <> y}).
        decide equality;
          try solve [apply binary_op_eqdec | apply unary_op_eqdec
                     | apply Constant_eqdec | apply Op_eqdec | apply Runtime_eqdec | apply string_eqdec].
        - revert l; induction el; intros; destruct l; simpl in *; try solve[right ;inversion 1].
          left; reflexivity.
          inversion X; subst; clear X.
          elim (X0 i); intros; subst; clear X0.
          + specialize (IHel X1); clear X1.
            elim (IHel l); intros; clear IHel.
            * subst; left; reflexivity.
            * right; congruence.
          + right; congruence.
        - revert l; induction el; intros; destruct l; simpl in *; try solve[right ;inversion 1].
          left; reflexivity.
          inversion X; subst; clear X.
          elim (X0 i); intros; subst; clear X0.
          + specialize (IHel X1); clear X1.
            elim (IHel l); intros; clear IHel.
            * subst; left; reflexivity.
            * right; congruence.
          + right; congruence.
      Defined.

      Global Instance imp_stmt_eqdec : EqDec imp_stmt eq.
      Proof.
        change (forall x y : imp_stmt,  {x = y} + {x <> y}).
        decide equality;
          try solve [apply imp_expr_eqdec | apply string_eqdec | apply option_eqdec].
        - subst; clear l.
          revert l0; induction sl; intros; destruct l0; simpl in *; try solve[right ;inversion 1].
          left; reflexivity.
          inversion X; subst; clear X.
          elim (X0 i); intros; subst; clear X0.
          + specialize (IHsl X1); clear X1.
            elim (IHsl l0); intros; clear IHsl.
            * subst; left; reflexivity.
            * right; congruence.
          + right; congruence.
        - clear X.
          revert l; induction el; intros; destruct l; simpl in *; try solve[right ;inversion 1].
          left; reflexivity.
          destruct a; simpl in *; destruct o; simpl in *;
          destruct p; simpl in *; destruct o; simpl in *.
          + elim (IHel l); intros; clear IHel.
            * elim (imp_expr_eqdec i i0); intros; [|right; congruence].
              assert (i = i0); auto; clear a0; subst;
                destruct (string_dec v v0); subst; [left; reflexivity| right; congruence].
            * right; congruence.
          + right; congruence.
          + right; congruence.
          + elim (IHel l); intros; clear IHel.
            * destruct (string_dec v v0); subst; [left; reflexivity| right; congruence].
            * right; congruence.
      Qed.

      Global Instance imp_function_eqdec : EqDec imp_function eq.
      Proof.
        change (forall x y : imp_function,  {x = y} + {x <> y}).
        decide equality; subst;
          try solve [apply imp_stmt_eqdec | apply string_eqdec | apply option_eqdec].
      Qed.
        
      Global Instance imp_eqdec : EqDec imp eq.
      Proof.
        change (forall x y : imp,  {x = y} + {x <> y}).
        decide equality.
        revert l0; induction l; intros; destruct l0; simpl in *; try solve[right ;inversion 1].
        left; reflexivity.
        destruct a; simpl in *; destruct p; simpl in *.
        + elim (IHl l0); intros; clear IHl.
          * elim (imp_function_eqdec i i0); intros; [|right; congruence].
            assert (i = i0); auto; clear a0; subst;
              destruct (string_dec s s0); subst; [left; reflexivity| right; congruence].
          * right; congruence.
      Qed.
    End dec.

  End Syntax.
End Imp.

Tactic Notation "imp_expr_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ImpExprError"%string
  | Case_aux c "ImpExprVar"%string
  | Case_aux c "ImpExprConst"%string
  | Case_aux c "ImpExprOp"%string
  | Case_aux c "ImpExprRuntimeCall"%string].

Tactic Notation "imp_stmt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ImpStmtBlock"%string
  | Case_aux c "ImpStmtAssign"%string
  | Case_aux c "ImpStmtFor"%string
  | Case_aux c "ImpStmtForRange"%string
  | Case_aux c "ImpStmtIf"%string].

Tactic Notation "imp_function_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ImpFun"%string].

Tactic Notation "imp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ImpLib"%string].


Delimit Scope imp with imp_scope.
