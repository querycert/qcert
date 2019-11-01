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

(** Imp is a small imperative language *)

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

    Context {Data: Type}.
    Context {Op: Type}.
    Context {Runtime: Type}.

    Definition var := string.

    Unset Elimination Schemes.
  
    Inductive imp_expr :=
    | ImpExprError : string -> imp_expr                          (**r raises an error *)
    | ImpExprVar : var -> imp_expr                               (**r local variable lookup ([$v])*)
    | ImpExprConst : Data -> imp_expr                            (**r constant data ([d]) *)
    | ImpExprOp : Op -> list imp_expr -> imp_expr                (**r operator ([e₁ ⊠ e₂]) *)
    | ImpExprRuntimeCall : Runtime -> list imp_expr -> imp_expr  (**r runtime function call *)
  (*| ImpExprIf : imp_expr -> imp_expr -> imp_expr -> imp_expr *)(* XXX Useful? Used in Qcert JS runtime *)
    .

    Set Elimination Schemes.

    Inductive imp_stmt :=
    | ImpStmtBlock : list (var * option imp_expr) -> list imp_stmt -> imp_stmt (**r block ([[{let x=e₁; let x=e₂; s₁; s₂}]]) *)
    | ImpStmtAssign : var -> imp_expr -> imp_stmt                              (**r variable assignent ([$v := e]) *)
    | ImpStmtFor : var -> imp_expr -> imp_stmt -> imp_stmt                     (**r for loop ([for ($v in e₁) { s₂ }]) *)
    | ImpStmtForRange : var -> imp_expr -> imp_expr -> imp_stmt -> imp_stmt    (**r for loop ([for ($v = e₁ to e₂) { s₂ }]) *)
    | ImpStmtIf : imp_expr -> imp_stmt -> imp_stmt -> imp_stmt                 (**r conditional ([if e₁ { s₂ } else { s₃ }]) *)
  (*| ImpStmtBreak : imp_stnt *)(* XXX Possible? Useful? -- Used in Qcert JS runtime *)
    .

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
                 (fconst : forall d : Data, P (ImpExprConst d))
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
                 (fconst : forall d : Data, P (ImpExprConst d))
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
              fop op el ((fix F2 (c : list imp_expr) : Forall P c :=
                            match c as c0 with
                            | nil => Forall_nil _
                            | cons d c0 => @Forall_cons _ P d c0 (F d) (F2 c0)
                            end) el)
            | ImpExprRuntimeCall rt el =>
              fruntime rt el ((fix F3 (c : list imp_expr) : Forall P c :=
                                 match c as c0 with
                                 | nil => Forall_nil _
                                 | cons d c0 => @Forall_cons _ P d c0 (F d) (F3 c0)
                                 end) el)
            end.

      Definition imp_expr_rec (P:imp_expr->Set) := imp_expr_rect P.
  
    End RectInd.
  End Syntax.

  (* Section dec. *)
  (*   Context {fruntime:foreign_runtime}. *)

  (*   Global Instance imp_expr_eqdec : EqDec imp_expr eq. *)
  (*   Proof. *)
  (*     change (forall x y : imp_expr,  {x = y} + {x <> y}). *)
  (*     decide equality; *)
  (*       try solve [apply binary_op_eqdec | apply unary_op_eqdec *)
  (*                  | apply data_eqdec | apply string_eqdec]. *)
  (*     - decide equality; apply string_dec. *)
  (*   Defined. *)

  (*   Global Instance imp_stmt_eqdec : EqDec imp_stmt eq. *)
  (*   Proof. *)
  (*     change (forall x y : imp_stmt,  {x = y} + {x <> y}). *)
  (*     decide equality; *)
  (*       try solve [apply imp_expr_eqdec | apply string_eqdec | apply option_eqdec]. *)
  (*   Defined. *)

  (*   Global Instance imp_eqdec : EqDec imp eq. *)
  (*   Proof. *)
  (*     intros [s1 r1] [s2 r2]. *)
  (*     destruct (r1 == r2). *)
  (*     - destruct (s1 == s2). *)
  (*       + left; congruence. *)
  (*       + right; congruence. *)
  (*     - right; congruence. *)
  (*   Defined. *)
  (* End dec. *)

(* Section Env. *)
(*   Context {fruntime:foreign_runtime}. *)

(*   (* bindings that may or may not be initialized (defined) *) *)
(*   Definition pd_bindings := list (string*option data). *)

(* End Env. *)

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
