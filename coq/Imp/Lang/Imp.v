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

Section Imp.

  Section Syntax.

    Context {Data: Type}.
    Context {Op: Type}.
    Context {Runtime: Type}.

    Definition var := string.

    Inductive imp_expr :=
    | ImpExprVar : var -> imp_expr                               (**r local variable lookup ([$v])*)
    | ImpExprConst : Data -> imp_expr                            (**r constant data ([d]) *)
    | ImpExprOp : Op -> list imp_expr -> imp_expr                (**r operator ([e₁ ⊠ e₂]) *)
    | ImpExprCall : string -> list imp_expr -> imp_expr          (**r function call *)
    | ImpExprRuntimeCall : Runtime -> list imp_expr -> imp_expr   (**r runtime function call *)
    .

    Inductive imp_stmt :=
    | ImpStmtBlock : list (var * option imp_expr) -> list imp_stmt -> imp_stmt (**r block ([[{let x=e₁; let x=e₂; s₁; s₂}]]) *)
    | ImpStmtAssign : var -> imp_expr -> imp_stmt                              (**r variable assignent ([$v := e]) *)
    | ImpStmtFor : var -> imp_expr -> imp_stmt -> imp_stmt                     (**r for loop ([for ($v in e₁) { s₂ }]) *)
    | ImpStmtForRange : var -> imp_expr -> imp_expr -> imp_stmt -> imp_stmt    (**r for loop ([for ($v = e₁ to e₂) { s₂ }]) *)
    | ImpStmtIf : imp_expr -> imp_stmt -> imp_stmt -> imp_stmt                 (**r conditional ([if e₁ { s₂ } else { s₃ }]) *)
    | ImpStmtReturn : option imp_expr -> imp_stmt                              (**r return ([return e]) *)
    .

    Inductive imp_function :=
    | ImpFun : list var -> imp_stmt -> imp_function
    .

    (** [imp] is composed of a list of function declarations *)
    (*     and a main statement *)
    Inductive imp :=
    | ImpDef : string -> imp_function -> imp -> imp
    | ImpMain : imp_stmt -> imp
    .

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
  [ Case_aux c "ImpExprVar"%string
  | Case_aux c "ImpExprConst"%string
  | Case_aux c "ImpExprOp"%string
  | Case_aux c "ImpExprCall"%string].

Tactic Notation "imp_stmt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ImpStmtBlock"%string
  | Case_aux c "ImpStmtAssign"%string
  | Case_aux c "ImpStmtFor"%string
  | Case_aux c "ImpStmtForRange"%string
  | Case_aux c "ImpStmtIf"%string
  | Case_aux c "ImpStmtReturn"%string].

Tactic Notation "imp_function_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ImpFun"%string].

Tactic Notation "imp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ImpDef"%string
  | Case_aux c "ImpMain"%string].


Delimit Scope imp with imp_scope.
