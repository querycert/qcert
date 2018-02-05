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
    | NNRCimpLetMut : var -> option (nnrc_imp_expr) -> nnrc_imp_stmt -> nnrc_imp_stmt (**r variable declaration ([const $v (:= e₁)? { s₂ }]) *)
    (* This creates a mutable collection, and evaluates the first
       statement with it bound to the given variable.  It then freezes
       the collection (makes it a normal bag) and evaluates the second
       statement with the variable bound to the bag version *)
    | NNRCimpBuildCollFor : var -> nnrc_imp_stmt -> nnrc_imp_stmt -> nnrc_imp_stmt    (**r mutable collection declaration ([var $v { s1 }; s2]) *)
    (* pushes to a variable that holds a mutable collection *)
    | NNRCimpPush : var -> nnrc_imp_expr -> nnrc_imp_stmt                             (**r push item in mutable collection ([push e in $v]) *)
    | NNRCimpAssign : var -> nnrc_imp_expr -> nnrc_imp_stmt                           (**r variable assignent ([$v := e]) *)
    | NNRCimpFor : var -> nnrc_imp_expr -> nnrc_imp_stmt -> nnrc_imp_stmt             (**r for loop ([for ($v in e₁) { s₂ }]) *)
    | NNRCimpIf : nnrc_imp_expr -> nnrc_imp_stmt -> nnrc_imp_stmt -> nnrc_imp_stmt    (**r conditional ([if e₁ { s₂ } else { s₃ }]) *)
    | NNRCimpEither : nnrc_imp_expr                                                   (**r case expression ([either e case left $v₁ { s₁ } case right $v₂ { s₂ }]) *)
                      -> var -> nnrc_imp_stmt
                      -> var -> nnrc_imp_stmt -> nnrc_imp_stmt
    .

    Definition nnrc_imp := nnrc_imp_stmt.

  End Syntax.

  Section Env.
      Context {fruntime:foreign_runtime}.

  (* bindings that may or may not be initialized (defined) *)
    Definition pd_bindings := list (string*option data).
    Definition mc_bindings := list (string*list data).

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
  | Case_aux c "NNRCimpLetMut"%string
  | Case_aux c "NNRCimpBuildCollFor"%string
  | Case_aux c "NNRCimpPush"%string
  | Case_aux c "NNRCimpAssign"%string
  | Case_aux c "NNRCimpFor"%string
  | Case_aux c "NNRCimpIf"%string
  | Case_aux c "NNRCimpEither"%string].

Delimit Scope nnrc_imp with nnrc_imp_scope.
