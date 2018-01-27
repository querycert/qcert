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

Section BinaryOperators.
  Require Import EquivDec.
  Require Import String.
  Require Import Utils.
  Require Import ForeignData.
  Require Import ForeignOperators.

  Context {fdata:foreign_data}.
  Context {fbop:foreign_binary_op}.

  Inductive arith_binary_op
    := ArithPlus     (**r addition *)
     | ArithMinus    (**r substraction *)
     | ArithMult     (**r multiplication *)
     | ArithMin      (**r smallest *)
     | ArithMax      (**r biggest *)
     | ArithDivide   (**r division *)
     | ArithRem.     (**r remainder *)
  
  Inductive binary_op : Set :=
  | OpEqual : binary_op                          (**r equality *)
  | OpRecConcat : binary_op                      (**r record concatenation *)
  | OpRecMerge : binary_op                       (**r record merge-concatenation *)
  | OpAnd : binary_op                            (**r boolean conjunction *)
  | OpOr : binary_op                             (**r boolean disjunction *)
  | OpLt : binary_op                             (**r less than *)
  | OpLe : binary_op                             (**r less than or equal to *)
  | OpBagUnion : binary_op                       (**r bag union *)
  | OpBagDiff : binary_op                        (**r bag difference *)
  | OpBagMin : binary_op                         (**r bag min *)
  | OpBagMax : binary_op                         (**r bag max *)
  | OpContains : binary_op                       (**r is an element in a collection *)
  | OpStringConcat : binary_op                   (**r string concatenation *)
  | OpArithBinary : arith_binary_op -> binary_op (**r arithmetic operators *)
  | OpForeignBinary
      (fb : foreign_binary_op_type) : binary_op  (**r foreign binary operators *)
  .

  Global Instance arith_binary_op_eqdec : EqDec arith_binary_op eq.
  Proof.
    change (forall x y : arith_binary_op,  {x = y} + {x <> y}).
    decide equality.
  Defined.

  Global Instance binary_op_eqdec : EqDec binary_op eq.
  Proof.
    change (forall x y : binary_op,  {x = y} + {x <> y}).
    decide equality.
    apply arith_binary_op_eqdec.
    apply foreign_binary_op_dec.
  Defined.

  Local Open Scope string.

  Global Instance ToString_arith_binary_op : ToString arith_binary_op
    := {toString :=
          fun (op:arith_binary_op) =>
            match op with
            | ArithPlus => "ArithPlus"
            | ArithMinus => "ArithMinus"
            | ArithMult => "ArithMult"
            | ArithMin => "ArithMin"
            | ArithMax => "ArithMax"
            | ArithDivide => "ArithDivide"
            | ArithRem => "ArithRem"
            end
       }.

  Global Instance ToString_binary_op : ToString binary_op
    := {toString :=
          fun (op:binary_op) =>
            match op with
            | OpEqual => "OpEqual"
            | OpRecConcat  => "OpRecConcat"
            | OpRecMerge  => "OpRecMerge"
            | OpAnd  => "OpAnd"
            | OpOr  => "OpOr"
            | OpLt  => "OpLt"
            | OpLe  => "OpLe"
            | OpBagUnion => "OpBagUnion"
            | OpBagDiff => "OpBagDiff"
            | OpBagMin => "OpBagMin"
            | OpBagMax => "OpBagMax"
            | OpContains  => "OpContains"
            | OpStringConcat  => "OpStringConcat"
            | OpArithBinary aop => "(OpArithBinary " ++ (toString aop) ++ ")"
            | OpForeignBinary fb => toString fb
            end
       }.

End BinaryOperators.

Tactic Notation "binary_op_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "OpEqual"%string
  | Case_aux c "OpRecConcat"%string
  | Case_aux c "OpRecMerge"%string
  | Case_aux c "OpAnd"%string
  | Case_aux c "OpOr"%string
  | Case_aux c "OpLt"%string
  | Case_aux c "OpLe"%string
  | Case_aux c "OpBagUnion"%string
  | Case_aux c "OpBagDiff"%string
  | Case_aux c "OpBagMin"%string
  | Case_aux c "OpBagMax"%string
  | Case_aux c "OpContains"%string
  | Case_aux c "OpStringConcat"%string
  | Case_aux c "OpArithBinary"%string
  | Case_aux c "OpForeignBinary"%string].

