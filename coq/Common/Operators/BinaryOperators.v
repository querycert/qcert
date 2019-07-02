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

Require Import EquivDec.
Require Import String.
Require Import Utils.
Require Import ForeignData.
Require Import ForeignOperators.

Section BinaryOperators.
  Context {fdata:foreign_data}.
  Context {fbop:foreign_binary_op}.

  Inductive nat_arith_binary_op
    := NatPlus     (**r addition *)
     | NatMinus    (**r substraction *)
     | NatMult     (**r multiplication *)
     | NatDiv      (**r division *)
     | NatRem      (**r remainder *)
     | NatMin      (**r smallest *)
     | NatMax.     (**r biggest *)
  
  Inductive float_arith_binary_op
    :=
    | FloatPlus   (**r addition *)
    | FloatMinus  (**r substraction *)
    | FloatMult   (**r multiplication *)
    | FloatDiv    (**r division *)
    | FloatPow    (**r exponent *)
    | FloatMin    (**r min *)
    | FloatMax    (**r max *)
  .

  Inductive float_compare_binary_op
    :=
    | FloatLt     (**r less than *)
    | FloatLe     (**r less than or equal to *)
    | FloatGt     (**r greater than *)
    | FloatGe     (**r greater than or equal to *)
  .

  Inductive binary_op : Set :=
  | OpEqual : binary_op                                   (**r equality *)
  | OpRecConcat : binary_op                               (**r record concatenation *)
  | OpRecMerge : binary_op                                (**r record merge-concatenation *)
  | OpAnd : binary_op                                     (**r boolean conjunction *)
  | OpOr : binary_op                                      (**r boolean disjunction *)
  | OpLt : binary_op                                      (**r less than *)
  | OpLe : binary_op                                      (**r less than or equal to *)
  | OpBagUnion : binary_op                                (**r bag union *)
  | OpBagDiff : binary_op                                 (**r bag difference *)
  | OpBagMin : binary_op                                  (**r bag min *)
  | OpBagMax : binary_op                                  (**r bag max *)
  | OpBagNth : binary_op                                  (**r random element in a bag *)
  | OpContains : binary_op                                (**r is an element in a collection *)
  | OpStringConcat : binary_op                            (**r string concatenation *)
  | OpStringJoin : binary_op                              (**r string join *)
  | OpNatBinary : nat_arith_binary_op -> binary_op        (**r arithmetic operators on integers *)
  | OpFloatBinary : float_arith_binary_op -> binary_op    (**r arithmetic operators on floats *)
  | OpFloatCompare : float_compare_binary_op -> binary_op (**r comparison operators on floats *)
  | OpForeignBinary
      (fb : foreign_binary_op_type) : binary_op         (**r foreign binary operators *)
  .

  Global Instance nat_arith_binary_op_eqdec : EqDec nat_arith_binary_op eq.
  Proof.
    change (forall x y : nat_arith_binary_op,  {x = y} + {x <> y}).
    decide equality.
  Defined.

  Global Instance float_arith_binary_op_eqdec : EqDec float_arith_binary_op eq.
  Proof.
    change (forall x y : float_arith_binary_op,  {x = y} + {x <> y}).
    decide equality.
  Defined.

  Global Instance float_compare_binary_op_eqdec : EqDec float_compare_binary_op eq.
  Proof.
    change (forall x y : float_compare_binary_op,  {x = y} + {x <> y}).
    decide equality.
  Defined.

  Global Instance binary_op_eqdec : EqDec binary_op eq.
  Proof.
    change (forall x y : binary_op,  {x = y} + {x <> y}).
    decide equality.
    apply nat_arith_binary_op_eqdec.
    apply float_arith_binary_op_eqdec.
    apply float_compare_binary_op_eqdec.
    apply foreign_binary_op_dec.
  Defined.

  Local Open Scope string.

  Global Instance ToString_nat_binary_op : ToString nat_arith_binary_op
    := {toString :=
          fun (op:nat_arith_binary_op) =>
            match op with
            | NatPlus => "NatPlus"
            | NatMinus => "NatMinus"
            | NatMult => "NatMult"
            | NatMin => "NatMin"
            | NatMax => "NatMax"
            | NatDiv => "NatDiv"
            | NatRem => "NatRem"
            end
       }.

  Global Instance ToString_float_arith_binary_op : ToString float_arith_binary_op
    := {toString :=
          fun (op:float_arith_binary_op) =>
            match op with
            | FloatPlus => "FloatPlus"
            | FloatMinus => "FloatMinus"
            | FloatMult => "FloatMult"
            | FloatDiv => "FloatDiv"
            | FloatPow => "FloatPow"
            | FloatMin => "FloatMin"
            | FloatMax => "FloatMax"
            end
       }.

  Global Instance ToString_float_compare_binary_op : ToString float_compare_binary_op
    := {toString :=
          fun (op:float_compare_binary_op) =>
            match op with
            | FloatLt => "FloatLt"
            | FloatLe => "FloatLe"
            | FloatGt => "FloatGt"
            | FloatGe => "FloatGe"
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
            | OpBagNth => "OpBagNth"
            | OpContains  => "OpContains"
            | OpStringConcat  => "OpStringConcat"
            | OpStringJoin  => "OpStringJoin"
            | OpNatBinary aop => "(OpNatBinary " ++ (toString aop) ++ ")"
            | OpFloatBinary aop => "(OpFloatBinary " ++ (toString aop) ++ ")"
            | OpFloatCompare aop => "(OpFloatCompare " ++ (toString aop) ++ ")"
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
  | Case_aux c "OpBagNth"%string
  | Case_aux c "OpContains"%string
  | Case_aux c "OpStringConcat"%string
  | Case_aux c "OpStringJoin"%string
  | Case_aux c "OpNatBinary"%string
  | Case_aux c "OpFloatBinary"%string
  | Case_aux c "OpFloatCompare"%string
  | Case_aux c "OpForeignBinary"%string].

