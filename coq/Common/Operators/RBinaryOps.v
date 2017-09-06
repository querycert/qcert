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

Section RBinaryOps.
  Require Import EquivDec.
  Require Import String.
  Require Import Utils.
  Require Import ForeignData.
  Require Import ForeignOps.

  Context {fdata:foreign_data}.
  Context {fbop:foreign_binary_op}.

  Inductive ArithBOp
    := ArithPlus
     | ArithMinus
     | ArithMult
     | ArithMin
     | ArithMax
     | ArithDivide
     | ArithRem.
  
  Inductive binOp : Set :=
  | AEq: binOp                  (* equality *)
  | AConcat : binOp             (* Record concatenation *)
  | AMergeConcat : binOp        (* Record merge-concatenation *)
  | AAnd : binOp                (* boolean conjunction *)
  | AOr : binOp                 (* boolean disjunction *)
  | ABArith : ArithBOp -> binOp (* arithmetic operators *)
  | ALt : binOp                 (* less than *)
  | ALe : binOp                 (* less than or equal to *)
  | AUnion: binOp               (* bag union *)
  | AMinus: binOp               (* bag difference *)
  | AMin: binOp                 (* bag min *)
  | AMax: binOp                 (* bag max *)
  | AContains : binOp           (* is an element in a collection *)
  | ASConcat : binOp            (* String concatenation *)
  | AForeignBinaryOp (fb : foreign_binary_op_type) : binOp
  .

Global Instance ArithBOp_eqdec : EqDec ArithBOp eq.
Proof.
  change (forall x y : ArithBOp,  {x = y} + {x <> y}).
  decide equality.
Defined.

Global Instance binOp_eqdec : EqDec binOp eq.
Proof.
  change (forall x y : binOp,  {x = y} + {x <> y}).
  decide equality.
  apply ArithBOp_eqdec.
  apply foreign_binary_op_dec.
Defined.

Local Open Scope string.

Global Instance ToString_ArithBOp : ToString ArithBOp
  := {toString :=
        fun (op:ArithBOp) =>
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

Global Instance ToString_binOp : ToString binOp
  := {toString :=
        fun (op:binOp) =>
          match op with
            | AEq => "AEq"
            | AUnion => "AUnion"
            | AConcat  => "AConcat"
            | AMergeConcat  => "AMergeConcat"
            | AAnd  => "AAnd"
            | AOr  => "AOr"
            | ABArith aop => "(ABArith " ++ (toString aop) ++ ")"
            | ALt  => "ALt"
            | ALe  => "ALe"
            | AMinus => "AMinus"
            | AMin => "AMin"
            | AMax => "AMax"
            | AContains  => "AContains"
            | ASConcat  => "ASConcat"
            | AForeignBinaryOp fb => toString fb
          end
     }.

End RBinaryOps.

Tactic Notation "binOp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "AEq"%string
  | Case_aux c "AConcat"%string
  | Case_aux c "AMergeConcat"%string
  | Case_aux c "AAnd"%string
  | Case_aux c "AOr"%string
  | Case_aux c "ABArith"%string
  | Case_aux c "ALt"%string
  | Case_aux c "ALe"%string
  | Case_aux c "AUnion"%string
  | Case_aux c "AMinus"%string
  | Case_aux c "AMin"%string
  | Case_aux c "AMax"%string
  | Case_aux c "AContains"%string
  | Case_aux c "ASConcat"%string
  | Case_aux c "AForeignBinaryOp"%string].

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
