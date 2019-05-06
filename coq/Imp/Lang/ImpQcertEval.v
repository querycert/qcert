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

(** NNRSimp is a variant of the named nested relational calculus
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
Require Import Imp.
Require Import ImpQcert.

Section ImpQcertEval.

  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  (* Local Open Scope imp_qcert. *)
  Local Open Scope string.

  (** ** Evaluation Semantics *)
  Section Evaluation.

    (** Evaluation takes a ImpQcert expression and an environment. It
          returns an optional value. When [None] is returned, it
          denotes an error. An error is always propagated. *)

    Fixpoint imp_qcert_expr_eval
             (σc:bindings) (σ:pd_bindings) (e:imp_qcert_expr)
    : option data
      := None. (* XXX TODO XXX *)


    Fixpoint imp_qcert_stmt_eval
             (σc:bindings) (s:imp_qcert_stmt)
             (σ:pd_bindings) : option (pd_bindings)
      := None. (* XXX TODO XXX *)


    Definition imp_qcert_eval (σc:bindings) (q:imp_qcert) : option (option data)
      := let ignore := h in None. (* XXX TODO XXX *)

    Definition imp_qcert_eval_top σc (q:imp_qcert) :=
      olift id (imp_qcert_eval (rec_sort σc) q).

  End Evaluation.

End ImpQcertEval.

(* Arguments imp_stmt_eval_domain_stack {fruntime h s σc σ₁ σ₂}. *)
