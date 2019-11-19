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
Require Import ZArith.
Require Import Max.
Require Import Bool.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import CommonRuntime.
Require Import Imp.
Require Import ImpEval.
Require Import ImpQcert.

Section ImpQcertEval.

  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  (* Local Open Scope imp_qcert. *)
  Local Open Scope string.
  Import ListNotations.

  Section EvalInstantiation.
    (* Instantiate Imp for Qcert data *)
    Definition imp_qcert_data_normalize (d:imp_qcert_data) : imp_qcert_data :=
      normalize_data h d.

    Definition imp_qcert_data_to_bool (d:imp_qcert_data) : option bool :=
      match d with
      | dbool b => Some b
      | _ => None
      end.

    Definition imp_qcert_data_to_Z (d:imp_qcert_data) : option Z :=
      match d with
      | dnat n => Some n
      | _ => None
      end.

    Definition imp_qcert_Z_to_data (n:Z) : imp_qcert_data :=
      dnat n.

    Definition imp_qcert_data_to_list (d:imp_qcert_data) : option (list imp_qcert_data) :=
      match d with
      | dcoll c => Some (c)
      | _ => None
      end.

    Definition imp_qcert_runtime_eval (rt:imp_qcert_runtime_op) (dl:list imp_qcert_data) : option imp_qcert_data :=
      match rt with
      | QcertRuntimeGroupby g kl =>
        match dl with
        | (dcoll dl) :: nil =>
          match group_by_nested_eval_table g kl dl with
          | Some dl' => Some (dcoll dl')
          | None => None
          end
        | _ => None
        end
      | QcertRuntimeEither =>
        match dl with
        | (dleft d) :: nil => Some (dbool true)
        | (dright d) :: nil => Some (dbool false)
        | _ => None
        end
      | QcertRuntimeToLeft =>
        match dl with
        | (dleft d) :: nil => Some d
        | _ => None
        end
      | QcertRuntimeToRight =>
        match dl with
        | (dright d) :: nil => Some d
        | _ => None
        end
      | QcertRuntimeDeref => (* XXX Not so sure this should be so high-level *)
        match dl with
        | d :: nil => Some d
        | _ => None
        end
      end.

    Definition imp_qcert_op_eval (op:imp_qcert_op) (dl:list imp_qcert_data) : option imp_qcert_data :=
      match op with
      | QcertOpUnary uop =>
        match dl with
        | [d] =>
          unary_op_eval h uop d
        | _ => None
        end

      | QcertOpBinary bop =>
        match dl with
        | [d1;d2] =>
          binary_op_eval h bop d1 d2
        | _ => None
        end
      end.

  End EvalInstantiation.

  (** ** Evaluation Semantics *)
  Section Evaluation.

    (** Evaluation takes a ImpQcert expression and an environment. It
          returns an optional value. When [None] is returned, it
          denotes an error. An error is always propagated. *)

    Definition imp_qcert_expr_eval
             (σ:pd_bindings) (e:imp_qcert_expr)
    : option data
      := @imp_expr_eval
           imp_qcert_data
           imp_qcert_op
           imp_qcert_runtime_op
           imp_qcert_data_normalize
           imp_qcert_runtime_eval
           imp_qcert_op_eval
           σ e.

    Definition imp_qcert_stmt_eval
             (s:imp_qcert_stmt) (σ:pd_bindings) : option (pd_bindings)
      := @imp_stmt_eval
           imp_qcert_data
           imp_qcert_op
           imp_qcert_runtime_op
           imp_qcert_data_normalize
           imp_qcert_data_to_bool
           imp_qcert_data_to_Z
           imp_qcert_data_to_list
           imp_qcert_Z_to_data
           imp_qcert_runtime_eval
           imp_qcert_op_eval
           s σ.

    Definition imp_qcert_function_eval
             (f:imp_qcert_function) args : option imp_qcert_data
      := @imp_function_eval
           imp_qcert_data
           imp_qcert_op
           imp_qcert_runtime_op
           imp_qcert_data_normalize
           imp_qcert_data_to_bool
           imp_qcert_data_to_Z
           imp_qcert_data_to_list
           imp_qcert_Z_to_data
           imp_qcert_runtime_eval
           imp_qcert_op_eval
           f args.

    Definition imp_qcert_eval (q:imp_qcert) (d: data) : option (option data)
      := @imp_eval
           imp_qcert_data
           imp_qcert_op
           imp_qcert_runtime_op
           imp_qcert_data_normalize
           imp_qcert_data_to_bool
           imp_qcert_data_to_Z
           imp_qcert_data_to_list
           imp_qcert_Z_to_data
           imp_qcert_runtime_eval
           imp_qcert_op_eval
           q d.

    Definition imp_qcert_eval_top σc (q:imp_qcert) :=
      olift id (imp_qcert_eval q (drec (rec_sort σc))).

  End Evaluation.

End ImpQcertEval.

(* Arguments imp_stmt_eval_domain_stack {fruntime h s σ₁ σ₂}. *)
