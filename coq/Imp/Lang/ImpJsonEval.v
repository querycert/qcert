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
Require Import ImpJson.

Section ImpJsonEval.

  Local Open Scope string.

  Section EvalInstantiation.
    (* Instantiate Imp for Qcert data *)
    Definition imp_json_data_normalize (d:imp_json_data) : imp_json_data :=
      d. (* XXX What to do? *)

    Definition imp_json_data_to_bool (d:imp_json_data) : option bool :=
      match d with
      | jbool b => Some b
      | _ => None
      end.

    Definition imp_json_data_to_Z (d:imp_json_data) : option Z :=
      match d with
      | jnumber n => Some (float_truncate n)
      | _ => None
      end.

    Definition imp_json_data_to_list (d:imp_json_data) : option (list imp_json_data) :=
      match d with
      | jarray c => Some (c)
      | _ => None
      end.

    Definition of_string_list (sl:list json) : option (list string)
      := lift_map (fun x => match x with jstring s => Some s | _ => None end) sl.

    Definition imp_json_runtime_eval (rt:imp_json_runtime_op) (dl:list imp_json_data) : option imp_json_data :=
      match rt with
      | JSONRuntimeEqual =>
        apply_binary (fun d1 d2 => if json_eq_dec d1 d2 then Some (jbool true) else Some (jbool false)) dl
      | JSONRuntimeCompare => None (* XXX pfff... *)
      | JSONRuntimeRecConcat =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | (jobject r1), (jobject r2) => Some (jobject (rec_sort (r1++r2)))
             | _, _ => None
             end) dl
      | JSONRuntimeRecMerge =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | (jobject r1), (jobject r2) =>
               match @merge_bindings json _ json_eq_dec r1 r2 with
               | Some x => Some (jarray ((jobject x) :: nil))
               | None => Some (jarray nil)
               end
             | _, _ => None
             end) dl
      | JSONRuntimeDistinct =>
        apply_unary
          (fun d =>
             match d with
             | jarray l =>
               Some (jarray (@bdistinct json json_eq_dec l))
             | _ => None
             end)
          dl
      | JSONRuntimeGroupBy => None (* XXX TODO *)
      | JSONRuntimeDeref => (* XXX the one in qcert-runtime is a lot more complex *)
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | jobject r, jstring s =>
               edot r s
             | _, _ => None
             end) dl
      | JSONRuntimeEither =>
        apply_unary
          (fun d =>
             match d with
             | jobject (("left", _)::nil) => Some (jbool true)
             | jobject (("right",_)::nil) => Some (jbool false)
             | _ => None
             end) dl
      | JSONRuntimeToLeft =>
        apply_unary
          (fun d =>
             match d with
             | jobject (("left", d)::nil) => Some d
             | _ => None
             end) dl
      | JSONRuntimeToRight =>
        apply_unary
          (fun d =>
             match d with
             | jobject (("right", d)::nil) => Some d
             | _ => None
             end) dl
      | JSONRuntimeRemove =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | jobject r, jstring s =>
               Some (jobject (rremove r s))
             | _, _ => None
             end) dl
      | JSONRuntimeProject =>
        apply_binary
          (fun d1 d2 =>
             match d1, d2 with
             | jobject r, jarray sl =>
               lift jobject (lift (rproject r) (of_string_list sl))
             | _, _ => None
             end) dl
      | JSONRuntimeSingleton =>
        apply_unary
          (fun d =>
             match d with
             | jarray (d::nil) => Some d
             | _ => None
             end) dl
      | JSONRuntimeFlatten => None
      | JSONRuntimeSort => None
      | JSONRuntimeCount => None
      | JSONRuntimeLength => None
      | JSONRuntimeSubstring => None
      | JSONRuntimeBrand => None
      | JSONRuntimeUnbrand => None
      | JSONRuntimeCast => None
      | JSONRuntimeNatPlus => None
      | JSONRuntimeNatMinus => None
      | JSONRuntimeNatMult => None
      | JSONRuntimeNatDiv => None
      | JSONRuntimeNatRem => None
      | JSONRuntimeNatAbs => None
      | JSONRuntimeNatLog2 => None
      | JSONRuntimeNatSqrt => None
      | JSONRuntimeNatSum => None
      | JSONRuntimeNatMin => None
      | JSONRuntimeNatMax => None
      | JSONRuntimeNatArithMean => None
      | JSONRuntimeFloatOfNat => None
      | JSONRuntimeSum => None
      | JSONRuntimeArithMean => None
      | JSONRuntimeBunion => None
      | JSONRuntimeBminus => None
      | JSONRuntimeBmin => None
      | JSONRuntimeBmax => None
      | JSONRuntimeBnth => None
      | JSONRuntimeContains => None
      | JSONRuntimeToString => None
      | JSONRuntimeGenerateText => None
      | JSONRuntimeStringJoin => None
      end.

    Definition imp_json_op_eval (op:imp_json_op) (dl:list imp_json_data) : option imp_json_data :=
      json_op_eval op dl. (* XXX In Utils.JSONOperators *)

  End EvalInstantiation.

  (** ** Evaluation Semantics *)
  Section Evaluation.

    (** Evaluation takes a ImpQcert expression and an environment. It
          returns an optional value. When [None] is returned, it
          denotes an error. An error is always propagated. *)

    Definition jbindings := list (string * imp_json_data).
    Definition pd_jbindings := list (string * option imp_json_data).

    Definition imp_json_expr_eval
             (σc:jbindings) (σ:pd_jbindings) (e:imp_json_expr)
    : option imp_json_data
      := @imp_expr_eval
           imp_json_data
           imp_json_op
           imp_json_runtime_op
           imp_json_data_normalize
           imp_json_runtime_eval
           imp_json_op_eval
           σc σ e.

    Definition imp_json_stmt_eval
             (σc:jbindings) (s:imp_json_stmt) (σ:pd_jbindings) : option (pd_jbindings)
      := @imp_stmt_eval
           imp_json_data
           imp_json_op
           imp_json_runtime_op
           imp_json_data_normalize
           imp_json_data_to_bool
           imp_json_data_to_list
           imp_json_runtime_eval
           imp_json_op_eval
           σc s σ.

    Definition imp_json_eval (σc:jbindings) (q:imp_json) : option (option imp_json_data)
      := None. (* XXX TODO XXX *)

    Definition imp_json_eval_top σc (q:imp_json) :=
      olift id (imp_json_eval (rec_sort σc) q).

  End Evaluation.

End ImpJsonEval.

(* Arguments imp_stmt_eval_domain_stack {fruntime h s σc σ₁ σ₂}. *)
