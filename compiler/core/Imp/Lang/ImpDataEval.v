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
Require Import DataRuntime.
Require Import Imp.
Require Import ImpEval.
Require Import ImpData.

Section ImpDataEval.
  Context {fruntime:foreign_runtime}.

  Context (h:brand_relation_t).

  (* Local Open Scope imp_data. *)
  Local Open Scope string.
  Import ListNotations.

  Section EvalInstantiation.
    (* Instantiate Imp for Data data *)
    Definition imp_data_model_normalize (d:imp_data_constant) : imp_data_model :=
      normalize_data h d.

    Definition imp_data_model_to_bool (d:imp_data_model) : option bool :=
      match d with
      | dbool b => Some b
      | _ => None
      end.

    Definition imp_data_model_to_Z (d:imp_data_model) : option Z :=
      match d with
      | dnat n => Some n
      | _ => None
      end.

    Definition imp_data_Z_to_data (n:Z) : imp_data_model :=
      dnat n.

    Definition imp_data_model_to_list (d:imp_data_model) : option (list imp_data_model) :=
      match d with
      | dcoll c => Some (c)
      | _ => None
      end.

    Definition imp_data_runtime_eval (rt:imp_data_runtime_op) (dl:list imp_data_model) : option imp_data_model :=
      match rt with
      | DataRuntimeGroupby g kl =>
        match dl with
        | (dcoll dl) :: nil =>
          match group_by_nested_eval_table g kl dl with
          | Some dl' => Some (dcoll dl')
          | None => None
          end
        | _ => None
        end
      | DataRuntimeEither =>
        match dl with
        | (dleft d) :: nil => Some (dbool true)
        | (dright d) :: nil => Some (dbool false)
        | _ => None
        end
      | DataRuntimeToLeft =>
        match dl with
        | (dleft d) :: nil => Some d
        | _ => None
        end
      | DataRuntimeToRight =>
        match dl with
        | (dright d) :: nil => Some d
        | _ => None
        end
      end.

    Definition imp_data_op_eval (op:imp_data_op) (dl:list imp_data_model) : option imp_data_model :=
      match op with
      | DataOpUnary uop =>
        match dl with
        | [d] =>
          unary_op_eval h uop d
        | _ => None
        end
      | DataOpBinary bop =>
        match dl with
        | [d1;d2] =>
          binary_op_eval h bop d1 d2
        | _ => None
        end
      end.

  End EvalInstantiation.

  (** ** Evaluation Semantics *)
  Section Evaluation.

    (** Evaluation takes a ImpData expression and an environment. It
          returns an optional value. When [None] is returned, it
          denotes an error. An error is always propagated. *)

    Definition imp_data_expr_eval
             (σ:pd_bindings) (e:imp_data_expr)
    : option data
      := @imp_expr_eval
           imp_data_model
           imp_data_constant
           imp_data_op
           imp_data_runtime_op
           imp_data_model_normalize
           imp_data_runtime_eval
           imp_data_op_eval
           σ e.

    Definition imp_data_decls_eval
               (σ:pd_bindings) (el:list (string * option imp_data_expr))
      : option pd_bindings
      := @imp_decls_eval
           imp_data_model
           imp_data_constant
           imp_data_op
           imp_data_runtime_op
           imp_data_model_normalize
           imp_data_runtime_eval
           imp_data_op_eval
           σ el.

    Definition imp_data_decls_erase
               (σ:option pd_bindings) (el:list (string * option imp_data_expr))
      : option pd_bindings
      := imp_decls_erase σ el.

    Definition imp_data_stmt_eval
             (s:imp_data_stmt) (σ:pd_bindings) : option (pd_bindings)
      := @imp_stmt_eval
           imp_data_model
           imp_data_constant
           imp_data_op
           imp_data_runtime_op
           imp_data_model_normalize
           imp_data_model_to_bool
           imp_data_model_to_Z
           imp_data_model_to_list
           imp_data_Z_to_data
           imp_data_runtime_eval
           imp_data_op_eval
           s σ.

    Definition imp_data_function_eval
             (f:imp_data_function) args : option imp_data_model
      := @imp_function_eval
           imp_data_model
           imp_data_constant
           imp_data_op
           imp_data_runtime_op
           imp_data_model_normalize
           imp_data_model_to_bool
           imp_data_model_to_Z
           imp_data_model_to_list
           imp_data_Z_to_data
           imp_data_runtime_eval
           imp_data_op_eval
           f args.

    Definition imp_data_eval (q:imp_data) (d: data) : option (option data)
      := @imp_eval
           imp_data_model
           imp_data_constant
           imp_data_op
           imp_data_runtime_op
           imp_data_model_normalize
           imp_data_model_to_bool
           imp_data_model_to_Z
           imp_data_model_to_list
           imp_data_Z_to_data
           imp_data_runtime_eval
           imp_data_op_eval
           q d.

    Definition imp_data_eval_top σc (q:imp_data) :=
      olift id (imp_data_eval q (drec (rec_sort σc))).

  End Evaluation.

End ImpDataEval.

(* Arguments imp_stmt_eval_domain_stack {fruntime h s σ₁ σ₂}. *)
