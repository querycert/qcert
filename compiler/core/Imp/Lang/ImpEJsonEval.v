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
Require Import BrandRelation.
Require Import EJsonRuntime.
Require Import Imp.
Require Import ImpEval.
Require Import ImpEJson.

Section ImpEJsonEval.
  Context {fejson:foreign_ejson}.
  Context {fejruntime:foreign_ejson_runtime}.
  (* XXX We should try and compile the hierarchy in. Currenty it is still used in cast for sub-branding check *)
  Context (h:brand_relation_t).

  Section EvalInstantiation.
    (* Instantiate Imp for Qcert data *)
    Definition imp_ejson_model_normalize (c:imp_ejson_constant) : imp_ejson_model :=
      match c with
      | cejnull => ejnull
      | cejnumber f => ejnumber f
      | cejbigint n => ejbigint n
      | cejbool b => ejbool b
      | cejstring s => ejstring s
      | cejforeign f => ejforeign f
      end.

    Definition imp_ejson_model_to_bool (d:imp_ejson_model) : option bool :=
      match d with
      | ejbool b => Some b
      | _ => None
      end.

    Definition imp_ejson_model_to_list (d:imp_ejson_model) : option (list imp_ejson_model) :=
      match d with
      | ejarray c => Some (c)
      | _ => None
      end.

    Definition imp_ejson_model_to_Z (d:imp_ejson_model) : option Z :=
      match d with
      | ejbigint n => Some n
      | _ => None
      end.

    Definition imp_ejson_Z_to_data (n: Z) : imp_ejson_model := ejbigint n.

    Definition imp_ejson_op_eval (op:imp_ejson_op) (dl:list imp_ejson_model) : option imp_ejson_model :=
      ejson_op_eval op dl. (* XXX In Common.EJson.EJsonOperators *)

    Definition imp_ejson_runtime_eval (op:imp_ejson_runtime_op)
               (dl:list imp_ejson_model) : option imp_ejson_model :=
      ejson_runtime_eval h op dl. (* XXX In Common.EJson.EJsonOperators *)
  End EvalInstantiation.

  (** ** Evaluation Semantics *)
  Section Evaluation.

    (** Evaluation takes a ImpQcert expression and an environment. It
          returns an optional value. When [None] is returned, it
          denotes an error. An error is always propagated. *)

    Definition imp_ejson_expr_eval
               (σ:pd_jbindings) (e:imp_ejson_expr)
      : option imp_ejson_model
      := @imp_expr_eval
           imp_ejson_model
           imp_ejson_constant
           imp_ejson_op
           imp_ejson_runtime_op
           imp_ejson_model_normalize
           imp_ejson_runtime_eval
           imp_ejson_op_eval
           σ e.

    Definition imp_ejson_decls_eval
               (σ:pd_jbindings) (el:list (string * option imp_ejson_expr))
      : option pd_jbindings
      := @imp_decls_eval
           imp_ejson_model
           imp_ejson_constant
           imp_ejson_op
           imp_ejson_runtime_op
           imp_ejson_model_normalize
           imp_ejson_runtime_eval
           imp_ejson_op_eval
           σ el.

    Definition imp_ejson_decls_erase
               (σ:option pd_jbindings) (el:list (string * option imp_ejson_expr))
      : option pd_jbindings
      := imp_decls_erase σ el.

    Definition imp_ejson_stmt_eval
             (s:imp_ejson_stmt) (σ:pd_jbindings) : option (pd_jbindings)
      := @imp_stmt_eval
           imp_ejson_model
           imp_ejson_constant
           imp_ejson_op
           imp_ejson_runtime_op
           imp_ejson_model_normalize
           imp_ejson_model_to_bool
           imp_ejson_model_to_Z
           imp_ejson_model_to_list
           imp_ejson_Z_to_data
           imp_ejson_runtime_eval
           imp_ejson_op_eval
           s σ.

    Definition imp_ejson_function_eval
             (f:imp_ejson_function) args : option imp_ejson_model
      := @imp_function_eval
           imp_ejson_model
           imp_ejson_constant
           imp_ejson_op
           imp_ejson_runtime_op
           imp_ejson_model_normalize
           imp_ejson_model_to_bool
           imp_ejson_model_to_Z
           imp_ejson_model_to_list
           imp_ejson_Z_to_data
           imp_ejson_runtime_eval
           imp_ejson_op_eval
           f args.

    Import ListNotations.
    Definition imp_ejson_eval (q:imp_ejson) (d:imp_ejson_model) : option (option imp_ejson_model)
      := @imp_eval
           imp_ejson_model
           imp_ejson_constant
           imp_ejson_op
           imp_ejson_runtime_op
           imp_ejson_model_normalize
           imp_ejson_model_to_bool
           imp_ejson_model_to_Z
           imp_ejson_model_to_list
           imp_ejson_Z_to_data
           imp_ejson_runtime_eval
           imp_ejson_op_eval
           q d.

    Definition imp_ejson_eval_top_on_ejson σc (q:imp_ejson) : option imp_ejson_model :=
      let σc' := List.map (fun xy => (key_encode (fst xy), snd xy)) (rec_sort σc) in
      olift id (imp_ejson_eval q (ejobject σc')).

  End Evaluation.

End ImpEJsonEval.

Require Import DataRuntime.
Require Import ForeignDataToEJson.
Require Import DataToEJson.
Section Top.
  Context {fruntime:foreign_runtime}.
  Context {fejson:foreign_ejson}.
  Context {fdatatoejson:foreign_to_ejson}.
  Context {fejruntime:foreign_ejson_runtime}.
  (* XXX We should try and compile the hierarchy in. Currenty it is still used in cast for sub-branding check *)
  Context (h:brand_relation_t).
  Definition imp_ejson_eval_top (cenv: bindings) (q:imp_ejson) : option data :=
    let jenv := List.map (fun xy => (fst xy, data_to_ejson(snd xy))) cenv in
    lift ejson_to_data (imp_ejson_eval_top_on_ejson h jenv q).
End Top.

