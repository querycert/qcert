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

Require Import String.
Require Import List.
Require Import Bool.
Require Import Arith.
Require Import Utils.
Require Import Imp.
Require Import ImpJson.
Require Import JavaScriptAstRuntime.

Section ImpJsontoJavaScriptAst.
  Import ListNotations.

  (** Translation *)

  Definition mk_expr_error := expr_literal literal_null.
  Definition mk_unary_expr (f:expr -> expr) (el:list expr) : expr :=
    match el with
    | [e] => f e
    | _ => mk_expr_error
    end.

  Definition mk_unary_op (op:unary_op) (el:list expr) : expr :=
    mk_unary_expr (expr_unary_op op) el.

  Definition mk_binary_expr (f:expr -> expr -> expr) (el:list expr) : expr :=
    match el with
    | [e1;e2] => f e1 e2
    | _ => mk_expr_error
    end.

  Definition mk_binary_op (op:binary_op) (el:list expr) : expr :=
    mk_binary_expr (fun e1 e2 => expr_binary_op e1 op e2) el.

  Definition mk_object (atts:list string) (el:list expr) : expr :=
    match zip atts el with
    | Some l =>
      expr_object
        (List.map
           (fun (entry: string * expr) =>
              let (lbl, e) := entry in
              (propname_identifier lbl, propbody_val e))
           l)
    | None => mk_expr_error
    end.
  
  Definition imp_json_op_to_js_ast (op:imp_json_op) el : expr :=
    match op with
    | JSONOpNot => mk_unary_op unary_op_not el
    | JSONOpNeg => mk_unary_op unary_op_neg el
    | JSONOpAnd => mk_binary_op binary_op_and el
    | JSONOpOr => mk_binary_op binary_op_or el
    | JSONOpLt => mk_binary_op binary_op_lt el
    | JSONOpLe => mk_binary_op binary_op_le el
    | JSONOpGt => mk_binary_op binary_op_gt el
    | JSONOpGe => mk_binary_op binary_op_ge el
    | JSONOpAddString => mk_binary_op binary_op_add el
    | JSONOpAddNumber => mk_binary_op binary_op_add el
    | JSONOpSub => mk_binary_op binary_op_sub el
    | JSONOpDiv => mk_binary_op binary_op_div el
    | JSONOpMult => mk_binary_op binary_op_mult el
    | JSONOpStrictEqual => mk_binary_op binary_op_strict_equal el
    | JSONOpStrictDisequal => mk_binary_op binary_op_strict_disequal el
    | JSONOpArray => expr_array (List.map Some el)
    | JSONOpArrayLength => mk_expr_error (** XXX TBD *)
    | JSONOpArrayPush => mk_binary_expr array_push el
    | JSONOpObject atts => mk_object atts el
    | JSONOpAccess att => mk_binary_expr expr_access (el++[expr_literal (literal_string att)])
    | JSONOpHasOwnProperty att => mk_binary_expr object_hasOwnProperty (el++[expr_literal (literal_string att)])
    | JSONOpToString => mk_unary_expr object_toString el
    end.

  Fixpoint imp_json_to_js_ast (exp: imp_json_expr) : expr :=
    match exp with
    | ImpExprVar v => expr_identifier v
    | ImpExprConst j => json_to_js_ast j
    | ImpExprOp op el => imp_json_op_to_js_ast op (map imp_json_to_js_ast el)
    | ImpExprCall f el => call_js_function f (map imp_json_to_js_ast el)
    | ImpExprRuntimeCall rop el => mk_expr_error (* XXX TBD *)
    end.

  (* XXX this should be kinda like what happens in NNRSimptoJavaScriptAst *)
  Fixpoint imp_stmt_to_imp_qcert (stmt: imp_json_stmt): stat :=
    match stmt with
    | _ => stat_block []
    end.

End ImpJsontoJavaScriptAst.
