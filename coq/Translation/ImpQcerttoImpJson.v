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
Require Import JSONOperators.
Require Import CommonRuntime.
Require Import Imp.
Require Import ImpQcert.
Require Import ImpJson.

Section ImpJsontoJavaScriptAst.
  Import ListNotations.

  Context {fruntime:foreign_runtime}.
  Context {ftojson:foreign_to_JSON}.

  (** Translation *)

  Definition mk_imp_json_expr_error : imp_json_expr := ImpExprConst jnil.
  Definition mk_imp_json_op op el : imp_json_expr := ImpExprOp op el.
  Definition mk_imp_json_runtime_call op el : imp_json_expr := ImpExprRuntimeCall op el.
  Definition imp_qcert_unary_op_to_imp_json (op:unary_op) el : imp_json_expr :=
    match op with
    | OpIdentity =>
      match el with
      | [e] => e
      | _ => mk_imp_json_expr_error
      end
    | OpNeg => mk_imp_json_op JSONOpNeg el
    | OpRec s => mk_imp_json_op (JSONOpObject [s]) el
    | OpDot s => mk_imp_json_op (JSONOpAccess s) el
    | _ => mk_imp_json_expr_error (* XXX TODO  *)
    end.

  Definition imp_qcert_binary_op_to_imp_json (op:binary_op) el : imp_json_expr :=
    match op with
    | OpEqual => mk_imp_json_runtime_call JSONRuntimeEqual el
    | OpRecConcat => mk_imp_json_runtime_call JSONRuntimeRecConcat el
    | OpRecMerge => mk_imp_json_runtime_call JSONRuntimeRecMerge el
    | OpAnd => mk_imp_json_op JSONOpAnd el
    | OpOr => mk_imp_json_op JSONOpOr el
    | _ => mk_imp_json_expr_error (* XXX TODO  *)
    end.

  Definition imp_qcert_op_to_imp_json (op:imp_qcert_op) el : imp_json_expr :=
    match op with
    | Unary op => imp_qcert_unary_op_to_imp_json op el
    | Binary op => imp_qcert_binary_op_to_imp_json op el
    end.

  Definition mk_either_expr (el:list imp_json_expr) : imp_json_expr :=
    mk_imp_json_expr_error. (* XXX TODO  *)
  Definition mk_to_left_expr (el:list imp_json_expr) : imp_json_expr :=
    mk_imp_json_expr_error. (* XXX TODO  *)
  Definition mk_to_right_expr (el:list imp_json_expr) : imp_json_expr :=
    mk_imp_json_expr_error. (* XXX TODO  *)

  Definition imp_qcert_runtime_call_to_imp_json
             (op:imp_qcert_runtime_op)
             (el:list imp_json_expr) : imp_json_expr :=
    match op with
    | RuntimeGroupby s ls =>
      mk_imp_json_runtime_call
        JSONRuntimeGroupBy
        ((ImpExprConst (jstring s))
           :: (ImpExprConst (jarray (map jstring ls)))
           :: el)
    | RuntimeEither => mk_either_expr el
    | RuntimeToLeft => mk_to_left_expr el
    | RuntimeToRight => mk_to_right_expr el
    | RuntimeDeref =>
      mk_imp_json_runtime_call JSONRuntimeDeref el (* XXX ???? TODO *)
    end.

  Fixpoint imp_qcert_expr_to_imp_json (exp: imp_qcert_expr) : imp_json_expr :=
    match exp with
    | ImpExprVar v => ImpExprVar v
    | ImpExprConst d => ImpExprConst (data_to_json d)
    | ImpExprOp op el => imp_qcert_op_to_imp_json op (map imp_qcert_expr_to_imp_json el)
    | ImpExprCall f el => ImpExprCall f (map imp_qcert_expr_to_imp_json el)
    | ImpExprRuntimeCall op el => imp_qcert_runtime_call_to_imp_json op (map imp_qcert_expr_to_imp_json el)
    end.

  Fixpoint imp_qcert_stmt_to_imp_json (stmt: imp_qcert_stmt): imp_json_stmt :=
    match stmt with
    | ImpStmtBlock lv ls =>
      ImpStmtBlock
        (map (fun xy => (fst xy,
                         lift imp_qcert_expr_to_imp_json (snd xy))) lv)
        (map imp_qcert_stmt_to_imp_json ls)
    | ImpStmtAssign v e =>
      ImpStmtAssign v (imp_qcert_expr_to_imp_json e)
    | ImpStmtFor v e s =>
      ImpStmtFor v (imp_qcert_expr_to_imp_json e) (imp_qcert_stmt_to_imp_json s)
    | ImpStmtForRange v e1 e2 s =>
      ImpStmtForRange v
                      (imp_qcert_expr_to_imp_json e1)
                      (imp_qcert_expr_to_imp_json e2)
                      (imp_qcert_stmt_to_imp_json s)
    | ImpStmtIf e s1 s2 =>
      ImpStmtIf (imp_qcert_expr_to_imp_json e)
                (imp_qcert_stmt_to_imp_json s1)
                (imp_qcert_stmt_to_imp_json s2)
    | ImpStmtReturn e =>
      ImpStmtReturn (lift imp_qcert_expr_to_imp_json e)
    end.

  Definition imp_qcert_function_to_imp_json (f:imp_qcert_function) : imp_json_function :=
    match f with
    | ImpFun lv s => ImpFun lv (imp_qcert_stmt_to_imp_json s)
    end.

  Fixpoint imp_qcert_to_imp_json (i:imp_qcert) : imp_json :=
    match i with
    | ImpDef s f i1 =>
      ImpDef s
             (imp_qcert_function_to_imp_json f)
             (imp_qcert_to_imp_json i1)
    | ImpMain s =>
      ImpMain (imp_qcert_stmt_to_imp_json s)
    end.
  
End ImpJsontoJavaScriptAst.
