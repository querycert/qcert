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
Require Import ForeignEJSONtoJavaScriptAst.

Section ImpJsontoJavaScriptAst.
  Import ListNotations.

  Section Util.
    Definition scope l := stat_block l. (* XXX TODO XXX *)
    Definition prog_to_string (x: prog) : string := "". (* XXX TODO: prog_to_string XXX *)

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

    Definition mk_runtime_call (op: imp_json_runtime_op) (el: list expr) :=
      call_runtime (string_of_json_runtime_op op) el.

    Definition imp_json_op_to_js_ast (op:imp_json_op) el : expr :=
      match op with
      | EJSONOpNot => mk_unary_op unary_op_not el
      | EJSONOpNeg => mk_unary_op unary_op_neg el
      | EJSONOpAnd => mk_binary_op binary_op_and el
      | EJSONOpOr => mk_binary_op binary_op_or el
      | EJSONOpLt => mk_binary_op binary_op_lt el
      | EJSONOpLe => mk_binary_op binary_op_le el
      | EJSONOpGt => mk_binary_op binary_op_gt el
      | EJSONOpGe => mk_binary_op binary_op_ge el
      | EJSONOpAddString => mk_binary_op binary_op_add el
      | EJSONOpAddNumber => mk_binary_op binary_op_add el
      | EJSONOpSub => mk_binary_op binary_op_sub el
      | EJSONOpDiv => mk_binary_op binary_op_div el
      | EJSONOpMult => mk_binary_op binary_op_mult el
      | EJSONOpStrictEqual => mk_binary_op binary_op_strict_equal el
      | EJSONOpStrictDisequal => mk_binary_op binary_op_strict_disequal el
      | EJSONOpArray => expr_array (List.map Some el)
      | EJSONOpArrayLength => mk_unary_expr (fun e => expr_member e  "length") el
      | EJSONOpArrayPush => mk_binary_expr array_push el
      | EJSONOpArrayAccess => mk_binary_expr array_get el
      | EJSONOpObject atts => mk_object atts el
      | EJSONOpAccess att => mk_binary_expr expr_access (el++[expr_literal (literal_string att)])
      | EJSONOpHasOwnProperty att => mk_binary_expr object_hasOwnProperty (el++[expr_literal (literal_string att)])
      | EJSONOpToString => expr_call (expr_identifier "toString") el
      | EJSONOpMathMin => expr_call (expr_member (expr_identifier "Math") "min") el
      | EJSONOpMathMax => expr_call (expr_member (expr_identifier "Math") "max") el
      | EJSONOpMathMinApply =>
        expr_call
          (expr_member (expr_member (expr_identifier "Math") "min") "apply")
          (expr_identifier "Math" :: el)
      | EJSONOpMathMaxApply =>
        expr_call
          (expr_member (expr_member (expr_identifier "Math") "max") "apply")
          (expr_identifier "Math" :: el)
      | EJSONOpMathPow => expr_call (expr_member (expr_identifier "Math") "pow") el
      | EJSONOpMathExp => expr_call (expr_member (expr_identifier "Math") "exp") el
      | EJSONOpMathAbs => expr_call (expr_member (expr_identifier "Math") "abs") el
      | EJSONOpMathLog => expr_call (expr_member (expr_identifier "Math") "log2") el
      | EJSONOpMathLog10 => expr_call (expr_member (expr_identifier "Math") "log10") el
      | EJSONOpMathSqrt => expr_call (expr_member (expr_identifier "Math") "sqrt") el
      | EJSONOpMathCeil => expr_call (expr_member (expr_identifier "Math") "ceil") el
      | EJSONOpMathFloor => expr_call (expr_member (expr_identifier "Math") "floor") el
      | EJSONOpMathTrunc => expr_call (expr_member (expr_identifier "Math") "trunc") el
      end.

  End Util.

  (** Translation *)
  Section Translation.

    Context {ft:foreign_ejson}.
    Context {ftjast:foreign_ejson_to_ajavascript}.
  
    Fixpoint ejson_to_js_ast (json: ejson) : expr :=
      match json with
      | ejnull => expr_literal literal_null
      | ejnumber n => expr_literal (literal_number n)
      | ejbigint n => expr_literal (literal_number (float_of_int n)) (* XXX Could be replaced by JavaScript BigInt some fix to JsAst XXX *)
      | ejbool b => expr_literal (literal_bool b)
      | ejstring s => expr_literal (literal_string s)
      | ejarray a =>
        let a :=
            List.map
              (fun v => Some (ejson_to_js_ast v))
              a
        in
        expr_array a
      | ejobject o =>
        expr_object
          (List.map
             (fun (prop: (string * EJSON.ejson)) =>
                let (x, v) := prop in
                (propname_identifier x, propbody_val (ejson_to_js_ast v)))
             o)
      | ejforeign fd =>
        foreign_ejson_to_ajavascript_expr fd
      end.

    Fixpoint imp_json_expr_to_js_ast (exp: imp_json_expr) : expr :=
      match exp with
      | ImpExprError v => mk_expr_error
      | ImpExprVar v => expr_identifier v
      | ImpExprConst j => ejson_to_js_ast j
      | ImpExprOp op el => imp_json_op_to_js_ast op (map imp_json_expr_to_js_ast el)
      | ImpExprRuntimeCall rop el => mk_runtime_call rop (map imp_json_expr_to_js_ast el)
      end.

    Definition decl_to_js_ast (d : var * option imp_expr) :=
      match d with
      | (x, None) => (x, None)
      | (x, Some e) => (x, Some (imp_json_expr_to_js_ast e))
      end.

    Fixpoint imp_json_stmt_to_js_ast (stmt: imp_json_stmt): stat :=
      match stmt with
      | ImpStmtBlock decls stmts =>
        scope
          (stat_let_decl (List.map decl_to_js_ast decls) :: (List.map imp_json_stmt_to_js_ast stmts))
      | ImpStmtAssign x e =>
        stat_expr (expr_assign (expr_identifier x) None (imp_json_expr_to_js_ast e))
      | ImpStmtFor x e s =>
        stat_for_in_let nil x None (imp_json_expr_to_js_ast e)
                        (imp_json_stmt_to_js_ast s)
      | ImpStmtForRange x e1 e2 s =>
        stat_for_let
          nil
          [ (x, Some (imp_json_expr_to_js_ast e1)) ]
          (Some (expr_binary_op (expr_identifier x) binary_op_lt (imp_json_expr_to_js_ast e2)))
          (Some (expr_unary_op unary_op_post_incr (expr_identifier x)))
          (imp_json_stmt_to_js_ast s)
      | ImpStmtIf e s1 s2 =>
        stat_if
          (imp_json_expr_to_js_ast e)
          (imp_json_stmt_to_js_ast s1)
          (Some (imp_json_stmt_to_js_ast s2))
      end.

    Definition imp_json_function_to_js_ast (f: imp_function) : list string * funcbody :=
      match f with
      | ImpFun v s ret =>
        let body := imp_json_stmt_to_js_ast s in
        let ret := scope (body :: stat_return (Some (expr_identifier ret)) :: nil) in
        let prog :=
            prog_intro strictness_true [ element_stat ret ]
        in
        ([v], funcbody_intro prog (prog_to_string prog))
      end.

    Definition imp_json_to_js_ast (q: imp) : list funcdecl :=
      match q with
      | ImpLib l =>
        List.map
          (fun (decl: string * imp_function) =>
             let (x, f) := decl in
             let (args, body) := imp_json_function_to_js_ast f in
             funcdecl_intro x args body)
          l
      end.
  End Translation.

End ImpJsontoJavaScriptAst.
