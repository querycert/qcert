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
Require Import Bool.
Require Import Arith.
Require Import Utils.
Require Import EJsonRuntime.
Require Import Imp.
Require Import ImpEJson.
Require Import JavaScriptAstRuntime.
Require Import ForeignToJavaScriptAst.

Section ImpEJsontoJavaScriptAst.
  Import ListNotations.

  Context {ft:foreign_ejson}.
  Context {ftjast:foreign_ejson_to_ajavascript}.
  Context {fejruntime:foreign_ejson_runtime}.

  Section Util.
    Definition scope l := stat_block l. (* XXX TODO XXX *)
    Definition prog_to_string (x: prog) : string := "". (* XXX TODO: prog_to_string XXX *)

    (* XXX Should be done earlier *)
    Definition box_nat e :=
      expr_object
        ((propname_identifier "$nat"%string,
          propbody_val e)::nil).
    Definition unbox_nat e :=
      expr_member e "$nat"%string.

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

    Definition mk_runtime_call
               (op: imp_ejson_runtime_op) (el: list expr) :=
      call_runtime (string_of_ejson_runtime_op op) el.

    Definition sortCriteria_to_js_ast (sc: string * SortDesc) :=
      let (lbl, c) := sc in
      match c with
      | Ascending =>
        expr_object
          [ (propname_identifier "asc", propbody_val (expr_literal (literal_string lbl))) ]
      | Descending =>
        expr_object
          [ (propname_identifier "desc", propbody_val (expr_literal (literal_string lbl))) ]
      end.

    Definition sortCriterias_to_js_ast (scl: SortCriterias) :=
      expr_array
        (List.map
           (fun sc => Some (sortCriteria_to_js_ast sc))
           scl).

    Definition imp_ejson_op_to_js_ast (op:imp_ejson_op) el : expr :=
      match op with
      | EJsonOpNot => mk_unary_op unary_op_not el
      | EJsonOpNeg => mk_unary_op unary_op_neg el
      | EJsonOpAnd => mk_binary_op binary_op_and el
      | EJsonOpOr => mk_binary_op binary_op_or el
      | EJsonOpLt => mk_binary_op binary_op_lt el
      | EJsonOpLe => mk_binary_op binary_op_le el
      | EJsonOpGt => mk_binary_op binary_op_gt el
      | EJsonOpGe => mk_binary_op binary_op_ge el
      | EJsonOpAddString => mk_binary_op binary_op_add el
      | EJsonOpAddNumber => mk_binary_op binary_op_add el
      | EJsonOpSub => mk_binary_op binary_op_sub el
      | EJsonOpDiv => mk_binary_op binary_op_div el
      | EJsonOpMult => mk_binary_op binary_op_mult el
      | EJsonOpStrictEqual => mk_binary_op binary_op_strict_equal el
      | EJsonOpStrictDisequal => mk_binary_op binary_op_strict_disequal el
      | EJsonOpArray => expr_array (List.map Some el)
      | EJsonOpArrayLength => mk_unary_expr (fun e => box_nat (expr_member e  "length")) el
      | EJsonOpArrayPush => mk_binary_expr array_push el
      | EJsonOpArrayAccess => mk_binary_expr array_get el
      | EJsonOpObject atts => mk_object atts el
      | EJsonOpAccess att => mk_binary_expr expr_access (el++[expr_literal (literal_string att)])
      | EJsonOpHasOwnProperty att => mk_binary_expr object_hasOwnProperty (el++[expr_literal (literal_string att)])
      | EJsonOpMathMin => expr_call (expr_member (expr_identifier "Math") "min") el
      | EJsonOpMathMax => expr_call (expr_member (expr_identifier "Math") "max") el
      | EJsonOpMathMinApply =>
        expr_call
          (expr_member (expr_member (expr_identifier "Math") "min") "apply")
          (expr_identifier "Math" :: el)
      | EJsonOpMathMaxApply =>
        expr_call
          (expr_member (expr_member (expr_identifier "Math") "max") "apply")
          (expr_identifier "Math" :: el)
      | EJsonOpMathPow => expr_call (expr_member (expr_identifier "Math") "pow") el
      | EJsonOpMathExp => expr_call (expr_member (expr_identifier "Math") "exp") el
      | EJsonOpMathAbs => expr_call (expr_member (expr_identifier "Math") "abs") el
      | EJsonOpMathLog => expr_call (expr_member (expr_identifier "Math") "log2") el
      | EJsonOpMathLog10 => expr_call (expr_member (expr_identifier "Math") "log10") el
      | EJsonOpMathSqrt => expr_call (expr_member (expr_identifier "Math") "sqrt") el
      | EJsonOpMathCeil => expr_call (expr_member (expr_identifier "Math") "ceil") el
      | EJsonOpMathFloor => expr_call (expr_member (expr_identifier "Math") "floor") el
      | EJsonOpMathTrunc => expr_call (expr_member (expr_identifier "Math") "trunc") el
      end.

  End Util.

  (** Translation *)
  Section Translation.

    Fixpoint ejson_to_js_ast (json: ejson) : expr :=
      match json with
      | ejnull => expr_literal literal_null
      | ejnumber n => expr_literal (literal_number n)
      | ejbigint n => box_nat (expr_literal (literal_number (float_of_int n)))
      (* XXX Could be replaced by JavaScript BigInt some fix to JsAst XXX *)
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
             (fun (prop: (string * EJson.ejson)) =>
                let (x, v) := prop in
                (propname_identifier x, propbody_val (ejson_to_js_ast v)))
             o)
      | ejforeign fd =>
        foreign_ejson_to_ajavascript_expr fd
      end.

    Fixpoint imp_ejson_expr_to_js_ast (exp: imp_ejson_expr) : expr :=
      match exp with
      | ImpExprError v => mk_expr_error
      | ImpExprVar v => expr_identifier v
      | ImpExprConst j => ejson_to_js_ast j
      | ImpExprOp op el => imp_ejson_op_to_js_ast op (map imp_ejson_expr_to_js_ast el)
      | ImpExprRuntimeCall rop el => mk_runtime_call rop (map imp_ejson_expr_to_js_ast el)
      end.

    Definition decl_to_js_ast (d : var * option imp_expr) :=
      match d with
      | (x, None) => (x, None)
      | (x, Some e) => (x, Some (imp_ejson_expr_to_js_ast e))
      end.

    Fixpoint imp_ejson_stmt_to_js_ast (stmt: imp_ejson_stmt): stat :=
      match stmt with
      | ImpStmtBlock decls stmts =>
        scope
          (stat_let_decl (List.map decl_to_js_ast decls) :: (List.map imp_ejson_stmt_to_js_ast stmts))
      | ImpStmtAssign x e =>
        stat_expr (expr_assign (expr_identifier x) None (imp_ejson_expr_to_js_ast e))
      | ImpStmtFor x e s =>
        let c := imp_ejson_expr_to_js_ast e in
        let prog :=
            prog_intro strictness_true [ element_stat (imp_ejson_stmt_to_js_ast s)]
        in
        let f :=
            expr_function None [x]
                          (funcbody_intro prog (prog_to_string prog))
        in
        call_runtime "iterColl" [c; f]
        (* stat_for_in_let nil x None (imp_ejson_expr_to_js_ast e) *)
        (*                 (imp_ejson_stmt_to_js_ast s) *)
      | ImpStmtForRange x e1 e2 s =>
        stat_for_let
          nil
          [ (x, Some (unbox_nat (imp_ejson_expr_to_js_ast e1))) ]
          (* XXX Use binary_op_le, consistent with semantic of 'for i1 to i2 do ... done' loop *)
          (Some (expr_binary_op (expr_identifier x) binary_op_le (unbox_nat (imp_ejson_expr_to_js_ast e2))))
          (Some (expr_unary_op unary_op_post_incr (expr_identifier x)))
          (imp_ejson_stmt_to_js_ast s)
      | ImpStmtIf e s1 s2 =>
        stat_if
          (imp_ejson_expr_to_js_ast e)
          (imp_ejson_stmt_to_js_ast s1)
          (Some (imp_ejson_stmt_to_js_ast s2))
      end.

    Definition imp_ejson_function_to_js_ast (f: imp_function) : list string * funcbody :=
      match f with
      | ImpFun v s ret =>
        let body := imp_ejson_stmt_to_js_ast s in
        let ret := scope (stat_let_decl ((ret,None)::nil) :: body :: stat_return (Some (expr_identifier ret)) :: nil) in
        let prog :=
            prog_intro strictness_true [ element_stat ret ]
        in
        ([v], funcbody_intro prog (prog_to_string prog))
      end.

    Definition imp_ejson_function_to_funcelement (fname:string) (fbody: imp_function) : element :=
      let (args, body) := imp_ejson_function_to_js_ast fbody in
      element_func_decl fname args body.

    Definition imp_ejson_function_to_funcdecl (fname:string) (fbody: imp_function) : funcdecl :=
      let (args, body) := imp_ejson_function_to_js_ast fbody in
      funcdecl_intro fname args body.

    Definition imp_ejson_function_to_topdecl (fname:string) (fbody: imp_function) : topdecl :=
      elementdecl (imp_ejson_function_to_funcelement fname fbody).

    Definition imp_ejson_to_js_ast (classname:option string) (q: imp) : js_ast :=
      match classname with
      | None =>
        match q with
        | ImpLib l =>
          List.map
            (fun (decl: string * imp_function) =>
               let (fname, fbody) := decl in
               imp_ejson_function_to_topdecl fname fbody)
            l
        end
      | Some cname =>
        let decls :=
            match q with
            | ImpLib l =>
              List.map
                (fun (decl: string * imp_function) =>
                   let (fname, fbody) := decl in
                   imp_ejson_function_to_funcdecl fname fbody)
                l
            end
        in
        classdecl cname decls::nil
      end.

    Definition imp_ejson_to_function (q: imp_ejson) : list topdecl :=
        match q with
        | ImpLib [(fname,fbody)] =>
          (imp_ejson_function_to_topdecl fname fbody)::nil
        | _ => nil
        end.

    Definition imp_ejson_to_method (q: imp_ejson) : list funcdecl :=
        match q with
        | ImpLib [(fname,fbody)] =>
          (imp_ejson_function_to_funcdecl fname fbody)::nil
        | _ => nil
        end.

    Definition imp_ejson_table_to_topdecls (cname:string) (q: list imp_ejson) : list topdecl :=
      classdecl cname (concat (map imp_ejson_to_method q))::nil.

    Definition imp_ejson_table_to_class (cname:string) (q: imp_ejson) : topdecl :=
      match q with
      | ImpLib l =>
        classdecl cname (map (fun xy => imp_ejson_function_to_funcdecl (fst xy) (snd xy)) l)
      end.

  End Translation.

End ImpEJsontoJavaScriptAst.
