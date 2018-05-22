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
Require Import EquivDec.
Require Import Morphisms.
Require Import Permutation.
Require Import Eqdep_dec.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRCimpRuntime.
Require Import JavaScriptAstRuntime.
Require Import ForeignToJavaScriptAst.
Require Import JSON.
Require Import DatatoJSON.
Require Import JsAst.JsNumber.
Require Import Fresh.

Section NNRCimptoJavaScriptAst.
  Import ListNotations.

  Context {fruntime:foreign_runtime}.
  Context {ftoajavascript:foreign_to_ajavascript}.
  Context {ftojson:foreign_to_JSON}.

  Definition prog_to_string (x: prog) : string := "". (* XXX TODO: prog_to_string XXX *)

  (** Standard library *)

  (* TODO: review the standard library *)

  Definition toString e :=
    expr_call (expr_identifier "toString") [ e ].

  Definition substring e start len_opt :=
    let start := expr_literal (literal_number (start)) in
    let args :=
      match len_opt with
      | None => [ start ]
      | Some len => [ start; len ]
      end
    in
    expr_call (expr_member e "substring") args.

  Definition math_min e1 e2 :=
    expr_call (expr_member (expr_identifier "Math") "min") [ e1; e2 ].

  Definition math_pow e1 e2 :=
    expr_call (expr_member (expr_identifier "Math") "pow") [ e1; e2 ].

  Definition math_max e1 e2 :=
    expr_call (expr_member (expr_identifier "Math") "max") [ e1; e2 ].

  Definition math_min_apply e :=
    expr_call
      (expr_member (expr_member (expr_identifier "Math") "min") "apply")
      [ expr_identifier "Math"; e ].

  Definition math_max_apply e :=
    expr_call
      (expr_member (expr_member (expr_identifier "Math") "max") "apply")
      [ expr_identifier "Math"; e ].

  Definition math_abs e :=
    expr_call (expr_member (expr_identifier "Math") "abs") [ e ].

  Definition math_log e :=
    expr_call (expr_member (expr_identifier "Math") "log2") [ e ].

  Definition math_log10 e :=
    expr_call (expr_member (expr_identifier "Math") "log10") [ e ].

  Definition math_sqrt e :=
    expr_call (expr_member (expr_identifier "Math") "sqrt") [ e ].

  Definition math_exp e :=
    expr_call (expr_member (expr_identifier "Math") "exp") [ e ].

  Definition math_ceil e :=
    expr_call (expr_member (expr_identifier "Math") "ceil") [ e ].

  Definition math_floor e :=
    expr_call (expr_member (expr_identifier "Math") "floor") [ e ].

  Definition math_trunc e :=
    expr_call (expr_member (expr_identifier "Math") "trunc") [ e ].


  Definition runtime_either e :=
    call_runtime "either" [ e ].

  Definition runtime_toLeft e :=
    call_runtime "toLeft" [ e ].

  Definition runtime_toRight e :=
    call_runtime "toRight" [ e ].

  Definition runtime_equal e1 e2 :=
    call_runtime "equal" [ e1; e2 ].

  Definition runtime_concat e1 e2 :=
    call_runtime "concat" [ e1; e2 ].

  Definition runtime_mergeConcat e1 e2 :=
    call_runtime "mergeConcat" [ e1; e2 ].

  Definition runtime_bunion e1 e2 :=
    call_runtime "bunion" [ e1; e2 ].

  Definition runtime_bminus e1 e2 :=
    call_runtime "bminus" [ e1; e2 ].

  Definition runtime_bmin e1 e2 :=
    call_runtime "bmin" [ e1; e2 ].

  Definition runtime_bmax e1 e2 :=
    call_runtime "bmax" [ e1; e2 ].

  Definition runtime_contains e1 e2 :=
    call_runtime "contains" [ e1; e2 ].

  Definition runtime_deref e s :=
    call_runtime "deref" [ e; expr_literal (literal_string s) ].

  Definition runtime_remove e s :=
    call_runtime "remove" [ e; expr_literal (literal_string s) ].

  Definition runtime_project e sl :=
    call_runtime "project" [ e; brands_to_js_ast sl ].

  Definition runtime_singleton e :=
    call_runtime "singleton" [ e ].

  Definition runtime_flatten e :=
    call_runtime "flatten" [ e ].

  Definition runtime_distinct e :=
    call_runtime "distinct" [ e ].

  Definition runtime_sort e scl :=
    call_runtime "sort" [ e; sortCriterias_to_js_ast scl ].

  Definition runtime_sum e :=
    call_runtime "sum" [ e ].

  Definition runtime_mean e :=
    call_runtime "arithMean" [ e ].

  Definition runtime_brand b e :=
    call_runtime "brand" [ brands_to_js_ast b; e ].

  Definition runtime_unbrand e :=
    call_runtime "unbrand" [ e ].

  Definition runtime_cast b e :=
    call_runtime "cast" [ brands_to_js_ast b; e ].

  Definition runtime_nat_plus e1 e2 :=
    call_runtime "natPlus" [ e1; e2 ].

  Definition runtime_nat_minus e1 e2 :=
    call_runtime "natMinus" [ e1; e2 ].

  Definition runtime_nat_mult e1 e2 :=
    call_runtime "natMult" [ e1; e2 ].

  Definition runtime_nat_div e1 e2 :=
    call_runtime "natDiv" [ e1; e2 ].

  Definition runtime_nat_rem e1 e2 :=
    call_runtime "natRem" [ e1; e2 ].

  Definition runtime_nat_min e1 e2 :=
    call_runtime "natMin" [ e1; e2 ].

  Definition runtime_nat_max e1 e2 :=
    call_runtime "natMax" [ e1; e2 ].

  Definition runtime_nat_abs e :=
    call_runtime "natAbs" [ e ].

  Definition runtime_nat_log2 e :=
    call_runtime "natLog2" [ e ].

  Definition runtime_nat_sqrt e :=
    call_runtime "natSqrt" [ e ].

  Definition runtime_nat_sum e :=
    call_runtime "natSum" [ e ].

  Definition runtime_nat_min_apply e :=
    call_runtime "natMinApply" [ e ].

  Definition runtime_nat_max_apply e :=
    call_runtime "natMaxApply" [ e ].

  Definition runtime_nat_mean e :=
    call_runtime "natArithMean" [ e ].

  Definition runtime_compare e1 e2 :=
    call_runtime "compare" [ e1; e2 ].

  Definition runtime_count e :=
    call_runtime "count"
                 [ e ].

  Definition runtime_floatOfNat e :=
    call_runtime "floatOfNat"
                 [ e ].

  Definition runtime_substring start len e :=
    call_runtime "substring"
                 [ e;
                   expr_literal (literal_number start);
                   expr_literal (literal_number len) ].

  Definition runtime_substringNoLength start e :=
    call_runtime "substringNoLength"
                 [ e;
                   expr_literal (literal_number start) ].

  (** Data model *)

  Definition mk_rec (l: list (string * expr)) : expr :=
    expr_object
      (List.map
         (fun (entry: string * expr) =>
            let (lbl, e) := entry in
            (propname_identifier lbl, propbody_val e))
         l).

  Definition mk_bag (l: list expr) : expr :=
    expr_array (List.map (fun e => Some e) l).

  Definition mk_left (e: expr) : expr :=
    expr_object [ (propname_identifier "left", propbody_val e) ].

  Definition mk_right (e: expr) : expr :=
    expr_object [(propname_identifier "right", propbody_val e) ].

  Fixpoint json_to_js_ast (json: json) : expr :=
    match json with
    | jnil => expr_literal literal_null
    | jnumber n =>
      expr_literal (literal_number n)
    | jbool b =>
      expr_literal (literal_bool b)
    | jstring s =>
      expr_literal (literal_string s)
    | jarray a =>
      let a :=
          List.map
            (fun v => Some (json_to_js_ast v))
            a
      in
      expr_array a
    | jobject o =>
      expr_object
        (List.map
           (fun (prop: (string * JSON.json)) =>
              let (x, v) := prop in
              (propname_identifier x, propbody_val (json_to_js_ast v)))
           o)
    end.

  Definition data_to_js_ast (d: data) : expr :=
    let json :=
        (* XXX TODO: is it the good choice vs data_enhanced_to_json XXX *)
        data_to_json d
    in
    json_to_js_ast json.


  (** Translation *)

  Definition scope l := stat_block l. (* XXX TODO XXX *)

  Definition mk_binary_op op (e1':expr) (e2':expr) : expr :=
    match op with
    | OpEqual =>
      runtime_equal e1' e2'
    | OpRecConcat =>
      runtime_concat e1' e2'
    | OpRecMerge =>
      runtime_mergeConcat e1' e2'
    | OpAnd =>
      expr_binary_op e1' binary_op_and e2'
    | OpOr =>
      expr_binary_op e1' binary_op_or e2'
    | OpLt =>
      expr_binary_op (runtime_compare e1' e2')
                     binary_op_lt
                     (expr_literal (literal_number zero))
    | OpLe =>
      expr_binary_op (runtime_compare e1' e2')
                     binary_op_le
                     (expr_literal (literal_number zero))
    | OpBagUnion =>
      runtime_bunion e1' e2'
    | OpBagDiff =>
      runtime_bminus e1' e2'
    | OpBagMin =>
      runtime_bmin e1' e2'
    | OpBagMax =>
      runtime_bmax e1' e2'
    | OpContains =>
      runtime_contains e1' e2'
    | OpStringConcat =>
      expr_binary_op e1' binary_op_add e2'
    | OpNatBinary opa =>
      match opa with
      | NatPlus =>
        runtime_nat_plus e1' e2'
      | NatMinus =>
        runtime_nat_plus e1' e2'
      | NatMult =>
        runtime_nat_mult e1' e2'
      | NatDiv =>
        runtime_nat_div e1' e2'
      | NatRem =>
        runtime_nat_rem e1' e2'
      | NatMin =>
        runtime_nat_min e1' e2'
      | NatMax =>
        runtime_nat_max e1' e2'
      end
    | OpFloatBinary opa =>
      match opa with
      | FloatPlus =>
        expr_binary_op e1' binary_op_add e2'
      | FloatMinus =>
        expr_binary_op e1' binary_op_sub e2'
      | FloatMult =>
        expr_binary_op e1' binary_op_mult e2'
      | FloatDiv =>
        expr_binary_op e1' binary_op_div e2'
      | FloatPow =>
        math_pow e1' e2'
      | FloatMin =>
        math_min e1' e2'
      | FloatMax =>
        math_max e1' e2'
      end
    | OpFloatCompare opa =>
      match opa with
      | FloatLt =>
        expr_binary_op e1' binary_op_lt e2'
      | FloatLe =>
        expr_binary_op e1' binary_op_le e2'
      | FloatGt =>
        expr_binary_op e1' binary_op_gt e2'
      | FloatGe =>
        expr_binary_op e1' binary_op_ge e2'
      end
    | OpForeignBinary fb =>
      foreign_to_ajavascript_binary_op fb e1' e2'
    end.

  Definition mk_unary_op op (e':expr) :=
    match op with
    | OpIdentity =>
      e'
    | OpNeg =>
      expr_unary_op unary_op_not e'
    | OpRec s =>
      mk_rec [ (s, e') ]
    | OpDot s =>
      runtime_deref e' s
    | OpRecRemove s =>
      runtime_remove e' s
    | OpRecProject sl =>
      runtime_project e' sl
    | OpBag =>
      mk_bag [ e' ]
    | OpSingleton =>
      runtime_singleton e'
    | OpFlatten =>
      runtime_flatten e'
    | OpDistinct =>
      runtime_distinct e'
    | OpOrderBy scl =>
      runtime_sort e' scl
    | OpCount =>
      runtime_count e'
    | OpNatSum =>
      runtime_nat_sum e'
    | OpNatMin =>
      runtime_nat_min_apply e'
    | OpNatMax =>
      runtime_nat_max_apply e'
    | OpNatMean =>
      runtime_nat_mean e'
    | OpToString =>
      toString e'
    | OpSubstring start olen =>
      let start_num := float_of_int start in
      match olen with
      | None =>
        runtime_substringNoLength start_num e'
      | Some len =>
        let len_num := float_of_int len
        in runtime_substring start_num len_num e'
      end
    | OpLike pat oescape =>
    (*   let lc := make_like_clause pat oescape in *)
    (*   let regex := "new RegExp([" ++ (joinStrings "," (map like_clause_to_javascript lc)) ++ "].join(" ++ quotel ++ quotel ++ "))" in *)
    (*   regex ++ ".test(" ++ e1 ++ ")" *)
      expr_literal (literal_string "XXX TODO: mk_binary_op OpLike XXX") (* XXX TODO XXX *)
    | OpLeft =>
      mk_left e'
    | OpRight =>
      mk_right e'
    | OpBrand b =>
      runtime_brand b e'
    | OpUnbrand =>
      runtime_unbrand e'
    | OpCast b =>
      runtime_cast b e'
    | OpNatUnary u =>
      match u with
      | NatAbs => runtime_nat_abs e'
      | NatLog2 => runtime_nat_log2 e'
      | NatSqrt => runtime_nat_sqrt e'
      end
    | OpFloatUnary u =>
      match u with
      | FloatNeg => expr_unary_op unary_op_neg e'
      | FloatSqrt => math_sqrt e'
      | FloatExp => math_exp e'
      | FloatLog => math_log e'
      | FloatLog10 => math_log10 e'
      | FloatCeil => math_ceil e'
      | FloatFloor => math_floor e'
      | FloatAbs => math_abs e'
      end
    | OpFloatTruncate =>
      math_trunc e'
    | OpFloatSum =>
      runtime_sum e'
    | OpFloatMean =>
      runtime_mean e'
    | OpFloatBagMin =>
      math_min_apply e'
    | OpFloatBagMax =>
      math_max_apply e'
    | OpFloatOfNat =>
      runtime_floatOfNat e'
    | OpForeignUnary fu =>
      foreign_to_ajavascript_unary_op fu e'
    end.

  Fixpoint nnrc_imp_expr_to_js_ast (exp: nnrc_imp_expr): expr :=
    match exp with
    | NNRCimpGetConstant x =>
      expr_identifier x
    | NNRCimpVar x =>
      expr_identifier x
    | NNRCimpConst d =>
      data_to_js_ast d
    | NNRCimpBinop op e1 e2 =>
      let e1' := nnrc_imp_expr_to_js_ast e1 in
      let e2' := nnrc_imp_expr_to_js_ast e2 in
      mk_binary_op op e1' e2'
    | NNRCimpUnop op e =>
      let e' := nnrc_imp_expr_to_js_ast e in
      mk_unary_op op e'
    | NNRCimpGroupBy _ _ _ => (* XXX TODO XXX *)
      expr_literal (literal_string "XXX TODO: nnrc_imp_expr_to_js_ast groupby XXX")
    end.

  Fixpoint nnrc_imp_stmt_to_js_ast (avoid: list string) (stmt: nnrc_imp_stmt): stat :=
    match stmt with
    | NNRCimpSeq s1 s2 =>
      stat_block
        [ nnrc_imp_stmt_to_js_ast avoid s1;
          nnrc_imp_stmt_to_js_ast avoid s2 ]
    | NNRCimpLet x e s =>
      let avoid := x :: avoid in
      scope
        [ stat_var_decl [ (x, lift nnrc_imp_expr_to_js_ast e) ] ]
    (* | NNRCimpLetMut x s1 s2 => *)
    (*   let avoid := x :: avoid in *)
    (*   scope *)
    (*     [ stat_var_decl [ (x, None) ]; *)
    (*       nnrc_imp_stmt_to_js_ast avoid s1; *)
    (*       nnrc_imp_stmt_to_js_ast avoid s2 ] *)
    (* | NNRCimpLetMutColl x s1 s2 => *)
    (*   let avoid := x :: avoid in *)
    (*   scope *)
    (*     [ stat_var_decl [ (x, Some (empty_array)) ]; *)
    (*       nnrc_imp_stmt_to_js_ast avoid s1; *)
    (*       nnrc_imp_stmt_to_js_ast avoid s2 ] *)
    | NNRCimpAssign x e =>
      stat_expr (expr_assign (expr_identifier x) None (nnrc_imp_expr_to_js_ast e))
    (* | NNRCimpPush x e => *)
    (*   stat_expr (array_push (expr_identifier x) (nnrc_imp_expr_to_js_ast e)) *)
    | NNRCimpFor x e s =>
      (* for (var src = e, i = 0; i < src.length; i++) { var x = src[i]; s } *)
      let avoid := x :: avoid in
      let e := nnrc_imp_expr_to_js_ast e in
      let src_id := fresh_var "src" avoid in
      let avoid := src_id :: avoid in
      let i_id := fresh_var "i" avoid in
      let avoid := i_id :: avoid in
      let src := expr_identifier src_id in
      let i := expr_identifier i_id in
      scope
        [ stat_for_var
            nil
            [ (src_id, Some e); (i_id, Some (expr_literal (literal_number zero))) ]
            (Some (expr_binary_op i binary_op_lt (expr_member src "length")))
            (Some (expr_unary_op unary_op_post_incr i))
            (stat_block
               [ stat_var_decl [ (x, Some (array_get src i)) ];
                   nnrc_imp_stmt_to_js_ast avoid s ]) ]
    | NNRCimpIf e s1 s2 =>
      stat_if
        (nnrc_imp_expr_to_js_ast e)
        (nnrc_imp_stmt_to_js_ast avoid s1)
        (Some (nnrc_imp_stmt_to_js_ast avoid s2))
    | NNRCimpEither (NNRCimpVar x) x1 s1 x2 s2 =>
      let avoid := x1 :: x2 :: avoid in
      let e' := expr_identifier x  in
      stat_if
        (runtime_either e')
        (scope (* var x1 = toLeft(e); s1 *)
           [ stat_var_decl [ (x1, Some (runtime_toLeft e')) ];
             nnrc_imp_stmt_to_js_ast avoid s1 ])
        (Some (scope (* var x2 = toRight(e); s2 *)
                 [ stat_var_decl [ (x2, Some (runtime_toRight e')) ];
                   nnrc_imp_stmt_to_js_ast avoid s2 ]))
    | NNRCimpEither e x1 s1 x2 s2 =>
      (* XXX TODO: introduce a variable for e here or earlier in compilation? XXX *)
      let e' := nnrc_imp_expr_to_js_ast e in
      stat_if
        (runtime_either e')
        (scope (* var x1 = toLeft(e); s1 *)
           [ stat_var_decl [ (x1, Some (runtime_toLeft e')) ];
             nnrc_imp_stmt_to_js_ast avoid s1 ])
        (Some (scope (* var x2 = toRight(e); s2 *)
                 [ stat_var_decl [ (x2, Some (runtime_toRight e')) ];
                   nnrc_imp_stmt_to_js_ast avoid s2 ]))
    end.

  Definition nnrc_imp_to_js_ast_top globals (q: nnrc_imp): funcdecl :=
    let constants := "constants"%string in
    let (stmt, ret) := q in
    let body :=
      stat_block
        [ stat_var_decl
            (List.map
               (fun x => (x, Some (runtime_deref (expr_identifier constants) x)))
               globals);
          stat_var_decl [ (ret, None) ];
          nnrc_imp_stmt_to_js_ast globals stmt;
          stat_return (Some (expr_identifier ret)) ]
    in
    let prog := prog_intro strictness_true [ element_stat body ] in
    funcdecl_intro
      "query"
      [ constants ]
      (funcbody_intro prog (prog_to_string prog))
  .

End NNRCimptoJavaScriptAst.
