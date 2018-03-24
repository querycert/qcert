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

Section NNRCimptoJavaScriptAst.
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
  Require Import JSON.
  Require Import DatatoJSON.

  Context {fruntime:foreign_runtime}.
  Context {ftojson:foreign_to_JSON}.

  Definition prog_to_string (x: prog) : string := "". (* XXX TODO: prog_to_string XXX *)

  (** Standard library *)

  Definition toString e := (* TODO: review *)
    expr_call (expr_identifier "toString") (e::nil).

  Definition empty_array := expr_array nil. (* TODO: review *)

  Definition array_push e1 e2 := (* TODO: review *)
    (* use [array_proto_push_function_object] ? *)
    expr_call (expr_member e1 "push") (e2::nil).

  Definition array_get e1 e2 := (* TODO: review *)
    expr_access e1 e2.

  Definition math_min e1 e2 := (* TODO: review *)
    expr_call (expr_member (expr_identifier "Math") "min") (e1::e2::nil).

  Definition math_pow e1 e2 := (* TODO: review *)
    expr_call (expr_member (expr_identifier "Math") "pow") (e1::e2::nil).

  Definition math_max e1 e2 := (* TODO: review *)
    expr_call (expr_member (expr_identifier "Math") "max") (e1::e2::nil).

  Definition math_min_apply e := (* TODO: review *)
    expr_call
      (expr_member (expr_member (expr_identifier "Math") "min") "apply")
      ((expr_identifier "Math")::e::nil).

  Definition math_max_apply e := (* TODO: review *)
    expr_call
      (expr_member (expr_member (expr_identifier "Math") "max") "apply")
      ((expr_identifier "Math")::e::nil).

  Definition math_abs e := (* TODO: review *)
    expr_call (expr_member (expr_identifier "Math") "abs") (e::nil).

  Definition math_log e := (* TODO: review *)
    expr_call (expr_member (expr_identifier "Math") "log2") (e::nil).

  Definition math_log10 e := (* TODO: review *)
    expr_call (expr_member (expr_identifier "Math") "log10") (e::nil).

  Definition math_sqrt e := (* TODO: review *)
    expr_call (expr_member (expr_identifier "Math") "sqrt") (e::nil).

  Definition math_exp e := (* TODO: review *)
    expr_call (expr_member (expr_identifier "Math") "exp") (e::nil).

  Definition math_ceil e := (* TODO: review *)
    expr_call (expr_member (expr_identifier "Math") "ceil") (e::nil).

  Definition math_floor e := (* TODO: review *)
    expr_call (expr_member (expr_identifier "Math") "floor") (e::nil).

  Definition math_trunc e := (* TODO: review *)
    expr_call (expr_member (expr_identifier "Math") "trunc") (e::nil).


  (** Runtime  functions *)

  Definition brands_to_js_ast sl : expr :=
    expr_array
      (List.map
         (fun s => Some (expr_literal (literal_string s)))
         sl).

  Definition sortCriteria_to_js_ast (sc: string * SortDesc) :=
    let (lbl, c) := sc in
    match c with
    | Ascending =>
      expr_object
        ((propname_identifier "asc", propbody_val (expr_literal (literal_string lbl)))
           :: nil)
    | Descending =>
      expr_object
        ((propname_identifier "desc", propbody_val (expr_literal (literal_string lbl)))
           :: nil)
    end.

  Definition sortCriterias_to_js_ast (scl: SortCriterias) :=
    expr_array
      (List.map
         (fun sc => Some (sortCriteria_to_js_ast sc))
         scl).

  Definition call_runtime (f: string) (args: list expr) : expr:= (* TODO: review *)
    expr_call (expr_identifier f) args.

  Definition runtime_either e :=
    call_runtime "either" (e::nil).

  Definition runtime_toLeft e :=
    call_runtime "toLeft" (e::nil).

  Definition runtime_toRight e :=
    call_runtime "toRight" (e::nil).

  Definition runtime_equal e1 e2 :=
    call_runtime "equal" (e1::e2::nil).

  Definition runtime_concat e1 e2 :=
    call_runtime "concat" (e1::e2::nil).

  Definition runtime_mergeConcat e1 e2 :=
    call_runtime "mergeConcat" (e1::e2::nil).

  Definition runtime_bunion e1 e2 :=
    call_runtime "bunion" (e1::e2::nil).

  Definition runtime_bminus e1 e2 :=
    call_runtime "bminus" (e1::e2::nil).

  Definition runtime_bmin e1 e2 :=
    call_runtime "bmin" (e1::e2::nil).

  Definition runtime_bmax e1 e2 :=
    call_runtime "bmax" (e1::e2::nil).

  Definition runtime_contains e1 e2 :=
    call_runtime "contains" (e1::e2::nil).

  Definition runtime_deref e s :=
    call_runtime "deref" (e::(expr_literal (literal_string s))::nil).

  Definition runtime_remove e s :=
    call_runtime "remove" (e::(expr_literal (literal_string s))::nil).

  Definition runtime_project e sl :=
    call_runtime "project" (e::(brands_to_js_ast sl)::nil).

  Definition runtime_singleton e :=
    call_runtime "singleton" (e::nil).

  Definition runtime_flatten e :=
    call_runtime "flatten" (e::nil).

  Definition runtime_distinct e :=
    call_runtime "distinct" (e::nil).

  Definition runtime_sort e scl :=
    call_runtime "sort" (e::(sortCriterias_to_js_ast scl)::nil).

  Definition runtime_sum e :=
    call_runtime "sum" (e::nil).

  Definition runtime_mean e :=
    call_runtime "arithMean" (e::nil).

  Definition runtime_brand b e :=
    call_runtime "brand" ((brands_to_js_ast b)::e::nil).

  Definition runtime_unbrand e :=
    call_runtime "unbrand" (e::nil).

  Definition runtime_cast b e :=
    call_runtime "cast" ((brands_to_js_ast b)::e::nil).

  Definition runtime_nat_plus e1 e2 :=
    call_runtime "natPlus" (e1::e2::nil).

  Definition runtime_nat_minus e1 e2 :=
    call_runtime "natMinus" (e1::e2::nil).

  Definition runtime_nat_mult e1 e2 :=
    call_runtime "natMult" (e1::e2::nil).

  Definition runtime_nat_div e1 e2 :=
    call_runtime "natDiv" (e1::e2::nil).

  Definition runtime_nat_rem e1 e2 :=
    call_runtime "natRem" (e1::e2::nil).

  Definition runtime_nat_min e1 e2 :=
    call_runtime "natMin" (e1::e2::nil).

  Definition runtime_nat_max e1 e2 :=
    call_runtime "natMax" (e1::e2::nil).

  Definition runtime_nat_abs e :=
    call_runtime "natAbs" (e::nil).

  Definition runtime_nat_log2 e :=
    call_runtime "natLog2" (e::nil).

  Definition runtime_nat_sqrt e :=
    call_runtime "natSqrt" (e::nil).

  Definition runtime_nat_sum e :=
    call_runtime "natSum" (e::nil).

  Definition runtime_nat_min_apply e :=
    call_runtime "natMinApply" (e::nil).
  
  Definition runtime_nat_max_apply e :=
    call_runtime "natMaxApply" (e::nil).
  
  Definition runtime_nat_mean e :=
    call_runtime "natArithMean" (e::nil).
  
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
    expr_object
        ((propname_identifier "left", propbody_val e)
           :: nil).

  Definition mk_right (e: expr) : expr :=
    expr_object
        ((propname_identifier "right", propbody_val e)
           :: nil).

  Fixpoint json_to_js_ast (json: json) : expr :=
    match json with
    | jnil => expr_literal literal_null
    | jnumber n =>
      expr_literal (literal_string "XXX TODO: json_to_js_ast number XXX")
    | jbool b =>
      expr_literal (literal_bool b)
    | jstring s =>
      expr_literal (literal_string s)
    | jarray a =>
      expr_literal (literal_string "XXX TODO: json_to_js_ast array XXX")
    | jobject o =>
      expr_literal (literal_string "XXX TODO: json_to_js_ast object XXX")
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
      expr_binary_op e1' binary_op_lt e2'
    | OpLe =>
      expr_binary_op e1' binary_op_le e2'
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
    | OpForeignBinary opf => (* XXX TODO XXX *)
      expr_literal (literal_string "XXX TODO:  XXX")
    end.

  Definition mk_unary_op op (e':expr) :=
    match op with
    | OpIdentity =>
      e'
    | OpNeg =>
      expr_unary_op unary_op_not e'
    | OpRec s =>
      mk_rec ((s, e') :: nil)
    | OpDot s =>
      runtime_deref e' s
    | OpRecRemove s =>
      runtime_remove e' s
    | OpRecProject sl =>
      runtime_project e' sl
    | OpBag =>
      mk_bag (e'::nil)
    | OpSingleton =>
      runtime_singleton e'
    | OpFlatten =>
      runtime_flatten e'
    | OpDistinct =>
      runtime_distinct e'
    | OpOrderBy scl =>
      runtime_sort e' scl
    | OpCount =>
      expr_member e' "length"
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
    (* | OpSubstring start olen => *)
    (*   "(" ++ e1 ++ ").substring(" ++ toString start ++ *)
    (*       match olen with *)
    (*       | Some len => ", " ++ toString len *)
    (*       | None => "" *)
    (*       end ++ ")" *)
    (* | OpLike pat oescape => *)
    (*   let lc := make_like_clause pat oescape in *)
    (*   let regex := "new RegExp([" ++ (joinStrings "," (map like_clause_to_javascript lc)) ++ "].join(" ++ quotel ++ quotel ++ "))" in *)
    (*   regex ++ ".test(" ++ e1 ++ ")" *)
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
    | OpForeignUnary fu =>
      expr_literal (literal_string "XXX TODO: mk_binary_op foreign XXX") (* XXX TODO XXX *)
    | _ =>
      expr_literal (literal_string "XXX TODO: mk_binary_op XXX") (* XXX TODO: cf. before XXX *)
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

  Fixpoint nnrc_imp_stmt_to_js_ast (stmt: nnrc_imp_stmt): stat :=
    match stmt with
    | NNRCimpSeq s1 s2 =>
      stat_block
        ((nnrc_imp_stmt_to_js_ast s1)
           :: (nnrc_imp_stmt_to_js_ast s2)
           :: nil)
    | NNRCimpLet x e s =>
      scope
        ((stat_var_decl ((x, Some (nnrc_imp_expr_to_js_ast e))::nil))
           :: nil)
    | NNRCimpLetMut x s1 s2 =>
      scope
        ((stat_var_decl ((x, None)::nil))
           :: (nnrc_imp_stmt_to_js_ast s1)
           :: (nnrc_imp_stmt_to_js_ast s2)
           :: nil)
    | NNRCimpLetMutColl x s1 s2 =>
      scope
        ((stat_var_decl ((x, Some (empty_array))::nil))
           :: (nnrc_imp_stmt_to_js_ast s1)
           :: (nnrc_imp_stmt_to_js_ast s2)
           :: nil)
    | NNRCimpAssign x e =>
      stat_expr (expr_assign (expr_identifier x) None (nnrc_imp_expr_to_js_ast e))
    | NNRCimpPush x e =>
      stat_expr (array_push (expr_identifier x) (nnrc_imp_expr_to_js_ast e))
    | NNRCimpFor x (NNRCimpVar c) s =>
      (* for (var x in c) { x = c[x]; s} *)
      let c := expr_identifier c in
      scope
        ((stat_for_in_var nil x None c
           (stat_block
              ((stat_expr (expr_assign (expr_identifier x) None
                                       (array_get c (expr_identifier x))))
                 :: (nnrc_imp_stmt_to_js_ast s)
                 :: nil)))
           :: nil)
    | NNRCimpFor x e s =>
      (* XXX TODO: introduce a variable for e here or earlier in compilation? XXX *)
      let c := nnrc_imp_expr_to_js_ast e in
      scope
        ((stat_for_in_var nil x None c
           (stat_block
              ((stat_expr (expr_assign (expr_identifier x) None
                                       (array_get c (expr_identifier x))))
                 :: (nnrc_imp_stmt_to_js_ast s)
                 :: nil)))
           :: nil)
    | NNRCimpIf e s1 s2 =>
      stat_if
        (nnrc_imp_expr_to_js_ast e)
        (nnrc_imp_stmt_to_js_ast s1)
        (Some (nnrc_imp_stmt_to_js_ast s2))
    | NNRCimpEither (NNRCimpVar x) x1 s1 x2 s2 =>
      let e' := expr_identifier x  in
      stat_if
        (runtime_either e')
        (scope (* var x1 = toLeft(e); s1 *)
           ((stat_var_decl ((x1, Some (runtime_toLeft e')):: nil))
              :: (nnrc_imp_stmt_to_js_ast s1)
              :: nil))
        (Some (scope (* var x2 = toRight(e); s2 *)
                 ((stat_var_decl ((x2, Some (runtime_toRight e')):: nil))
                    :: (nnrc_imp_stmt_to_js_ast s2)
                    :: nil)))
    | NNRCimpEither e x1 s1 x2 s2 =>
      (* XXX TODO: introduce a variable for e here or earlier in compilation? XXX *)
      let e' := nnrc_imp_expr_to_js_ast e in
      stat_if
        (runtime_either e')
        (scope (* var x1 = toLeft(e); s1 *)
           ((stat_var_decl ((x1, Some (runtime_toLeft e')):: nil))
              :: (nnrc_imp_stmt_to_js_ast s1)
              :: nil))
        (Some (scope (* var x2 = toRight(e); s2 *)
                 ((stat_var_decl ((x2, Some (runtime_toRight e')):: nil))
                    :: (nnrc_imp_stmt_to_js_ast s2)
                    :: nil)))
    end.

  Definition nnrc_imp_to_js_ast_top globals (q: nnrc_imp): funcdecl :=
    let (stmt, ret) := q in
    let body :=
      stat_block
        ((stat_var_decl ((ret, None)::nil))
           :: (nnrc_imp_stmt_to_js_ast stmt)
           :: (stat_return (Some (expr_identifier ret)))
           :: nil)
    in
    let prog := prog_intro strictness_true ((element_stat body)::nil) in
    funcdecl_intro
      "query"
      globals
      (funcbody_intro prog (prog_to_string prog))
  .

  (* (* Examples *) *)
  (* Definition ex1 := *)
  (*   let ret := "ret"%string in *)
  (*   let body := *)
  (*     NNRCimpLet "x"%string (NNRCimpConst (dnat 42)) *)
  (*                (NNRCimpAssign ret (NNRCimpVar "x"%string)) *)
  (*   in *)
  (*   (body, ret). *)
  (* Definition js1 := (nnrc_imp_to_js_ast_top nil ex1). *)
  (* Remark print1: Some js1 = None. *)
  (* Proof. *)
  (*   unfold js1. *)
  (*   unfold nnrc_imp_to_js_ast_top. *)
  (*   simpl. *)
  (* Qed. *)

End NNRCimptoJavaScriptAst.