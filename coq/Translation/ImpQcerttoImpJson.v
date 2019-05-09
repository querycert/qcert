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
Require Import CommonRuntime.
Require Import Imp.
Require Import ImpQcert.
Require Import ImpJson.
Require Import JsAst.JsNumber.
Require Import Fresh.

Section ImpJsontoJavaScriptAst.
  Import ListNotations.

  Context {fruntime:foreign_runtime}.
  Context {ftojson:foreign_to_JSON}.

  (** Translation *)


  Definition mk_imp_json_expr_error msg : imp_json_expr :=
    ImpExprConst (jstring msg).
  Definition mk_imp_json_op op el : imp_json_expr := ImpExprOp op el.
  Definition mk_imp_json_runtime_call op el : imp_json_expr := ImpExprRuntimeCall op el.

  Definition mk_string s : imp_json_expr := ImpExprConst (jstring s).
  Definition mk_bag el : imp_json_expr := mk_imp_json_op JSONOpArray el.
  Definition mk_left e : imp_json_expr :=
    mk_imp_json_op (JSONOpObject ["left"%string]) [ e ].
  Definition mk_right e : imp_json_expr :=
    mk_imp_json_op (JSONOpObject ["right"%string]) [ e ].


  Definition sortCriteria_to_json_expr (sc: string * SortDesc) : imp_json_expr :=
    let (lbl, c) := sc in
    let o :=
        match c with
        | Ascending => jobject [ ("asc"%string, jstring lbl) ]
        | Descending => jobject [ ("desc"%string, jstring lbl) ]
        end
    in
    ImpExprConst o.

  Definition brands_to_json_expr sl : imp_json_expr :=
    let j := jarray ((List.map (fun s => jstring s)) sl) in
    ImpExprConst j.

  Definition imp_qcert_unary_op_to_imp_json (op:unary_op) el : imp_json_expr :=
    match op with
    | OpIdentity =>
      match el with
      | [e] => e
      | _ => mk_imp_json_expr_error "OpIdentity: wrong number of arguments"
      end
    | OpNeg => mk_imp_json_op JSONOpNeg el
    | OpRec s => mk_imp_json_op (JSONOpObject [s]) el
    | OpDot s => mk_imp_json_op (JSONOpAccess s) el
    | OpRecRemove f =>
      match el with
      | [e] => mk_imp_json_runtime_call JSONRuntimeRemove [e; mk_string f ]
      | _ => mk_imp_json_expr_error "OpRecRemove: wrong number of arguments"
      end
    | OpRecProject fl =>
      match el with
      | [e] =>
        mk_imp_json_runtime_call
          JSONRuntimeProject ((List.map mk_string fl) ++ [ e ])
      | _ => mk_imp_json_expr_error "OpRecProject: wrong number of arguments"
      end
    | OpBag => mk_bag el
    | OpSingleton => mk_imp_json_runtime_call JSONRuntimeSingleton el
    | OpFlatten => mk_imp_json_runtime_call JSONRuntimeFlatten el
    | OpDistinct => mk_imp_json_runtime_call JSONRuntimeDistinct el
    | OpOrderBy scl =>
      match el with
      | [e] =>
        mk_imp_json_runtime_call
          JSONRuntimeSort (e :: (List.map sortCriteria_to_json_expr scl))
      | _ => mk_imp_json_expr_error "OpOrderBy: wrong number of arguments"
      end
    | OpCount => mk_imp_json_runtime_call JSONRuntimeCount el
    | OpToString => mk_imp_json_op JSONOpToString el
    | OpSubstring start len =>
      match el with
      | [e] =>
        let start :=
            (* XXX TODO XXX *)
            ImpExprConst jnull
            (* ImpExprConst (jnumber start) *)
        in
        let args :=
            match len with
            | None => [ e; start ]
            | Some length =>
              let len :=
                  ImpExprConst jnull
                  (* ImpExprConst (jnumber start) *)
              in
              [ e; start; len ]
            end
        in
        mk_imp_json_runtime_call JSONRuntimeSubstring args
      | _ => mk_imp_json_expr_error "OpSubstring: wrong number of arguments"
      end
    | OpLike pat oescape =>
      mk_imp_json_expr_error "XXX TODO: ImpQcerttoImpJson: OpLike XXX"
    | OpLeft =>
      match el with
      | [e] => mk_left e
      | _ => mk_imp_json_expr_error "OpLeft: wrong number of arguments"
      end
    | OpRight =>
      match el with
      | [e] => mk_right e
      | _ => mk_imp_json_expr_error "OpRight: wrong number of arguments"
      end
    | OpBrand b =>
      match el with
      | [e] =>
        mk_imp_json_runtime_call JSONRuntimeBrand [ brands_to_json_expr b; e ]
      | _ => mk_imp_json_expr_error "OpBrand: wrong number of arguments"
      end
    | OpUnbrand => mk_imp_json_runtime_call JSONRuntimeUnbrand el
    | OpCast b =>
      match el with
      | [e] =>
        mk_imp_json_runtime_call JSONRuntimeCast [ brands_to_json_expr b; e ]
      | _ => mk_imp_json_expr_error "OpCast: wrong number of arguments"
      end
    | OpNatUnary u =>
      match el with
      | [e] =>
        let op :=
            match u with
            | NatAbs => JSONRuntimeNatAbs
            | NatLog2 => JSONRuntimeNatLog2
            | NatSqrt => JSONRuntimeNatSqrt
            end
        in
        mk_imp_json_runtime_call op [ e ]
      | _ => mk_imp_json_expr_error "OpNatUnary: wrong number of arguments"
      end
    | OpNatSum => mk_imp_json_runtime_call JSONRuntimeNatSum el
    | OpNatMin => mk_imp_json_runtime_call JSONRuntimeNatMin el
    | OpNatMax => mk_imp_json_runtime_call JSONRuntimeNatMax el
    | OpNatMean => mk_imp_json_runtime_call JSONRuntimeNatArithMean el
    | OpFloatOfNat => mk_imp_json_runtime_call JSONRuntimeFloatOfNat el
    | OpFloatUnary u =>
      match el with
      | [e] =>
        match u with
        | FloatNeg => mk_imp_json_op JSONOpNeg [ e ]
        | _ =>
          mk_imp_json_expr_error "XXX TODO: OpFloatUnary: math operators XXX"
        (* | FloatSqrt => math_sqrt e' *)
        (* | FloatExp => math_exp e' *)
        (* | FloatLog => math_log e' *)
        (* | FloatLog10 => math_log10 e' *)
        (* | FloatCeil => math_ceil e' *)
        (* | FloatFloor => math_floor e' *)
        (* | FloatAbs => math_abs e' *)
        end
      | _ => mk_imp_json_expr_error "OpFloatUnary: wrong number of arguments"
      end
    | OpFloatTruncate =>
      mk_imp_json_expr_error "XXX TODO: OpFloatTruncate: math operators XXX"
    | OpFloatSum => mk_imp_json_runtime_call JSONRuntimeSum el
    | OpFloatMean => mk_imp_json_runtime_call JSONRuntimeArithMean el
    | _ => mk_imp_json_expr_error "XXX TODO: ImpQcerttoImpJson.imp_qcert_unary_op_to_imp_json: not yet implemented XXX" (* XXX TODO XXX *)
    end.

  Definition imp_qcert_binary_op_to_imp_json (op:binary_op) el : imp_json_expr :=
    match op with
    | OpEqual => mk_imp_json_runtime_call JSONRuntimeEqual el
    | OpRecConcat => mk_imp_json_runtime_call JSONRuntimeRecConcat el
    | OpRecMerge => mk_imp_json_runtime_call JSONRuntimeRecMerge el
    | OpAnd => mk_imp_json_op JSONOpAnd el
    | OpOr => mk_imp_json_op JSONOpOr el
    | _ => mk_imp_json_expr_error "XXX TODO: ImpQcerttoImpJson.imp_qcert_binary_op_to_imp_json: not yet implemented XXX" (* XXX TODO  *)
    end.

  Definition imp_qcert_op_to_imp_json (op:imp_qcert_op) el : imp_json_expr :=
    match op with
    | QcertOpUnary op => imp_qcert_unary_op_to_imp_json op el
    | QcertOpBinary op => imp_qcert_binary_op_to_imp_json op el
    end.

  Definition mk_either_expr (el:list imp_json_expr) : imp_json_expr :=
    mk_imp_json_runtime_call JSONRuntimeEither el.

  Definition mk_to_left_expr (el:list imp_json_expr) : imp_json_expr :=
    mk_imp_json_runtime_call JSONRuntimeToLeft el.

  Definition mk_to_right_expr (el:list imp_json_expr) : imp_json_expr :=
    mk_imp_json_runtime_call JSONRuntimeToRight el.

  Definition imp_qcert_runtime_call_to_imp_json
             (op:imp_qcert_runtime_op)
             (el:list imp_json_expr) : imp_json_expr :=
    match op with
    | QcertRuntimeGroupby s ls =>
      mk_imp_json_runtime_call
        JSONRuntimeGroupBy
        ((ImpExprConst (jstring s))
           :: (ImpExprConst (jarray (map jstring ls)))
           :: el)
    | QcertRuntimeEither => mk_either_expr el
    | QcertRuntimeToLeft => mk_to_left_expr el
    | QcertRuntimeToRight => mk_to_right_expr el
    | QcertRuntimeDeref =>
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

  Fixpoint imp_qcert_stmt_to_imp_json (avoid: list string) (stmt: imp_qcert_stmt): imp_json_stmt :=
    match stmt with
    | ImpStmtBlock lv ls =>
      ImpStmtBlock
        (map (fun xy => (fst xy,
                         lift imp_qcert_expr_to_imp_json (snd xy))) lv)
        (map (imp_qcert_stmt_to_imp_json ((List.map fst lv) ++ avoid)) ls)
    | ImpStmtAssign v e =>
      ImpStmtAssign v (imp_qcert_expr_to_imp_json e)
    | ImpStmtFor v e s =>
      let avoid := v :: avoid in
      let e := imp_qcert_expr_to_imp_json e in
      let src_id := fresh_var "src" avoid in
      let avoid := src_id :: avoid in
      let i_id := fresh_var "i" avoid in
      let avoid := i_id :: avoid in
      let src := ImpExprVar src_id in
      let i := ImpExprVar i_id in
      ImpStmtBlock
        [ (src_id, Some e) ]
        [ ImpStmtForRange
            i_id (ImpExprConst (jnumber zero)) (ImpExprOp JSONOpArrayLength [ src ])
            (ImpStmtBlock
               [ (v, Some (ImpExprOp JSONOpArrayAccess [ src; i ])) ]
               [ imp_qcert_stmt_to_imp_json avoid s ]) ]
    | ImpStmtForRange v e1 e2 s =>
      ImpStmtForRange v
                      (imp_qcert_expr_to_imp_json e1)
                      (imp_qcert_expr_to_imp_json e2)
                      (imp_qcert_stmt_to_imp_json (v :: avoid) s)
    | ImpStmtIf e s1 s2 =>
      ImpStmtIf (imp_qcert_expr_to_imp_json e)
                (imp_qcert_stmt_to_imp_json avoid s1)
                (imp_qcert_stmt_to_imp_json avoid s2)
    | ImpStmtReturn e =>
      ImpStmtReturn (lift imp_qcert_expr_to_imp_json e)
    end.

  Definition imp_qcert_function_to_imp_json (f:imp_qcert_function) : imp_json_function :=
    match f with
    | ImpFun lv s => ImpFun lv (imp_qcert_stmt_to_imp_json lv s)
    end.

  Fixpoint imp_qcert_to_imp_json (i:imp_qcert) : imp_json :=
    match i with
    | ImpLib l =>
      ImpLib
        (List.map
           (fun (decl: string * imp_qcert_function) =>
              let (name, def) := decl in (name, imp_qcert_function_to_imp_json def))
           l)
    end.

End ImpJsontoJavaScriptAst.
