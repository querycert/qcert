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
Require Import ImpQcertEval.
Require Import ImpJson.
Require Import ImpJsonEval.
Require Import JsAst.JsNumber.
Require Import Fresh.

Section ImpJsontoJavaScriptAst.
  Import ListNotations.

  (** Translation *)

  Context {fruntime:foreign_runtime}.
  Context {ftjson:foreign_to_JSON}.

(*Definition mk_imp_json_expr_error msg : imp_json_expr :=
    ImpExprConst (jstring msg). *)
  Definition mk_imp_json_expr_error msg : imp_json_expr :=
    ImpExprError msg. (* XXX Error should eval to None if we want to prove stuffs! *)
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
    match el with
    | [e] =>
      match op with
      | OpIdentity => e
      | OpNeg => mk_imp_json_op JSONOpNot el
      | OpRec s => mk_imp_json_op (JSONOpObject [s]) el
      | OpDot s => mk_imp_json_runtime_call JSONRuntimeDeref [e; ImpExprConst (jstring s)]
      | OpRecRemove f => mk_imp_json_runtime_call JSONRuntimeRemove [e; mk_string f ]
      | OpRecProject fl =>
        mk_imp_json_runtime_call
          JSONRuntimeProject ((List.map mk_string fl) ++ [ e ])
      | OpBag => mk_bag el
      | OpSingleton => mk_imp_json_runtime_call JSONRuntimeSingleton el
      | OpFlatten => mk_imp_json_runtime_call JSONRuntimeFlatten el
      | OpDistinct => mk_imp_json_runtime_call JSONRuntimeDistinct el
      | OpOrderBy scl =>
        mk_imp_json_runtime_call
          JSONRuntimeSort (e :: (List.map sortCriteria_to_json_expr scl))
      | OpCount => mk_imp_json_runtime_call JSONRuntimeCount el
      | OpToString => mk_imp_json_op JSONOpToString el
      | OpToText => mk_imp_json_runtime_call JSONRuntimeToText el
      | OpLength => mk_imp_json_runtime_call JSONRuntimeLength el
      | OpSubstring start len =>
        let start := ImpExprConst (jnumber (float_of_int start)) in
        let args :=
            match len with
            | None => [ e; start ]
            | Some len =>
              let len := ImpExprConst (jnumber (float_of_int len)) in
              [ e; start; len ]
            end
        in
        mk_imp_json_runtime_call JSONRuntimeSubstring args
      | OpLike pat oescape =>
        mk_imp_json_expr_error "XXX TODO: ImpQcerttoImpJson: OpLike XXX"
      | OpLeft => mk_left e
      | OpRight => mk_right e
      | OpBrand b =>
        mk_imp_json_runtime_call JSONRuntimeBrand [ brands_to_json_expr b; e ]
      | OpUnbrand => mk_imp_json_runtime_call JSONRuntimeUnbrand el
      | OpCast b =>
        mk_imp_json_runtime_call JSONRuntimeCast [ brands_to_json_expr b; e ]
      | OpNatUnary u =>
        let op :=
            match u with
            | NatAbs => JSONRuntimeNatAbs
            | NatLog2 => JSONRuntimeNatLog2
            | NatSqrt => JSONRuntimeNatSqrt
            end
        in
        mk_imp_json_runtime_call op [ e ]
      | OpNatSum => mk_imp_json_runtime_call JSONRuntimeNatSum el
      | OpNatMin => mk_imp_json_runtime_call JSONRuntimeNatMin el
      | OpNatMax => mk_imp_json_runtime_call JSONRuntimeNatMax el
      | OpNatMean => mk_imp_json_runtime_call JSONRuntimeNatArithMean el
      | OpFloatOfNat => mk_imp_json_runtime_call JSONRuntimeFloatOfNat el
      | OpFloatUnary u =>
        match u with
        | FloatNeg => mk_imp_json_op JSONOpNeg [ e ]
        | FloatSqrt => mk_imp_json_op JSONOpMathSqrt [ e ]
        | FloatExp => mk_imp_json_op JSONOpMathExp [ e ]
        | FloatLog => mk_imp_json_op JSONOpMathLog [ e ]
        | FloatLog10 => mk_imp_json_op JSONOpMathLog10 [ e ]
        | FloatCeil => mk_imp_json_op JSONOpMathCeil [ e ]
        | FloatFloor => mk_imp_json_op JSONOpMathFloor [ e ]
        | FloatAbs => mk_imp_json_op JSONOpMathAbs [ e ]
        end
      | OpFloatTruncate => mk_imp_json_op JSONOpMathTrunc [e]
      | OpFloatSum => mk_imp_json_runtime_call JSONRuntimeSum el
      | OpFloatMean => mk_imp_json_runtime_call JSONRuntimeArithMean el
      | OpFloatBagMin => mk_imp_json_op JSONOpMathMinApply [e]
      | OpFloatBagMax => mk_imp_json_op JSONOpMathMaxApply [e]
      | OpForeignUnary fu =>
        mk_imp_json_expr_error "XXX TODO: ImpQcerttoImpJson.imp_qcert_unary_op_to_imp_json OpForeignUnary"
      end
    | _ => mk_imp_json_expr_error "OpIdentity: wrong number of arguments"
    end.

  Definition imp_qcert_binary_op_to_imp_json (op:binary_op) el : imp_json_expr :=
    match el with
    | [e1; e2] =>
      match op with
      | OpEqual => mk_imp_json_runtime_call JSONRuntimeEqual el
      | OpRecConcat => mk_imp_json_runtime_call JSONRuntimeRecConcat el
      | OpRecMerge => mk_imp_json_runtime_call JSONRuntimeRecMerge el
      | OpAnd => mk_imp_json_op JSONOpAnd el
      | OpOr => mk_imp_json_op JSONOpOr el
      | OpLt =>
        mk_imp_json_op JSONOpLt
                       [ mk_imp_json_runtime_call JSONRuntimeCompare [e1; e2];
                         ImpExprConst (jnumber zero) ]
      | OpLe =>
        mk_imp_json_op JSONOpLe
                       [ mk_imp_json_runtime_call JSONRuntimeCompare [e1; e2];
                         ImpExprConst (jnumber zero) ]
      | OpBagUnion => mk_imp_json_runtime_call JSONRuntimeBunion [e1; e2]
      | OpBagDiff => mk_imp_json_runtime_call JSONRuntimeBminus [e1; e2]
      | OpBagMin => mk_imp_json_runtime_call JSONRuntimeBmin [e1; e2]
      | OpBagMax => mk_imp_json_runtime_call JSONRuntimeBmax [e1; e2]
      | OpBagNth => mk_imp_json_runtime_call JSONRuntimeBnth [e1; e2]
      | OpContains => mk_imp_json_runtime_call JSONRuntimeContains [e1; e2]
      | OpStringConcat => mk_imp_json_op JSONOpAddString el
      | OpStringJoin => mk_imp_json_runtime_call JSONRuntimeStringJoin [e1; e2]
      | OpNatBinary opa =>
        match opa with
        | NatPlus => mk_imp_json_runtime_call JSONRuntimeNatPlus [e1; e2]
        | NatMinus => mk_imp_json_runtime_call JSONRuntimeNatMinus [e1; e2]
        | NatMult => mk_imp_json_runtime_call JSONRuntimeNatMult [e1; e2]
        | NatDiv => mk_imp_json_runtime_call JSONRuntimeNatDiv [e1; e2]
        | NatRem => mk_imp_json_runtime_call JSONRuntimeNatRem [e1; e2]
        | NatMin => mk_imp_json_runtime_call JSONRuntimeNatMin [e1; e2]
        | NatMax => mk_imp_json_runtime_call JSONRuntimeNatMax [e1; e2]
        end
      | OpFloatBinary opa =>
        match opa with
        | FloatPlus => mk_imp_json_op JSONOpAddNumber [e1; e2]
        | FloatMinus => mk_imp_json_op JSONOpSub [e1; e2]
        | FloatMult => mk_imp_json_op JSONOpMult [e1; e2]
        | FloatDiv => mk_imp_json_op JSONOpDiv [e1; e2]
        | FloatPow => mk_imp_json_op JSONOpMathPow [e1; e2]
        | FloatMin => mk_imp_json_op JSONOpMathMin [e1; e2]
        | FloatMax => mk_imp_json_op JSONOpMathMax [e1; e2]
        end
      | OpFloatCompare opa =>
        match opa with
        | FloatLt => mk_imp_json_op JSONOpLt [e1; e2]
        | FloatLe => mk_imp_json_op JSONOpLe [e1; e2]
        | FloatGt => mk_imp_json_op JSONOpGt [e1; e2]
        | FloatGe => mk_imp_json_op JSONOpGe [e1; e2]
        end
      | OpForeignBinary fb =>
      (* foreign_to_ajavascript_binary_op fb [e1; e2] *)
        mk_imp_json_expr_error "XXX TODO: ImpQcerttoImpJson.imp_qcert_binary_op_to_imp_json(OpForeignBinary): not yet implemented XXX" (* XXX TODO  *)
      end
    | _ => mk_imp_json_expr_error "imp_qcert_binary_op_to_imp_json: wrong number of arguments"
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
    | ImpExprError msg => ImpExprError msg
    | ImpExprGetConstant v => ImpExprGetConstant v
    | ImpExprVar v => ImpExprVar v
    | ImpExprConst d => ImpExprConst (@data_to_json _ _ d)
    | ImpExprOp op el => imp_qcert_op_to_imp_json op (map imp_qcert_expr_to_imp_json el)
    | ImpExprRuntimeCall op el => imp_qcert_runtime_call_to_imp_json op (map imp_qcert_expr_to_imp_json el)
    end.

  Section Correctness.
    Context (h:list(string*string)).

    Definition lift_bindings (env:bindings) : jbindings :=
      List.map (fun xy => (fst xy, data_to_json (snd xy))) env.
    Definition lift_pd_bindings (env:pd_bindings) : pd_jbindings :=
      List.map (fun xy => (fst xy, lift data_to_json (snd xy))) env.
    Definition lift_result (res:option json) : option data :=
      lift (json_to_data h) res.

    Lemma lift_map_lift_result {A} (g:A -> option json) l :
      lift_map (fun x => lift_result (g x)) l = lift (map (json_to_data h)) (lift_map g l).
    Proof.
      unfold lift_result.
      apply lift_map_lift.
    Qed.

    Lemma test 
          (σc:bindings) (σ:pd_bindings) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σc σ exp =
           lift_result
             (imp_json_expr_eval (lift_bindings σc) (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json exp))) el -> 
      map (fun x : imp_qcert_expr => imp_qcert_expr_eval h σc σ x) el =
      map (fun x : imp_qcert_expr => lift_result
             (imp_json_expr_eval (lift_bindings σc) (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json x))) el.
    Proof.
      intros.
      apply map_eq.
      assumption.
    Qed.

    Lemma imp_qcert_unary_op_to_imp_json_expr_correct
           (σc:bindings) (σ:pd_bindings) (u:unary_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σc σ exp =
           lift_result
             (imp_json_expr_eval
                (lift_bindings σc)
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json exp))) el -> 
      imp_qcert_expr_eval h σc σ (ImpExprOp (QcertOpUnary u) el) =
      lift_result
        (imp_json_expr_eval (lift_bindings σc) (lift_pd_bindings σ)
                            (imp_qcert_unary_op_to_imp_json u (map imp_qcert_expr_to_imp_json el))).
    Proof.
      intros.
      unary_op_cases (destruct u) Case; simpl.
      - Case "OpIdentity"%string.
        simpl; unfold lift_result, lift, olift.
        rewrite test; [|assumption]; clear H.
        destruct el; simpl; [reflexivity|]; destruct el; simpl.
        + simpl; unfold lift_result, lift, olift.
          destruct (imp_json_expr_eval (lift_bindings σc) (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i));
            try reflexivity.
        + unfold olift, lift_result, lift; simpl.
          destruct (imp_json_expr_eval (lift_bindings σc) (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i)); try reflexivity.
          destruct (imp_json_expr_eval (lift_bindings σc) (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i0)); try reflexivity.
          rewrite lift_map_map_fusion.
          admit.
      - admit.
    Admitted.

    Lemma imp_qcert_binary_op_to_imp_json_expr_correct
           (σc:bindings) (σ:pd_bindings) (b:binary_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σc σ exp =
           lift_result
             (imp_json_expr_eval
                (lift_bindings σc)
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json exp))) el -> 
      imp_qcert_expr_eval h σc σ (ImpExprOp (QcertOpBinary b) el) =
      lift_result
        (imp_json_expr_eval (lift_bindings σc) (lift_pd_bindings σ)
                            (imp_qcert_binary_op_to_imp_json b (map imp_qcert_expr_to_imp_json el))).
    Proof.
    Admitted.

    Lemma imp_qcert_runtime_call_to_imp_json_expr_correct
           (σc:bindings) (σ:pd_bindings) (rt:imp_qcert_runtime_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σc σ exp =
           lift_result
             (imp_json_expr_eval
                (lift_bindings σc)
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json exp))) el -> 
      imp_qcert_expr_eval h σc σ (ImpExprRuntimeCall rt el) =
      lift_result
        (imp_json_expr_eval (lift_bindings σc) (lift_pd_bindings σ)
                            (imp_qcert_runtime_call_to_imp_json rt (map imp_qcert_expr_to_imp_json el))).
    Proof.
    Admitted.

    Lemma imp_qcert_op_to_imp_json_correct
          (σc:bindings) (σ:pd_bindings) (op:imp_qcert_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σc σ exp =
           lift_result
             (imp_json_expr_eval
                (lift_bindings σc)
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json exp))) el -> 
      imp_qcert_expr_eval h σc σ (ImpExprOp op el) =
      lift_result
        (imp_json_expr_eval (lift_bindings σc) (lift_pd_bindings σ)
                            (imp_qcert_op_to_imp_json op (map imp_qcert_expr_to_imp_json el))).
    Proof.
      intros.
      destruct op.
      + apply imp_qcert_unary_op_to_imp_json_expr_correct; assumption.
      + apply imp_qcert_binary_op_to_imp_json_expr_correct; assumption.
    Qed.
     
    Lemma imp_qcert_expr_to_imp_json_expr_correct (σc:bindings) (σ:pd_bindings) (exp:imp_qcert_expr) :
      imp_qcert_expr_eval h σc σ exp =
      lift_result
        (imp_json_expr_eval (lift_bindings σc) (lift_pd_bindings σ)
                            (imp_qcert_expr_to_imp_json exp)).
    Proof.
      imp_expr_cases (induction exp) Case.
      - Case "ImpExprError"%string.
        reflexivity.
      - Case "ImpExprGetConstant"%string.
        admit. (* XXX Needs lift/unlift roundtrip property over edot *)
      - Case "ImpExprVar"%string.
        admit. (* XXX Needs lift/unlift roundtrip property over lookup *)
      - Case "ImpExprConst"%string.
        admit. (* XXX Needs json_normalize with lift/unlift roundtrip property *)
      - Case "ImpExprOp"%string.
        apply imp_qcert_op_to_imp_json_correct; assumption.
      - Case "ImpExprRuntimeCall"%string.
        apply imp_qcert_runtime_call_to_imp_json_expr_correct; assumption.
    Admitted.

  End Correctness.

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
    end.

  Definition imp_qcert_function_to_imp_json (f:imp_qcert_function) : imp_json_function :=
    match f with
    | ImpFun lv s ret => ImpFun lv (imp_qcert_stmt_to_imp_json lv s) ret
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

