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
    mk_imp_json_op (JSONOpObject ["$left"%string]) [ e ].
  Definition mk_right e : imp_json_expr :=
    mk_imp_json_op (JSONOpObject ["$right"%string]) [ e ].

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
      | OpNeg => mk_imp_json_op JSONOpNot [e]
      | OpRec s => mk_imp_json_op (JSONOpObject [json_key_encode s]) [e]
      | OpDot s => mk_imp_json_runtime_call JSONRuntimeDeref [e; ImpExprConst (jstring (json_key_encode s))]
      | OpRecRemove s => mk_imp_json_runtime_call JSONRuntimeRemove [e; mk_string (json_key_encode s)]
      | OpRecProject fl =>
        mk_imp_json_runtime_call
          JSONRuntimeProject ((List.map mk_string fl) ++ [e])
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
    | _ => mk_imp_json_expr_error "wrong number of arguments"
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
    | ImpExprVar v => ImpExprVar v
    | ImpExprConst d => ImpExprConst (@data_to_json _ _ d)
    | ImpExprOp op el => imp_qcert_op_to_imp_json op (map imp_qcert_expr_to_imp_json el)
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
    end.


  Definition imp_qcert_function_to_imp_json (f:imp_qcert_function) : imp_json_function :=
    match f with
    | ImpFun v s ret => ImpFun v (imp_qcert_stmt_to_imp_json [v] s) ret
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


  Section Correctness.
    Context (h:list(string*string)).

    Definition lift_bindings (env:bindings) : jbindings :=
      List.map (fun xy => (fst xy, data_to_json (snd xy))) env.
    Definition lift_pd_bindings (env:pd_bindings) : pd_jbindings :=
      List.map (fun xy => (fst xy, lift data_to_json (snd xy))) env.
    Definition lift_result (res:option json) : option data :=
      lift (json_to_data h) res.
    Definition lift_result_env (res:option pd_jbindings) : option pd_bindings :=
      lift (fun env => List.map (fun xy => (fst xy, lift (json_to_data h) (snd xy))) env) res.


    Lemma map_qcert_json_eval 
          (σ:pd_bindings) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_json_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json exp))) el -> 
      map (fun x : imp_qcert_expr => imp_qcert_expr_eval h σ x) el =
      map (fun x : imp_qcert_expr => lift_result
             (imp_json_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json x))) el.
    Proof.
      intros.
      apply map_eq.
      assumption.
    Qed.

    Lemma json_to_data_to_json_id d:
      json_to_data h (data_to_json d) = normalize_data h d.
    Proof.
      apply json_to_data_to_json_idempotent.
    Qed.

    Lemma normalize_data_dbool d b : normalize_data h d = dbool b <-> d = dbool b.
    Proof.
      destruct d; simpl; intuition discriminate.
    Qed.

    Lemma json_to_data_pre_jobj_nbool l b : (json_to_data_pre (jobject l)) <> dbool b.
    Proof.
      destruct l; simpl; try congruence.
      destruct p.
      repeat match_destr.
    Qed.

    Lemma normalize_data_forall_ndbool d :  (forall b, d <> dbool b) -> (forall b, normalize_data h d <> dbool b).
    Proof.
      destruct d; simpl; intuition discriminate.
    Qed.
    
    Lemma data_to_bool_json_to_bool_correct j:
      imp_qcert_data_to_bool (json_to_data h j) = imp_json_data_to_bool j.
    Proof.
      unfold json_to_data.
      unfold imp_qcert_data_to_bool.
      unfold imp_json_data_to_bool.
      destruct j; trivial.
      generalize (json_to_data_pre_jobj_nbool l); intros HH1.
      generalize (normalize_data_forall_ndbool _ HH1); intros HH2.
      match_destr.
      specialize (HH2 b); congruence.
    Qed.

    Lemma normalize_data_forall_ndnat d :  (forall n, d <> dnat n) -> (forall n, normalize_data h d <> dnat n).
    Proof.
      destruct d; simpl; intuition discriminate.
    Qed.

    Lemma data_to_bool_json_to_nat_correct j:
      imp_qcert_data_to_Z (json_to_data h j) = imp_json_data_to_Z j.
    Proof.
      unfold json_to_data.
      unfold imp_qcert_data_to_Z.
      unfold imp_json_data_to_Z.
      destruct j; trivial.
      assert (simpl_eq1:
                match normalize_data h (json_to_data_pre (jobject l)) with
                | dnat n => Some n
                | _ => None
                end =
                match json_to_data_pre (jobject l) with
                | dnat n => Some n
                | _ => None
                end)
             
        by now destruct (json_to_data_pre (jobject l)).
      rewrite simpl_eq1; clear simpl_eq1.

      destruct l; trivial.
      destruct p.
      assert (simpl_eq: match s with
  | "$nat"%string =>
      match j with
      | jnumber n => match l with
                     | [] => Some (float_truncate n)
                     | _ :: _ => None
                     end
      | _ => None
      end
  | _ => None
                end =
                      (match l with
                      | [] => if string_dec s  ("$nat"%string)
                                  then match j with
                                  | jnumber n => Some (float_truncate n)
                                  | _ => None
                                       end
                              else None
                      | _ :: _ => None
                       end))
        by (repeat match_destr).
      rewrite simpl_eq; clear simpl_eq.      
      destruct l.
      - simpl.
        string_dec_to_equiv.
        destruct j; simpl
        ; repeat dest_eqdec; trivial
        ; destruct (foreign_to_JSON_to_data _); trivial.
      - simpl.
        destruct p.
        string_dec_to_equiv.
        destruct j; simpl
        ; repeat dest_eqdec; trivial
        ; destruct j0; simpl; trivial
        ; destruct l; simpl; trivial
        ; try destruct (json_brands l0); trivial.
        
        now destruct (json_brands l1).
    Qed.

    Lemma Forall_singleton σ i:
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result (imp_json_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json exp))) [i]
      -> imp_qcert_expr_eval h σ i
         = lift_result (imp_json_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i)).
    Proof.
      intros.
      rewrite Forall_forall in H.
      specialize (H i).
      apply H.
      left; reflexivity.
    Qed.

    Lemma imp_qcert_unary_op_to_imp_json_expr_correct
           (σ:pd_bindings) (u:unary_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_json_expr_eval
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json exp))) el -> 
      imp_qcert_expr_eval h σ (ImpExprOp (QcertOpUnary u) el) =
      lift_result
        (imp_json_expr_eval (lift_pd_bindings σ)
                            (imp_qcert_unary_op_to_imp_json u (map imp_qcert_expr_to_imp_json el))).
    Proof.
      intros.
      (* elim no params *)
      destruct el; simpl; [reflexivity|].
      (* elim two or more params *)
      destruct el; simpl;
        [|destruct (imp_qcert_expr_eval h σ i); [|reflexivity]; simpl;
          destruct (imp_qcert_expr_eval h σ i0); [|reflexivity]; simpl;
          unfold lift, olift;
          case_eq
            (lift_map (fun x : option imp_qcert_data => x)
                      (map (fun x : imp_qcert_expr => imp_qcert_expr_eval h σ x) el)); intros;
          unfold imp_qcert_data, ImpEval.imp_expr, imp_qcert_expr, imp_qcert_data, foreign_runtime_data in *;
          rewrite H0; reflexivity].
      (* just one param *)
      apply Forall_singleton in H.
      rewrite H; clear H.
      unfold imp_qcert_op_eval, imp_json_op_eval.
      unary_op_cases (destruct u) Case; unfold lift_result, lift, olift; simpl.
      - Case "OpIdentity"%string.
        destruct (imp_json_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i));
          try reflexivity; simpl.
      - Case "OpNeg"%string.
        destruct (imp_json_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        unfold unudbool.
        case_eq (json_to_data h (jobject l)); intros; try reflexivity.
        generalize (json_to_data_object_not_boolean h l b); intros.
        congruence.
      - Case "OpRec"%string.
        destruct (imp_json_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i));
          try reflexivity; simpl.
        f_equal.
        apply rec_json_key_encode_roundtrip.
      - Case "OpDot"%string.
        destruct (imp_json_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        unfold edot.
        apply assoc_lookupr_json_key_encode_roundtrip.
      - Case "OpRecRemove"%string.
        destruct (imp_json_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        apply rremove_json_key_encode_roundtrip.
      - Case "OpRecProject"%string.
        simpl.
        admit. (** XXX This one looks more complicated *)
      - Case "OpBag"%string.
        destruct (imp_json_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i));
          try reflexivity; simpl.
      - Case "OpSingleton"%string.
        destruct (imp_json_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        destruct l; try reflexivity; simpl.
        destruct l; try reflexivity; simpl.
        + f_equal.
          unfold json_to_data; simpl.
          admit.
        + case_eq (json_to_data h (jobject l)); intros; try reflexivity.
          generalize (json_to_data_object_not_coll h l l0); intros.
          congruence.
    Admitted.

    Lemma imp_qcert_binary_op_to_imp_json_expr_correct
           (σ:pd_bindings) (b:binary_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_json_expr_eval
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json exp))) el -> 
      imp_qcert_expr_eval h σ (ImpExprOp (QcertOpBinary b) el) =
      lift_result
        (imp_json_expr_eval (lift_pd_bindings σ)
                            (imp_qcert_binary_op_to_imp_json b (map imp_qcert_expr_to_imp_json el))).
    Proof.
    Admitted.

    Lemma imp_qcert_runtime_call_to_imp_json_expr_correct
            (σ:pd_bindings) (rt:imp_qcert_runtime_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_json_expr_eval
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json exp))) el -> 
      imp_qcert_expr_eval h σ (ImpExprRuntimeCall rt el) =
      lift_result
        (imp_json_expr_eval (lift_pd_bindings σ)
                            (imp_qcert_runtime_call_to_imp_json rt (map imp_qcert_expr_to_imp_json el))).
    Proof.
    Admitted.

    Lemma imp_qcert_op_to_imp_json_correct
          (σ:pd_bindings) (op:imp_qcert_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_json_expr_eval
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json exp))) el -> 
      imp_qcert_expr_eval h σ (ImpExprOp op el) =
      lift_result
        (imp_json_expr_eval (lift_pd_bindings σ)
                            (imp_qcert_op_to_imp_json op (map imp_qcert_expr_to_imp_json el))).
    Proof.
      intros.
      destruct op.
      + apply imp_qcert_unary_op_to_imp_json_expr_correct; assumption.
      + apply imp_qcert_binary_op_to_imp_json_expr_correct; assumption.
    Qed.

    Lemma imp_qcert_expr_to_imp_json_expr_correct (σ:pd_bindings) (exp:imp_qcert_expr) :
      imp_qcert_expr_eval h σ exp =
      lift_result
        (imp_json_expr_eval (lift_pd_bindings σ)
                            (imp_qcert_expr_to_imp_json exp)).
    Proof.
      imp_expr_cases (induction exp) Case.
      - Case "ImpExprError"%string.
        reflexivity.
      - Case "ImpExprVar"%string.
        simpl.
        unfold lift_result, olift.
        unfold lift_pd_bindings.
        rewrite lookup_map_codomain_unfolded; simpl.
        unfold lift.
        unfold imp_qcert_data.
        match_destr.
        destruct o; try reflexivity.
        rewrite json_to_data_to_json_id.
        admit.
      - Case "ImpExprConst"%string.
        simpl.
        f_equal.
        admit. (* XXX Needs json_normalize with lift/unlift roundtrip property *)
      - Case "ImpExprOp"%string.
        apply imp_qcert_op_to_imp_json_correct; assumption.
      - Case "ImpExprRuntimeCall"%string.
        apply imp_qcert_runtime_call_to_imp_json_expr_correct; assumption.
    Admitted.

    Lemma imp_qcert_stmt_to_imp_json_stmt_correct (σ:pd_bindings) (stmt:imp_qcert_stmt) :
      forall avoid: list string,
         (* (fres_var stmt) avoid -> *)
        imp_qcert_stmt_eval h stmt σ =
        lift_result_env (imp_json_stmt_eval (imp_qcert_stmt_to_imp_json avoid stmt) (lift_pd_bindings σ)).
    Proof.
      imp_stmt_cases (induction stmt) Case.
      - Case "ImpStmtBlock"%string.
        admit.
      - Case "ImpStmtAssign"%string.
        intros avoid.
        simpl.
        specialize (imp_qcert_expr_to_imp_json_expr_correct σ i).
        unfold imp_qcert_expr_eval in *.
        intros Hi.
        rewrite Hi.
        unfold lift_result.
        unfold lift.
        unfold imp_json_expr_eval.
        destruct (ImpEval.imp_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i));
          try reflexivity.
        unfold lift_pd_bindings.
        rewrite lookup_map_codomain_unfolded.
        unfold lift.
        unfold imp_qcert_data, foreign_runtime_data.
        match_destr.
        unfold lift_result_env, lift.
        assert (forall (x: pd_bindings) y,  x = y -> Some x = Some y) as Hsome; try congruence.
        apply Hsome.
        clear Hi.
        induction σ; try reflexivity.
        simpl.
        rewrite IHσ; clear IHσ.
        destruct a; simpl.
        assert (forall (x1 x2: string * option data) l1 l2,
                   x1 = x2 -> l1 = l2 -> x1 :: l1 = x2 :: l2) as Hl; try congruence.
        match_destr; simpl.
        + apply Hl; try reflexivity.
          induction σ; try reflexivity.
          destruct a; simpl.
          rewrite <- IHσ.
          apply Hl; try reflexivity.
          destruct o1; try reflexivity.
          rewrite json_to_data_to_json_id.
          admit. (** XX Needs a proof of normalization *)
        + apply Hl; try reflexivity.
          destruct o0; try reflexivity.
          rewrite json_to_data_to_json_id.
          admit. (** XX Needs a proof of normalization *)
      - Case "ImpStmtFor"%string.
        admit.
      - Case "ImpStmtForRange"%string.
        intros avoid.
        admit. (* XXX TODO: eval XXX *)
      - Case "ImpStmtIf"%string.
        intros avoid.
        simpl.
        specialize (imp_qcert_expr_to_imp_json_expr_correct σ i).
        unfold imp_qcert_expr_eval in *.
        intros Hi.
        rewrite Hi.
        unfold lift_result.
        unfold lift.
        unfold imp_json_expr_eval.
        destruct (ImpEval.imp_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_json i));
          try reflexivity.
        rewrite data_to_bool_json_to_bool_correct.
        match_destr.
        match_destr.
    (* Qed. *)
    Admitted.

    Lemma imp_qcert_function_to_imp_json_function_correct (d:data) (f:imp_qcert_function) :
      imp_qcert_function_eval h f d =
      lift (json_to_data h) (imp_json_function_eval (imp_qcert_function_to_imp_json f) (data_to_json d)).
    Proof.
      destruct f; simpl.
      generalize (imp_qcert_stmt_to_imp_json_stmt_correct [(v0, None); (v, Some d)] i (v::nil)); intros.
      unfold imp_qcert_stmt_eval in H.
      unfold imp_json_stmt_eval in H.
      unfold imp_qcert_data in *.
      rewrite H; clear H.
      unfold lift_result_env.
      unfold lift.
      case_eq (@ImpEval.imp_stmt_eval _ _ _ imp_json_data_normalize imp_json_data_to_bool imp_json_data_to_Z imp_json_data_to_list imp_json_Z_to_data imp_json_runtime_eval imp_json_op_eval (imp_qcert_stmt_to_imp_json [v] i) (lift_pd_bindings [(v0, None); (v, Some d)])); intros.
      - unfold olift.
        unfold imp_json_data in *.
        unfold imp_qcert_data in *.
        unfold imp_json_op in *.
        assert ((@ImpEval.imp_stmt_eval json json_op imp_json_runtime_op imp_json_data_normalize imp_json_data_to_bool
           imp_json_data_to_Z imp_json_data_to_list imp_json_Z_to_data imp_json_runtime_eval imp_json_op_eval
           (imp_qcert_stmt_to_imp_json (@cons var v (@nil var)) i)
           (lift_pd_bindings
              (@cons (prod var (option (@data (@foreign_runtime_data fruntime))))
                 (@pair var (option (@data (@foreign_runtime_data fruntime))) v0
                    (@None (@data (@foreign_runtime_data fruntime))))
                 (@cons (prod var (option (@data (@foreign_runtime_data fruntime))))
                    (@pair var (option (@data (@foreign_runtime_data fruntime))) v
                       (@Some (@data (@foreign_runtime_data fruntime)) d))
                    (@nil (prod var (option (@data (@foreign_runtime_data fruntime)))))))))
                = (@ImpEval.imp_stmt_eval json json_op imp_json_runtime_op imp_json_data_normalize imp_json_data_to_bool
          imp_json_data_to_Z imp_json_data_to_list imp_json_Z_to_data imp_json_runtime_eval imp_json_op_eval
          (imp_qcert_stmt_to_imp_json (@cons var v (@nil var)) i)
          (@cons (prod var (option json)) (@pair var (option json) v0 (@None json))
             (@cons (prod var (option json))
                (@pair var (option json) v (@Some json (@data_to_json (@foreign_runtime_data fruntime) ftjson d)))
                (@nil (prod var (option json))))))) by reflexivity.
        rewrite H0 in *; clear H0.
        rewrite H; clear H.
        generalize (@lookup_map_codomain_unfolded string (option json) (option data) string_dec (fun x => match x with
                   | Some a' => Some (json_to_data h a')
                   | None => None
                   end)); intros.
        rewrite H; clear H.
        unfold lift.
        assert (@lookup string (option json) string_dec p v0 = lookup EquivDec.equiv_dec p v0) by reflexivity.
        rewrite H; clear H.
        case_eq (lookup EquivDec.equiv_dec p v0); intros; try reflexivity.
      - unfold olift.
        unfold imp_json_data in *.
        unfold imp_qcert_data in *.
        unfold imp_json_op in *.
        assert ((@ImpEval.imp_stmt_eval json json_op imp_json_runtime_op imp_json_data_normalize imp_json_data_to_bool
           imp_json_data_to_Z imp_json_data_to_list imp_json_Z_to_data imp_json_runtime_eval imp_json_op_eval
           (imp_qcert_stmt_to_imp_json (@cons var v (@nil var)) i)
           (lift_pd_bindings
              (@cons (prod var (option (@data (@foreign_runtime_data fruntime))))
                 (@pair var (option (@data (@foreign_runtime_data fruntime))) v0
                    (@None (@data (@foreign_runtime_data fruntime))))
                 (@cons (prod var (option (@data (@foreign_runtime_data fruntime))))
                    (@pair var (option (@data (@foreign_runtime_data fruntime))) v
                       (@Some (@data (@foreign_runtime_data fruntime)) d))
                    (@nil (prod var (option (@data (@foreign_runtime_data fruntime)))))))))
                = (@ImpEval.imp_stmt_eval json json_op imp_json_runtime_op imp_json_data_normalize imp_json_data_to_bool
          imp_json_data_to_Z imp_json_data_to_list imp_json_Z_to_data imp_json_runtime_eval imp_json_op_eval
          (imp_qcert_stmt_to_imp_json (@cons var v (@nil var)) i)
          (@cons (prod var (option json)) (@pair var (option json) v0 (@None json))
             (@cons (prod var (option json))
                (@pair var (option json) v (@Some json (@data_to_json (@foreign_runtime_data fruntime) ftjson d)))
                (@nil (prod var (option json))))))) by reflexivity.
        rewrite H0 in *; clear H0.
        rewrite H.
        reflexivity.
    Qed.

    Lemma push_rec_sort_in_map env :
      (rec_sort (map (fun xy : string * data => (fst xy, data_to_json (snd xy))) env))
      = (map (fun xy : string * data => (fst xy, data_to_json (snd xy))) (rec_sort env)).
    Proof.
      rewrite map_rec_sort.
      - reflexivity.
      - intros; split; intros; auto.
    Qed.

    Theorem imp_qcert_to_imp_json_correct (σc:bindings) (q:imp_qcert) :
      imp_qcert_eval_top h σc q =
      imp_json_eval_top_alt h σc (imp_qcert_to_imp_json q).
    Proof.
      unfold imp_qcert_eval_top.
      unfold imp_json_eval_top_alt.
      unfold imp_json_eval_top.
      unfold imp_json_eval.
      destruct q; simpl.
      destruct l; try reflexivity; simpl.
      destruct p; simpl.
      destruct l; try reflexivity; simpl.
      generalize (imp_qcert_function_to_imp_json_function_correct (drec (rec_sort σc)) i); intros.
      unfold imp_qcert_eval_top.
      unfold imp_json_eval_top_alt.
      unfold imp_json_eval_top.
      unfold imp_json_eval.
      unfold id; simpl.
      simpl in H.
      unfold imp_qcert_function_eval in H.
      unfold imp_json_function_eval in H.
      rewrite H; clear H.
      f_equal.
      f_equal.
      f_equal.
      rewrite push_rec_sort_in_map.
      rewrite map_map.
      reflexivity.
    Qed.

  End Correctness.

End ImpJsontoJavaScriptAst.
