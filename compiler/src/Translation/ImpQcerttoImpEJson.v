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
Require Import ImpEJson.
Require Import ImpEJsonEval.
Require Import JsAst.JsNumber.
Require Import Fresh.

Section ImpQcerttoImpEJson.
  Import ListNotations.

  (** Translation *)

  Context {fruntime:foreign_runtime}.
  Context {ftejson:foreign_to_ejson}.

  Context (h:brand_relation_t). (* We need a brand relation for the Q*cert side *)

(*Definition mk_imp_ejson_expr_error msg : imp_ejson_expr :=
    ImpExprConst (jstring msg). *)
  Definition mk_imp_ejson_expr_error msg : imp_ejson_expr :=
    ImpExprError msg. (* XXX Error should eval to None if we want to prove stuffs! *)
  Definition mk_imp_ejson_op op el : imp_ejson_expr := ImpExprOp op el.
  Definition mk_imp_ejson_runtime_call op el : imp_ejson_expr := ImpExprRuntimeCall op el.

  Definition mk_string s : imp_ejson_expr := ImpExprConst (ejstring s).
  Definition mk_string_array sl : imp_ejson_expr := ImpExprConst (ejarray (map ejstring sl)).
  Definition mk_bag el : imp_ejson_expr := mk_imp_ejson_op EJsonOpArray el.
  Definition mk_left e : imp_ejson_expr :=
    mk_imp_ejson_op (EJsonOpObject ["$left"%string]) [ e ].
  Definition mk_right e : imp_ejson_expr :=
    mk_imp_ejson_op (EJsonOpObject ["$right"%string]) [ e ].

  Definition sortCriteria_to_ejson_expr (sc: string * SortDesc) : imp_ejson_expr :=
    let (lbl, c) := sc in
    let o :=
        match c with
        | Ascending => ejobject [ ("asc"%string, ejstring lbl) ]
        | Descending => ejobject [ ("desc"%string, ejstring lbl) ]
        end
    in
    ImpExprConst o.

  Definition brands_to_ejson_expr sl : imp_ejson_expr :=
    let j := ejarray ((List.map (fun s => ejstring s)) sl) in
    ImpExprConst j.

  Definition imp_qcert_unary_op_to_imp_ejson (op:unary_op) el : imp_ejson_expr :=
    match el with
    | [e] =>
      match op with
      | OpIdentity => e
      | OpNeg => mk_imp_ejson_op EJsonOpNot [e]
      | OpRec s => mk_imp_ejson_op (EJsonOpObject [json_key_encode s]) [e]
      | OpDot s => mk_imp_ejson_runtime_call EJsonRuntimeDeref [e; ImpExprConst (ejstring (json_key_encode s))]
      | OpRecRemove s => mk_imp_ejson_runtime_call EJsonRuntimeRemove [e; mk_string (json_key_encode s)]
      | OpRecProject fl =>
        mk_imp_ejson_runtime_call
          EJsonRuntimeProject ([e] ++ [mk_string_array fl])
      | OpBag => mk_bag el
      | OpSingleton => mk_imp_ejson_runtime_call EJsonRuntimeSingleton el
      | OpFlatten => mk_imp_ejson_runtime_call EJsonRuntimeFlatten el
      | OpDistinct => mk_imp_ejson_runtime_call EJsonRuntimeDistinct el
      | OpOrderBy scl =>
        mk_imp_ejson_runtime_call
          EJsonRuntimeSort (e :: (List.map sortCriteria_to_ejson_expr scl))
      | OpCount => mk_imp_ejson_runtime_call EJsonRuntimeCount el
      | OpToString => mk_imp_ejson_op EJsonOpToString el
      | OpToText => mk_imp_ejson_runtime_call EJsonRuntimeToText el
      | OpLength => mk_imp_ejson_runtime_call EJsonRuntimeLength el
      | OpSubstring start len => (* XXX Should be split into two different functions *)
        let start := ImpExprConst (ejnumber (float_of_int start)) in
        let args :=
            match len with
            | None => [ e; start ]
            | Some len =>
              let len := ImpExprConst (ejnumber (float_of_int len)) in
              [ e; start; len ]
            end
        in
        mk_imp_ejson_runtime_call EJsonRuntimeSubstring args
      | OpLike pat oescape =>
        mk_imp_ejson_expr_error "XXX TODO: ImpQcerttoImpEJson: OpLike XXX"
      | OpLeft => mk_left e
      | OpRight => mk_right e
      | OpBrand b =>
        mk_imp_ejson_runtime_call EJsonRuntimeBrand [ brands_to_ejson_expr (canon_brands h b); e ]
      | OpUnbrand => mk_imp_ejson_runtime_call EJsonRuntimeUnbrand el
      | OpCast b =>
        mk_imp_ejson_runtime_call EJsonRuntimeCast [ brands_to_ejson_expr b; e ]
      | OpNatUnary u =>
        let op :=
            match u with
            | NatAbs => EJsonRuntimeNatAbs
            | NatLog2 => EJsonRuntimeNatLog2
            | NatSqrt => EJsonRuntimeNatSqrt
            end
        in
        mk_imp_ejson_runtime_call op [ e ]
      | OpNatSum => mk_imp_ejson_runtime_call EJsonRuntimeNatSum el
      | OpNatMin => mk_imp_ejson_runtime_call EJsonRuntimeNatMin el
      | OpNatMax => mk_imp_ejson_runtime_call EJsonRuntimeNatMax el
      | OpNatMean => mk_imp_ejson_runtime_call EJsonRuntimeNatArithMean el
      | OpFloatOfNat => mk_imp_ejson_runtime_call EJsonRuntimeFloatOfNat el
      | OpFloatUnary u =>
        match u with
        | FloatNeg => mk_imp_ejson_op EJsonOpNeg [ e ]
        | FloatSqrt => mk_imp_ejson_op EJsonOpMathSqrt [ e ]
        | FloatExp => mk_imp_ejson_op EJsonOpMathExp [ e ]
        | FloatLog => mk_imp_ejson_op EJsonOpMathLog [ e ]
        | FloatLog10 => mk_imp_ejson_op EJsonOpMathLog10 [ e ]
        | FloatCeil => mk_imp_ejson_op EJsonOpMathCeil [ e ]
        | FloatFloor => mk_imp_ejson_op EJsonOpMathFloor [ e ]
        | FloatAbs => mk_imp_ejson_op EJsonOpMathAbs [ e ]
        end
      | OpFloatTruncate => mk_imp_ejson_op EJsonOpMathTrunc [e]
      | OpFloatSum => mk_imp_ejson_runtime_call EJsonRuntimeSum el
      | OpFloatMean => mk_imp_ejson_runtime_call EJsonRuntimeArithMean el
      | OpFloatBagMin => mk_imp_ejson_op EJsonOpMathMinApply [e]
      | OpFloatBagMax => mk_imp_ejson_op EJsonOpMathMaxApply [e]
      | OpForeignUnary fu =>
        mk_imp_ejson_expr_error "XXX TODO: ImpQcerttoImpEJson.imp_qcert_unary_op_to_imp_ejson OpForeignUnary"
      end
    | _ => mk_imp_ejson_expr_error "wrong number of arguments"
    end.

  Definition imp_qcert_binary_op_to_imp_ejson (op:binary_op) el : imp_ejson_expr :=
    match el with
    | [e1; e2] =>
      match op with
      | OpEqual => mk_imp_ejson_runtime_call EJsonRuntimeEqual el
      | OpRecConcat => mk_imp_ejson_runtime_call EJsonRuntimeRecConcat el
      | OpRecMerge => mk_imp_ejson_runtime_call EJsonRuntimeRecMerge el
      | OpAnd => mk_imp_ejson_op EJsonOpAnd el
      | OpOr => mk_imp_ejson_op EJsonOpOr el
      | OpLt =>
        mk_imp_ejson_op EJsonOpLt
                       [ mk_imp_ejson_runtime_call EJsonRuntimeCompare [e1; e2];
                         ImpExprConst (ejnumber zero) ]
      | OpLe =>
        mk_imp_ejson_op EJsonOpLe
                       [ mk_imp_ejson_runtime_call EJsonRuntimeCompare [e1; e2];
                         ImpExprConst (ejnumber zero) ]
      | OpBagUnion => mk_imp_ejson_runtime_call EJsonRuntimeBunion [e1; e2]
      | OpBagDiff => mk_imp_ejson_runtime_call EJsonRuntimeBminus [e1; e2]
      | OpBagMin => mk_imp_ejson_runtime_call EJsonRuntimeBmin [e1; e2]
      | OpBagMax => mk_imp_ejson_runtime_call EJsonRuntimeBmax [e1; e2]
      | OpBagNth => mk_imp_ejson_runtime_call EJsonRuntimeBnth [e1; e2]
      | OpContains => mk_imp_ejson_runtime_call EJsonRuntimeContains [e1; e2]
      | OpStringConcat => mk_imp_ejson_op EJsonOpAddString el
      | OpStringJoin => mk_imp_ejson_runtime_call EJsonRuntimeStringJoin [e1; e2]
      | OpNatBinary opa =>
        match opa with
        | NatPlus => mk_imp_ejson_runtime_call EJsonRuntimeNatPlus [e1; e2]
        | NatMinus => mk_imp_ejson_runtime_call EJsonRuntimeNatMinus [e1; e2]
        | NatMult => mk_imp_ejson_runtime_call EJsonRuntimeNatMult [e1; e2]
        | NatDiv => mk_imp_ejson_runtime_call EJsonRuntimeNatDiv [e1; e2]
        | NatRem => mk_imp_ejson_runtime_call EJsonRuntimeNatRem [e1; e2]
        | NatMin => mk_imp_ejson_runtime_call EJsonRuntimeNatMin [e1; e2]
        | NatMax => mk_imp_ejson_runtime_call EJsonRuntimeNatMax [e1; e2]
        end
      | OpFloatBinary opa =>
        match opa with
        | FloatPlus => mk_imp_ejson_op EJsonOpAddNumber [e1; e2]
        | FloatMinus => mk_imp_ejson_op EJsonOpSub [e1; e2]
        | FloatMult => mk_imp_ejson_op EJsonOpMult [e1; e2]
        | FloatDiv => mk_imp_ejson_op EJsonOpDiv [e1; e2]
        | FloatPow => mk_imp_ejson_op EJsonOpMathPow [e1; e2]
        | FloatMin => mk_imp_ejson_op EJsonOpMathMin [e1; e2]
        | FloatMax => mk_imp_ejson_op EJsonOpMathMax [e1; e2]
        end
      | OpFloatCompare opa =>
        match opa with
        | FloatLt => mk_imp_ejson_op EJsonOpLt [e1; e2]
        | FloatLe => mk_imp_ejson_op EJsonOpLe [e1; e2]
        | FloatGt => mk_imp_ejson_op EJsonOpGt [e1; e2]
        | FloatGe => mk_imp_ejson_op EJsonOpGe [e1; e2]
        end
      | OpForeignBinary fb =>
      (* foreign_to_ajavascript_binary_op fb [e1; e2] *)
        mk_imp_ejson_expr_error "XXX TODO: ImpQcerttoImpEJson.imp_qcert_binary_op_to_imp_ejson(OpForeignBinary): not yet implemented XXX" (* XXX TODO  *)
      end
    | _ => mk_imp_ejson_expr_error "imp_qcert_binary_op_to_imp_ejson: wrong number of arguments"
    end.

  Definition imp_qcert_op_to_imp_ejson (op:imp_qcert_op) el : imp_ejson_expr :=
    match op with
    | QcertOpUnary op => imp_qcert_unary_op_to_imp_ejson op el
    | QcertOpBinary op => imp_qcert_binary_op_to_imp_ejson op el
    end.

  Definition mk_either_expr (el:list imp_ejson_expr) : imp_ejson_expr :=
    mk_imp_ejson_runtime_call EJsonRuntimeEither el.

  Definition mk_to_left_expr (el:list imp_ejson_expr) : imp_ejson_expr :=
    mk_imp_ejson_runtime_call EJsonRuntimeToLeft el.

  Definition mk_to_right_expr (el:list imp_ejson_expr) : imp_ejson_expr :=
    mk_imp_ejson_runtime_call EJsonRuntimeToRight el.

  Definition imp_qcert_runtime_call_to_imp_ejson
             (op:imp_qcert_runtime_op)
             (el:list imp_ejson_expr) : imp_ejson_expr :=
    match op with
    | QcertRuntimeGroupby s ls =>
      mk_imp_ejson_runtime_call
        EJsonRuntimeGroupBy
        ((ImpExprConst (ejstring s))
           :: (ImpExprConst (ejarray (map ejstring ls)))
           :: el)
    | QcertRuntimeEither => mk_either_expr el
    | QcertRuntimeToLeft => mk_to_left_expr el
    | QcertRuntimeToRight => mk_to_right_expr el
    | QcertRuntimeDeref =>
      mk_imp_ejson_runtime_call EJsonRuntimeDeref el (* XXX ???? TODO *)
    end.

  Fixpoint imp_qcert_expr_to_imp_ejson (exp: imp_qcert_expr) : imp_ejson_expr :=
    match exp with
    | ImpExprError msg => ImpExprError msg
    | ImpExprVar v => ImpExprVar v
    | ImpExprConst d => ImpExprConst (@data_to_ejson _ _ _ (normalize_data h d)) (* XXX Add normalization *)
    | ImpExprOp op el => imp_qcert_op_to_imp_ejson op (map imp_qcert_expr_to_imp_ejson el)
    | ImpExprRuntimeCall op el => imp_qcert_runtime_call_to_imp_ejson op (map imp_qcert_expr_to_imp_ejson el)
    end.

  Fixpoint imp_qcert_stmt_to_imp_ejson (avoid: list string) (stmt: imp_qcert_stmt): imp_ejson_stmt :=
    match stmt with
    | ImpStmtBlock lv ls =>
      ImpStmtBlock
        (map (fun xy => (fst xy,
                         lift imp_qcert_expr_to_imp_ejson (snd xy))) lv)
        (map (imp_qcert_stmt_to_imp_ejson ((List.map fst lv) ++ avoid)) ls)
    | ImpStmtAssign v e =>
      ImpStmtAssign v (imp_qcert_expr_to_imp_ejson e)
    | ImpStmtFor v e s =>
      let avoid := v :: avoid in
      let e := imp_qcert_expr_to_imp_ejson e in
      let src_id := fresh_var "src" avoid in
      let avoid := src_id :: avoid in
      let i_id := fresh_var "i" avoid in
      let avoid := i_id :: avoid in
      let src := ImpExprVar src_id in
      let i := ImpExprVar i_id in
      ImpStmtBlock
        [ (src_id, Some e) ]
        [ ImpStmtForRange
            i_id (ImpExprConst (ejnumber zero)) (ImpExprOp EJsonOpArrayLength [ src ])
            (ImpStmtBlock
               [ (v, Some (ImpExprOp EJsonOpArrayAccess [ src; i ])) ]
               [ imp_qcert_stmt_to_imp_ejson avoid s ]) ]
    | ImpStmtForRange v e1 e2 s =>
      ImpStmtForRange v
                      (imp_qcert_expr_to_imp_ejson e1)
                      (imp_qcert_expr_to_imp_ejson e2)
                      (imp_qcert_stmt_to_imp_ejson (v :: avoid) s)
    | ImpStmtIf e s1 s2 =>
      ImpStmtIf (imp_qcert_expr_to_imp_ejson e)
                (imp_qcert_stmt_to_imp_ejson avoid s1)
                (imp_qcert_stmt_to_imp_ejson avoid s2)
    end.


  Definition imp_qcert_function_to_imp_ejson (f:imp_qcert_function) : imp_ejson_function :=
    match f with
    | ImpFun v s ret => ImpFun v (imp_qcert_stmt_to_imp_ejson [v] s) ret
    end.

  Fixpoint imp_qcert_to_imp_ejson (i:imp_qcert) : imp_ejson :=
    match i with
    | ImpLib l =>
      ImpLib
        (List.map
           (fun (decl: string * imp_qcert_function) =>
              let (name, def) := decl in (name, imp_qcert_function_to_imp_ejson def))
           l)
    end.

  Section Lift.
    Definition lift_bindings (env:bindings) : jbindings :=
      List.map (fun xy => (fst xy, data_to_ejson (snd xy))) env.
    Definition lift_pd_bindings (env:pd_bindings) : pd_jbindings :=
      List.map (fun xy => (fst xy, lift data_to_ejson (snd xy))) env.
    Definition lift_result (res:option ejson) : option data :=
      lift ejson_to_data res.
    Definition lift_result_env (res:option pd_jbindings) : option pd_bindings :=
      lift (fun env => List.map (fun xy => (fst xy, lift ejson_to_data (snd xy))) env) res.
  End Lift.

  Section Correctness.
    Lemma map_qcert_ejson_eval 
          (σ:pd_bindings) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp))) el -> 
      map (fun x : imp_qcert_expr => imp_qcert_expr_eval h σ x) el =
      map (fun x : imp_qcert_expr => lift_result
             (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson x))) el.
    Proof.
      intros.
      apply map_eq.
      assumption.
    Qed.

    Lemma normalize_data_dbool d b : normalize_data h d = dbool b <-> d = dbool b.
    Proof.
      destruct d; simpl; intuition discriminate.
    Qed.
    
    Lemma data_to_bool_ejson_to_bool_correct j:
      imp_qcert_data_to_bool (ejson_to_data j) = imp_ejson_data_to_bool j.
    Proof.
      unfold imp_qcert_data_to_bool.
      unfold imp_ejson_data_to_bool.
      destruct j; trivial.
      generalize (ejson_to_data_jobj_nbool l); intros HH1.
      match_destr.
      specialize (HH1 b); congruence.
    Qed.

    Lemma normalize_data_forall_ndnat d :  (forall n, d <> dnat n) -> (forall n, normalize_data h d <> dnat n).
    Proof.
      destruct d; simpl; intuition discriminate.
    Qed.

    Lemma data_to_bool_ejson_to_nat_correct j:
      imp_qcert_data_to_Z (ejson_to_data j) = imp_ejson_data_to_Z j.
    Proof.
      unfold imp_qcert_data_to_Z.
      unfold imp_ejson_data_to_Z.
      destruct j; trivial.
      case_eq (ejson_to_data (ejobject l)); intros; try reflexivity.
      generalize (ejson_to_data_object_not_nat l z); intros.
      contradiction.
    Qed.

    Lemma Forall_singleton σ i:
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp))) [i]
      -> imp_qcert_expr_eval h σ i
         = lift_result (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i)).
    Proof.
      intros.
      rewrite Forall_forall in H.
      specialize (H i).
      apply H.
      left; reflexivity.
    Qed.

    Lemma oflatten_eobject_is_none l l' :
      oflatten (map (fun x : ejson => ejson_to_data x) (ejobject l :: l')) = None.
    Proof.
      Opaque ejson_to_data.
      simpl.
      unfold oflatten.
      simpl.
      case_eq (ejson_to_data (ejobject l)); intros; try reflexivity.
      generalize (ejson_to_data_object_not_coll l l0); intros.
      contradiction.
      Transparent ejson_to_data.
    Qed.

    Lemma oflatten_jflatten_roundtrip l :
      match oflatten (map ejson_to_data l) with
      | Some a' => Some (dcoll a')
      | None => None
      end =
      match match jflatten l with
            | Some a' => Some (ejarray a')
            | None => None
            end with
      | Some a' => Some (ejson_to_data a')
      | None => None
      end.
    Proof.
      induction l; [reflexivity|].
      destruct a; try reflexivity.
      - case_eq (oflatten (map  ejson_to_data l));
          intros; rewrite H in *.
        + unfold jflatten in *.
          simpl.
          destruct (lift_flat_map (fun x : ejson => match x with
                                                | ejarray y => Some y
                                                | _ => None
                                                    end) l); simpl in *.
          inversion IHl; clear IHl; subst.
          rewrite (oflatten_cons _ _ (map ejson_to_data l2)); auto.
          simpl.
          rewrite map_app.
          reflexivity.
          congruence.
        + unfold jflatten in *.
          simpl.
          destruct (lift_flat_map (fun x : ejson => match x with
                                                | ejarray y => Some y
                                                | _ => None
                                                    end) l); simpl in *.
          congruence.
          rewrite oflatten_cons_none; auto.
      - rewrite oflatten_eobject_is_none.
        reflexivity.
    Qed.

    Lemma of_string_list_over_strings_idempotent sl :
      of_string_list (map (fun s : string => ejstring s) sl) = Some sl.
    Proof.
      induction sl; try reflexivity; simpl.
      unfold of_string_list in *; simpl.
      rewrite IHsl; reflexivity.
    Qed.

    Lemma json_brands_of_brands_idempotent b:
      ejson_brands (map ejstring b) = Some b.
    Proof.
      induction b; try reflexivity; simpl.
      rewrite IHb.
      reflexivity.
    Qed.

    Lemma bdistinct_ejson_to_data_comm l:
      bdistinct (map ejson_to_data l) = map ejson_to_data (bdistinct l).
    Proof.
      admit.
    Admitted.

    Lemma imp_qcert_unary_op_to_imp_ejson_expr_correct
           (σ:pd_bindings) (u:unary_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_ejson_expr_eval
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp))) el -> 
      imp_qcert_expr_eval h σ (ImpExprOp (QcertOpUnary u) el) =
      lift_result
        (imp_ejson_expr_eval (lift_pd_bindings σ)
                            (imp_qcert_unary_op_to_imp_ejson u (map imp_qcert_expr_to_imp_ejson el))).
    Proof.
      Opaque ejson_to_data.
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
      unfold imp_qcert_op_eval, imp_ejson_op_eval.
      unary_op_cases (destruct u) Case; unfold lift_result, lift, olift; simpl.
      - Case "OpIdentity"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
      - Case "OpNeg"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        destruct i0; try reflexivity.
        unfold unudbool.
        case_eq (ejson_to_data (ejobject l)); intros; try reflexivity.
        generalize (ejson_to_data_object_not_boolean l b); intros.
        congruence.
      - Case "OpRec"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity.
        simpl.
        f_equal.
        apply rec_ejson_key_encode_roundtrip.
      - Case "OpDot"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        unfold edot.
        apply assoc_lookupr_json_key_encode_roundtrip.
      - Case "OpRecRemove"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        apply rremove_json_key_encode_roundtrip.
      - Case "OpRecProject"%string.
        admit. (** XXX This one looks more complicated *)
      - Case "OpBag"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
      - Case "OpSingleton"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        + destruct l; try reflexivity; simpl.
          destruct l; try reflexivity; simpl.
          f_equal.
          destruct e; reflexivity.
        + case_eq (ejson_to_data (ejobject l)); intros; try reflexivity.
          generalize (ejson_to_data_object_not_coll l l0); intros.
          congruence.
      - Case "OpFlatten"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        + unfold lift. simpl.
          apply oflatten_jflatten_roundtrip.
        + simpl.
          case_eq (ejson_to_data (ejobject l)); intros; try reflexivity.
          generalize (ejson_to_data_object_not_coll l l0); intros.
          congruence.
      - Case "OpDistinct"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        + simpl.
          unfold rondcoll.
          unfold lift.
          unfold ondcoll.
          Transparent ejson_to_data.
          simpl.
          f_equal; f_equal.
          Opaque ejson_to_data.
          apply bdistinct_ejson_to_data_comm.
        + case_eq (ejson_to_data (ejobject l)); intros; try reflexivity.
          generalize (ejson_to_data_object_not_coll l l0); intros.
          congruence.
      - Case "OpOrderBy"%string.
        admit. (* XXX Not implemented *)
      - Case "OpCount"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        + Transparent ejson_to_data. unfold ejson_to_data; simpl.
          f_equal; f_equal; f_equal.
          unfold bcount.
          apply map_length.
          Opaque ejson_to_data.
        + case_eq (ejson_to_data (ejobject l)); intros; try reflexivity.
          generalize (ejson_to_data_object_not_coll l l0); intros.
          congruence.
      - Case "OpToString"%string.
        admit. (* XXX Not implemented *)
      - Case "OpToText"%string.
        admit. (* XXX Not implemented *)
      - Case "OpLength"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        case_eq (ejson_to_data (ejobject l)); intros; try reflexivity.
        generalize (ejson_to_data_object_not_string l s); intros.
        congruence.
      - Case "OpSubstring"%string.
        admit. (* XXX Not implemented *)
      - Case "OpLike"%string.
        admit. (* XXX Not implemented *)
      - Case "OpLeft"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        destruct i0; reflexivity.
      - Case "OpRight"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        destruct i0; reflexivity.
      - Case "OpBrand"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        rewrite of_string_list_over_strings_idempotent; simpl.
        Transparent ejson_to_data.
        unfold ejson_to_data; simpl.
        rewrite json_brands_of_brands_idempotent; simpl.
        destruct i0; try reflexivity; simpl.
        Opaque ejson_to_data.
      - Case "OpUnbrand"%string.
        destruct (imp_ejson_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity; simpl.
        destruct i0; try reflexivity; simpl.
        admit. (* XXX Shouldn't be too hard with proper lemma(s) tying json_to_data and dbrand *)
      - Case "OpCast"%string.
        admit. (* XXX Not implemented *)
      - Case "OpNatUnary"%string.
        admit. (* XXX Not implemented *)
      - Case "OpNatSum"%string.
        admit. (* XXX Not implemented *)
      - Case "OpNatMin"%string.
        admit. (* XXX Not implemented *)
      - Case "OpNatMax"%string.
        admit. (* XXX Not implemented *)
      - Case "OpNatMean"%string.
        admit. (* XXX Not implemented *)
      - Case "OpFloatOfNat"%string.
        admit. (* XXX Not implemented *)
      - Case "OpFloatUnary"%string.
        admit.
      - Case "OpFloatTruncate"%string.
        admit.
      - Case "OpFloatSum"%string.
        admit.
      - Case "OpFloatMean"%string.
        admit.
      - Case "OpFloatBagMin"%string.
        admit.
      - Case "OpFloatBagMax"%string.
        admit.
      - Case "OpForeignUnary"%string.
        admit.
    Admitted.

    Lemma imp_qcert_binary_op_to_imp_ejson_expr_correct
           (σ:pd_bindings) (b:binary_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_ejson_expr_eval
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp))) el -> 
      imp_qcert_expr_eval h σ (ImpExprOp (QcertOpBinary b) el) =
      lift_result
        (imp_ejson_expr_eval (lift_pd_bindings σ)
                            (imp_qcert_binary_op_to_imp_ejson b (map imp_qcert_expr_to_imp_ejson el))).
    Proof.
    Admitted.

    Lemma imp_qcert_runtime_call_to_imp_ejson_expr_correct
            (σ:pd_bindings) (rt:imp_qcert_runtime_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_ejson_expr_eval
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp))) el -> 
      imp_qcert_expr_eval h σ (ImpExprRuntimeCall rt el) =
      lift_result
        (imp_ejson_expr_eval (lift_pd_bindings σ)
                            (imp_qcert_runtime_call_to_imp_ejson rt (map imp_qcert_expr_to_imp_ejson el))).
    Proof.
    Admitted.

    Lemma imp_qcert_op_to_imp_ejson_correct
          (σ:pd_bindings) (op:imp_qcert_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_ejson_expr_eval
                (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp))) el -> 
      imp_qcert_expr_eval h σ (ImpExprOp op el) =
      lift_result
        (imp_ejson_expr_eval (lift_pd_bindings σ)
                            (imp_qcert_op_to_imp_ejson op (map imp_qcert_expr_to_imp_ejson el))).
    Proof.
      intros.
      destruct op.
      + apply imp_qcert_unary_op_to_imp_ejson_expr_correct; assumption.
      + apply imp_qcert_binary_op_to_imp_ejson_expr_correct; assumption.
    Qed.

    Lemma imp_qcert_expr_to_imp_ejson_expr_correct (σ:pd_bindings) (exp:imp_qcert_expr) :
      imp_qcert_expr_eval h σ exp =
      lift_result
        (imp_ejson_expr_eval (lift_pd_bindings σ)
                            (imp_qcert_expr_to_imp_ejson exp)).
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
        rewrite json_to_data_to_json_idempotent.
        reflexivity.
      - Case "ImpExprConst"%string.
        simpl.
        f_equal.
        unfold imp_qcert_data_normalize.
        unfold imp_ejson_data_normalize.
        rewrite json_to_data_to_json_idempotent.
        reflexivity.
      - Case "ImpExprOp"%string.
        apply imp_qcert_op_to_imp_ejson_correct; assumption.
      - Case "ImpExprRuntimeCall"%string.
        apply imp_qcert_runtime_call_to_imp_ejson_expr_correct; assumption.
    Qed.

    Lemma imp_qcert_stmt_to_imp_ejson_stmt_correct (σ:pd_bindings) (stmt:imp_qcert_stmt) :
      forall avoid: list string,
         (* (fres_var stmt) avoid -> *)
        imp_qcert_stmt_eval h stmt σ =
        lift_result_env (imp_ejson_stmt_eval (imp_qcert_stmt_to_imp_ejson avoid stmt) (lift_pd_bindings σ)).
    Proof.
      imp_stmt_cases (induction stmt) Case.
      - Case "ImpStmtBlock"%string.
        intros.
        (* XXX. Someing wrong here, missing inductive principle on imp statements. *)
        admit.
      - Case "ImpStmtAssign"%string.
        intros avoid.
        simpl.
        specialize (imp_qcert_expr_to_imp_ejson_expr_correct σ i).
        unfold imp_qcert_expr_eval in *.
        intros Hi.
        rewrite Hi.
        unfold lift_result.
        unfold lift.
        unfold imp_ejson_expr_eval.
        destruct (ImpEval.imp_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
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
          rewrite json_to_data_to_json_idempotent.
          reflexivity.
        + apply Hl; try reflexivity.
          destruct o0; try reflexivity.
          rewrite json_to_data_to_json_idempotent.
          reflexivity.
      - Case "ImpStmtFor"%string.
        intros avoid.
        specialize (imp_qcert_expr_to_imp_ejson_expr_correct σ i); simpl; unfold imp_qcert_expr_eval; intros.
        rewrite H; clear H.
        unfold lift_result; simpl.
        unfold imp_ejson_expr_eval; simpl.
        unfold lift; simpl.
        destruct (ImpEval.imp_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          simpl; [|reflexivity].
        (* XXX. Someing wrong here, likely translation to for-range variant always fails. *)
        admit.
      - Case "ImpStmtForRange"%string.
        intros avoid.
        admit. (* XXX TODO: eval XXX *)
      - Case "ImpStmtIf"%string.
        intros avoid.
        simpl.
        specialize (imp_qcert_expr_to_imp_ejson_expr_correct σ i).
        unfold imp_qcert_expr_eval in *.
        intros Hi.
        rewrite Hi.
        unfold lift_result.
        unfold lift.
        unfold imp_ejson_expr_eval.
        destruct (ImpEval.imp_expr_eval (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i));
          try reflexivity.
        rewrite data_to_bool_ejson_to_bool_correct.
        match_destr.
        match_destr.
    (* Qed. *)
    Admitted.

    Lemma imp_qcert_function_to_imp_ejson_function_correct (d:data) (f:imp_qcert_function) :
      imp_qcert_function_eval h f d =
      lift ejson_to_data (imp_ejson_function_eval (imp_qcert_function_to_imp_ejson f) (data_to_ejson d)).
    Proof.
      destruct f; simpl.
      generalize (imp_qcert_stmt_to_imp_ejson_stmt_correct [(v0, None); (v, Some d)] i (v::nil)); intros.
      unfold imp_qcert_stmt_eval in H.
      unfold imp_ejson_stmt_eval in H.
      unfold imp_qcert_data in *.
      rewrite H; clear H.
      unfold lift_result_env.
      unfold lift.
      case_eq (@ImpEval.imp_stmt_eval _ _ _ imp_ejson_data_normalize imp_ejson_data_to_bool imp_ejson_data_to_Z imp_ejson_data_to_list imp_ejson_Z_to_data imp_ejson_runtime_eval imp_ejson_op_eval (imp_qcert_stmt_to_imp_ejson [v] i) (lift_pd_bindings [(v0, None); (v, Some d)])); intros.
      - unfold olift.
        unfold imp_ejson_data in *.
        unfold imp_qcert_data in *.
        unfold imp_ejson_op in *.
        assert ((@ImpEval.imp_stmt_eval ejson ejson_op imp_ejson_runtime_op imp_ejson_data_normalize imp_ejson_data_to_bool
           imp_ejson_data_to_Z imp_ejson_data_to_list imp_ejson_Z_to_data imp_ejson_runtime_eval imp_ejson_op_eval
           (imp_qcert_stmt_to_imp_ejson (@cons var v (@nil var)) i)
           (lift_pd_bindings
              (@cons (prod var (option (@data (@foreign_runtime_data fruntime))))
                 (@pair var (option (@data (@foreign_runtime_data fruntime))) v0
                    (@None (@data (@foreign_runtime_data fruntime))))
                 (@cons (prod var (option (@data (@foreign_runtime_data fruntime))))
                    (@pair var (option (@data (@foreign_runtime_data fruntime))) v
                       (@Some (@data (@foreign_runtime_data fruntime)) d))
                    (@nil (prod var (option (@data (@foreign_runtime_data fruntime)))))))))
                = (@ImpEval.imp_stmt_eval ejson ejson_op imp_ejson_runtime_op imp_ejson_data_normalize imp_ejson_data_to_bool
          imp_ejson_data_to_Z imp_ejson_data_to_list imp_ejson_Z_to_data imp_ejson_runtime_eval imp_ejson_op_eval
          (imp_qcert_stmt_to_imp_ejson (@cons var v (@nil var)) i)
          (@cons (prod var (option ejson)) (@pair var (option ejson) v0 (@None ejson))
             (@cons (prod var (option ejson))
                (@pair var (option ejson) v (@Some ejson (@data_to_ejson (@foreign_runtime_data fruntime) _ ftejson d)))
                (@nil (prod var (option ejson))))))) by reflexivity.
        rewrite H0 in *; clear H0.
        rewrite H; clear H.
        generalize (@lookup_map_codomain_unfolded string (option ejson) (option data) string_dec (fun x => match x with
                   | Some a' => Some (ejson_to_data a')
                   | None => None
                   end)); intros.
        rewrite H; clear H.
        unfold lift.
        assert (@lookup string (option ejson) string_dec p v0 = lookup EquivDec.equiv_dec p v0) by reflexivity.
        rewrite H; clear H.
        case_eq (lookup EquivDec.equiv_dec p v0); intros; try reflexivity.
      - unfold olift.
        unfold imp_ejson_data in *.
        unfold imp_qcert_data in *.
        unfold imp_ejson_op in *.
        assert ((@ImpEval.imp_stmt_eval ejson ejson_op imp_ejson_runtime_op imp_ejson_data_normalize imp_ejson_data_to_bool
           imp_ejson_data_to_Z imp_ejson_data_to_list imp_ejson_Z_to_data imp_ejson_runtime_eval imp_ejson_op_eval
           (imp_qcert_stmt_to_imp_ejson (@cons var v (@nil var)) i)
           (lift_pd_bindings
              (@cons (prod var (option (@data (@foreign_runtime_data fruntime))))
                 (@pair var (option (@data (@foreign_runtime_data fruntime))) v0
                    (@None (@data (@foreign_runtime_data fruntime))))
                 (@cons (prod var (option (@data (@foreign_runtime_data fruntime))))
                    (@pair var (option (@data (@foreign_runtime_data fruntime))) v
                       (@Some (@data (@foreign_runtime_data fruntime)) d))
                    (@nil (prod var (option (@data (@foreign_runtime_data fruntime)))))))))
                = (@ImpEval.imp_stmt_eval ejson ejson_op imp_ejson_runtime_op imp_ejson_data_normalize imp_ejson_data_to_bool
          imp_ejson_data_to_Z imp_ejson_data_to_list imp_ejson_Z_to_data imp_ejson_runtime_eval imp_ejson_op_eval
          (imp_qcert_stmt_to_imp_ejson (@cons var v (@nil var)) i)
          (@cons (prod var (option ejson)) (@pair var (option ejson) v0 (@None ejson))
             (@cons (prod var (option ejson))
                (@pair var (option ejson) v (@Some ejson (@data_to_ejson (@foreign_runtime_data fruntime) _ ftejson d)))
                (@nil (prod var (option ejson))))))) by reflexivity.
        rewrite H0 in *; clear H0.
        rewrite H.
        reflexivity.
    Qed.

    Lemma push_rec_sort_in_map env :
      (rec_sort (map (fun xy : string * data => (fst xy, data_to_ejson (snd xy))) env))
      = (map (fun xy : string * data => (fst xy, data_to_ejson (snd xy))) (rec_sort env)).
    Proof.
      rewrite map_rec_sort.
      - reflexivity.
      - intros; split; intros; auto.
    Qed.

    Theorem imp_qcert_to_imp_ejson_correct (σc:bindings) (q:imp_qcert) :
      imp_qcert_eval_top h σc q =
      imp_ejson_eval_top σc (imp_qcert_to_imp_ejson q).
    Proof.
      unfold imp_qcert_eval_top.
      unfold imp_ejson_eval_top.
      unfold imp_ejson_eval_top_on_ejson.
      unfold imp_ejson_eval.
      destruct q; simpl.
      destruct l; try reflexivity; simpl.
      destruct p; simpl.
      destruct l; try reflexivity; simpl.
      generalize (imp_qcert_function_to_imp_ejson_function_correct (drec (rec_sort σc)) i); intros.
      unfold imp_qcert_eval_top.
      unfold imp_ejson_eval_top.
      unfold imp_ejson_eval_top_on_ejson.
      unfold imp_ejson_eval.
      unfold id; simpl.
      simpl in H.
      unfold imp_qcert_function_eval in H.
      unfold imp_ejson_function_eval in H.
      rewrite H; clear H.
      f_equal.
      f_equal.
      f_equal.
      rewrite push_rec_sort_in_map.
      rewrite map_map.
      reflexivity.
    Qed.

  End Correctness.

End ImpQcerttoImpEJson.
