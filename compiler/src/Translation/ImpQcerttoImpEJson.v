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
Require Import JsAst.JsNumber.
Require Import Fresh.
Require Import DataRuntime.
Require Import ImpRuntime.
Require Import ForeignDataToEJson.
Require Import DatatoEJson.

Section ImpQcerttoImpEJson.
  Import ListNotations.

  Context {fruntime:foreign_runtime}.
  Context {ftejson:foreign_to_ejson}.

  Context (h:brand_relation_t). (* We need a brand relation for the Q*cert side *)

  Section Util.
    Definition mk_imp_ejson_expr_error msg : imp_ejson_expr :=
      ImpExprError msg. (* XXX Error should eval to None if we want to prove stuffs! *)
    Definition mk_imp_ejson_op op el : imp_ejson_expr := ImpExprOp op el.
    Definition mk_imp_ejson_runtime_call op el : imp_ejson_expr := ImpExprRuntimeCall op el.

    Definition mk_string s : imp_ejson_expr := ImpExprConst (ejstring s).
    Definition mk_string_array sl : imp_ejson_expr := ImpExprConst (ejarray (map ejstring sl)).
    Definition mk_bag el : imp_ejson_expr := mk_imp_ejson_op EJsonOpArray el.
    Definition mk_left e : imp_ejson_expr := mk_imp_ejson_op (EJsonOpObject ["$left"%string]) [ e ].
    Definition mk_right e : imp_ejson_expr := mk_imp_ejson_op (EJsonOpObject ["$right"%string]) [ e ].

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

    Definition mk_either_expr (el:list imp_ejson_expr) : imp_ejson_expr :=
      mk_imp_ejson_runtime_call EJsonRuntimeEither el.

    Definition mk_to_left_expr (el:list imp_ejson_expr) : imp_ejson_expr :=
      mk_imp_ejson_runtime_call EJsonRuntimeToLeft el.

    Definition mk_to_right_expr (el:list imp_ejson_expr) : imp_ejson_expr :=
      mk_imp_ejson_runtime_call EJsonRuntimeToRight el.

    Lemma imp_qcert_data_to_list_comm d :
      lift (map ejson_to_data) (imp_ejson_data_to_list (data_to_ejson d)) =
      imp_qcert_data_to_list d.
    Proof.
      unfold lift.
      destruct d; simpl; try reflexivity.
      f_equal.
      rewrite map_map.
      rewrite map_eq_id; try reflexivity.
      rewrite Forall_forall; intros.
      rewrite data_to_ejson_idempotent.
      reflexivity.
    Qed.

    Lemma imp_ejson_data_to_list_comm d :
      (imp_ejson_data_to_list (data_to_ejson d)) =
      lift (map data_to_ejson) (imp_qcert_data_to_list d).
    Proof.
      unfold lift.
      destruct d; simpl; reflexivity.
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

    Lemma ejson_to_data_to_Z_comm j:
      imp_qcert_data_to_Z (ejson_to_data j) = imp_ejson_data_to_Z j.
    Proof.
      unfold imp_qcert_data_to_Z.
      unfold imp_ejson_data_to_Z.
      destruct j; trivial.
      case_eq (ejson_to_data (ejobject l)); intros; try reflexivity.
      generalize (ejson_to_data_object_not_nat l z); intros.
      contradiction.
    Qed.

    Lemma data_to_ejson_to_Z_comm d:
      imp_qcert_data_to_Z d = imp_ejson_data_to_Z (data_to_ejson d).
    Proof.
      destruct d; try reflexivity.
    Qed.

    Lemma ejson_lifted_fbag_comm l:
      lifted_fbag l =
      ejson_numbers (map data_to_ejson l).
    Proof.
      induction l; simpl; try reflexivity.
      unfold lifted_fbag in *; simpl.
      rewrite IHl; simpl; clear IHl.
      destruct a; reflexivity.
    Qed.

  End Util.

  Section Translation.
    
    Definition imp_qcert_unary_op_to_imp_ejson (op:unary_op) el : imp_ejson_expr :=
      match el with
      | [e] =>
        match op with
        | OpIdentity => e
        | OpNeg => mk_imp_ejson_op EJsonOpNot [ e ]
        | OpRec s => mk_imp_ejson_op (EJsonOpObject [json_key_encode s]) [ e ]
        | OpDot s => mk_imp_ejson_runtime_call EJsonRuntimeRecDot [ e; ImpExprConst (ejstring (json_key_encode s)) ]
        | OpRecRemove s => mk_imp_ejson_runtime_call EJsonRuntimeRecRemove [ e; mk_string (json_key_encode s) ]
        | OpRecProject fl =>
          mk_imp_ejson_runtime_call
            EJsonRuntimeRecProject ([ e ] ++ [ mk_string_array (map json_key_encode fl) ])
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
          let op := 
              match u with
              | FloatNeg => EJsonOpNeg
              | FloatSqrt => EJsonOpMathSqrt
              | FloatExp => EJsonOpMathExp
              | FloatLog => EJsonOpMathLog
              | FloatLog10 => EJsonOpMathLog10
              | FloatCeil => EJsonOpMathCeil
              | FloatFloor => EJsonOpMathFloor
              | FloatAbs => EJsonOpMathAbs
              end
          in mk_imp_ejson_op op [ e ]
        | OpFloatTruncate => mk_imp_ejson_op EJsonOpMathTrunc [ e ]
        | OpFloatSum => mk_imp_ejson_runtime_call EJsonRuntimeFloatSum el
        | OpFloatMean => mk_imp_ejson_runtime_call EJsonRuntimeFloatArithMean el
        | OpFloatBagMin => mk_imp_ejson_op EJsonOpMathMinApply [ e ]
        | OpFloatBagMax => mk_imp_ejson_op EJsonOpMathMaxApply [ e ]
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
        | OpBagUnion => mk_imp_ejson_runtime_call EJsonRuntimeUnion [e1; e2]
        | OpBagDiff => mk_imp_ejson_runtime_call EJsonRuntimeMinus [e1; e2]
        | OpBagMin => mk_imp_ejson_runtime_call EJsonRuntimeMin [e1; e2]
        | OpBagMax => mk_imp_ejson_runtime_call EJsonRuntimeMax [e1; e2]
        | OpBagNth => mk_imp_ejson_runtime_call EJsonRuntimeNth [e1; e2]
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
          | NatMin => mk_imp_ejson_runtime_call EJsonRuntimeNatMinPair [e1; e2]
          | NatMax => mk_imp_ejson_runtime_call EJsonRuntimeNatMaxPair [e1; e2]
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
      end.

    Fixpoint imp_qcert_expr_to_imp_ejson (exp: imp_qcert_expr) : imp_ejson_expr :=
      match exp with
      | ImpExprError msg => ImpExprError msg
      | ImpExprVar v => ImpExprVar v
      | ImpExprConst d => ImpExprConst (data_to_ejson (normalize_data h d)) (* XXX Add normalization *)
      | ImpExprOp op el => imp_qcert_op_to_imp_ejson op (map imp_qcert_expr_to_imp_ejson el)
      | ImpExprRuntimeCall op el => imp_qcert_runtime_call_to_imp_ejson op (map imp_qcert_expr_to_imp_ejson el)
      end.

    Fixpoint imp_qcert_stmt_to_imp_ejson (stmt: imp_qcert_stmt): imp_ejson_stmt :=
      match stmt with
      | ImpStmtBlock lv ls =>
        ImpStmtBlock
          (map (fun xy => (fst xy, lift imp_qcert_expr_to_imp_ejson (snd xy))) lv)
          (map imp_qcert_stmt_to_imp_ejson ls)
      | ImpStmtAssign v e =>
        ImpStmtAssign v (imp_qcert_expr_to_imp_ejson e)
      | ImpStmtFor v e s =>
        ImpStmtFor v
                   (imp_qcert_expr_to_imp_ejson e)
                   (imp_qcert_stmt_to_imp_ejson s)
      | ImpStmtForRange v e1 e2 s =>
        ImpStmtForRange v
                        (imp_qcert_expr_to_imp_ejson e1)
                        (imp_qcert_expr_to_imp_ejson e2)
                        (imp_qcert_stmt_to_imp_ejson s)
      | ImpStmtIf e s1 s2 =>
        ImpStmtIf (imp_qcert_expr_to_imp_ejson e)
                  (imp_qcert_stmt_to_imp_ejson s1)
                  (imp_qcert_stmt_to_imp_ejson s2)
      end.

    Section ForRewrite.
      (* Rewriting functional for into imperative for loop is now isolated *)
      (* If we want to combine both rewrites into a single pass *)
      Fixpoint imp_qcert_stmt_to_imp_ejson_combined (avoid: list string) (stmt: imp_qcert_stmt): imp_ejson_stmt :=
        match stmt with
        | ImpStmtBlock lv ls =>
          ImpStmtBlock
            (map (fun xy => (fst xy,
                             lift imp_qcert_expr_to_imp_ejson (snd xy))) lv)
            (map (imp_qcert_stmt_to_imp_ejson_combined ((List.map fst lv) ++ avoid)) ls)
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
                i_id
                (ImpExprConst (ejbigint 0))
                (* XXX Use src.length - 1, consistent with semantic of 'for i1 to i2 do ... done' loop *)
                (ImpExprRuntimeCall EJsonRuntimeNatMinus [ ImpExprOp EJsonOpArrayLength [ src ] ; ImpExprConst (ejbigint 1) ])
                (ImpStmtBlock
                   [ (v, Some (ImpExprOp EJsonOpArrayAccess [ src; i ])) ]
                   [ imp_qcert_stmt_to_imp_ejson_combined avoid s ]) ]
        | ImpStmtForRange v e1 e2 s =>
          ImpStmtForRange v
                          (imp_qcert_expr_to_imp_ejson e1)
                          (imp_qcert_expr_to_imp_ejson e2)
                          (imp_qcert_stmt_to_imp_ejson_combined (v :: avoid) s)
        | ImpStmtIf e s1 s2 =>
          ImpStmtIf (imp_qcert_expr_to_imp_ejson e)
                    (imp_qcert_stmt_to_imp_ejson_combined avoid s1)
                    (imp_qcert_stmt_to_imp_ejson_combined avoid s2)
        end.

      Lemma imp_qcert_stmt_to_imp_ejson_combined_idem avoid (stmt: imp_qcert_stmt):
        imp_qcert_stmt_to_imp_ejson_combined avoid stmt =
        imp_ejson_stmt_for_rewrite avoid (imp_qcert_stmt_to_imp_ejson stmt).
      Proof.
        revert avoid.
        imp_stmt_cases (induction stmt) Case; intros; simpl.
        + Case "ImpStmtBlock"%string.
          repeat rewrite map_map.
          f_equal.
          assert
            (Hforall:
               Forall
                 (fun stmt : imp_stmt =>
                    imp_qcert_stmt_to_imp_ejson_combined (map fst el ++ avoid) stmt =
                    imp_ejson_stmt_for_rewrite (map fst el ++ avoid) (imp_qcert_stmt_to_imp_ejson stmt)) sl)
            by
              (apply (@Forall_impl
                        imp_stmt
                        (fun stmt : imp_stmt =>
                           forall avoid : list string,
                             imp_qcert_stmt_to_imp_ejson_combined avoid stmt =
                             imp_ejson_stmt_for_rewrite avoid (imp_qcert_stmt_to_imp_ejson stmt))
                        (fun stmt : imp_stmt =>
                           imp_qcert_stmt_to_imp_ejson_combined (map fst el ++ avoid) stmt =
                           imp_ejson_stmt_for_rewrite (map fst el ++ avoid) (imp_qcert_stmt_to_imp_ejson stmt)));
               try assumption; intros; apply H0); clear H.
          apply (map_eq Hforall).
        + Case "ImpStmtAssign"%string.
          reflexivity.
        + Case "ImpStmtFor"%string.
          repeat f_equal.
          rewrite IHstmt.
          reflexivity.
        + Case "ImpStmtForRange"%string.
          rewrite IHstmt.
          reflexivity.
        + Case "ImpStmtIf"%string.
          repeat f_equal.
          apply IHstmt1.
          apply IHstmt2.
      Qed.

    End ForRewrite.

    Definition imp_qcert_function_to_imp_ejson (f:imp_qcert_function) : imp_ejson_function :=
      match f with
      | ImpFun v s ret => ImpFun v (imp_qcert_stmt_to_imp_ejson_combined [v] s) ret
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
  End Translation.

  Section Correctness.
    Section Lift.
      Definition lift_bindings (env:bindings) : jbindings :=
        List.map (fun xy => (fst xy, data_to_ejson (snd xy))) env.
      Definition lift_pd_bindings (env:pd_bindings) : pd_jbindings :=
        List.map (fun xy => (fst xy, lift data_to_ejson (snd xy))) env.
      Definition lift_result (res:option ejson) : option data :=
        lift ejson_to_data res.
      Definition unlift_result (res:option data) : option ejson :=
        lift data_to_ejson res.
      Definition lift_result_env (res:option pd_jbindings) : option pd_bindings :=
        lift (fun env => List.map (fun xy => (fst xy, lift ejson_to_data (snd xy))) env) res.
      Definition unlift_result_env (res:option pd_bindings) : option pd_jbindings :=
        lift (fun env => List.map (fun xy => (fst xy, lift data_to_ejson (snd xy))) env) res.
    End Lift.

    Lemma dsum_to_ejson_sum l :
      match match dsum l with
            | Some a' => Some (dnat a')
            | None => None
            end with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match ejson_bigints (map data_to_ejson l) with
      | Some zl => Some (ejbigint (fold_right BinInt.Z.add BinNums.Z0 zl))
      | None => None
      end.
    Proof.
      induction l; [reflexivity|]; simpl in *.
      destruct a; simpl; trivial.
      unfold lift.
      destruct (dsum l); destruct (ejson_bigints (map data_to_ejson l)); simpl in *; congruence.
    Qed.

    Lemma lifted_zbag_is_ejson_bigint l:
      lifted_zbag l = ejson_bigints (map data_to_ejson l).
    Proof.
      unfold lifted_zbag.
      induction l; simpl; try reflexivity.
      rewrite <- IHl.
      destruct a; simpl; trivial.
    Qed.

    Lemma dmin_to_ejson_min l:
      match lifted_min l with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match ejson_bigints (map data_to_ejson l) with
      | Some zl => Some (ejbigint (bnummin zl))
      | None => None
      end.
    Proof.
      rewrite <- lifted_zbag_is_ejson_bigint.
      unfold lifted_min, lift; simpl.
      destruct (lifted_zbag l); reflexivity.
    Qed.

    Lemma dmax_to_ejson_max l:
      match lifted_max l with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end =
      match ejson_bigints (map data_to_ejson l) with
      | Some zl => Some (ejbigint (bnummax zl))
      | None => None
      end.
    Proof.
      rewrite <- lifted_zbag_is_ejson_bigint.
      unfold lifted_max, lift; simpl.
      destruct (lifted_zbag l); reflexivity.
    Qed.

    Ltac rewrite_string_dec_from_neq H
      :=  let d := fresh "d" in
          let neq := fresh "neq" in
          destruct (string_dec_from_neq H) as [d neq]
          ; repeat rewrite neq in *
          ; clear d neq.

    Lemma imp_qcert_unary_op_to_imp_ejson_expr_correct
           (σ:pd_bindings) (u:unary_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           unlift_result (imp_qcert_expr_eval h σ exp) =
           imp_ejson_expr_eval
             h (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp)) el -> 
      unlift_result (imp_qcert_expr_eval h σ (ImpExprOp (QcertOpUnary u) el)) =
      imp_ejson_expr_eval h
                          (lift_pd_bindings σ)
                          (imp_qcert_unary_op_to_imp_ejson u (map imp_qcert_expr_to_imp_ejson el)).
    Proof.
      Opaque ejson_to_data.
      intros.
      (* elim no params *)
      destruct el; [reflexivity|].
      (* elim two or more params *)
      destruct el; simpl;
        [|destruct (imp_qcert_expr_eval h σ i); [|reflexivity];
          destruct (imp_qcert_expr_eval h σ i0); [|reflexivity];
          unfold lift, olift;
          case_eq
            (lift_map (fun x : option imp_qcert_data => x)
                      (map (fun x : imp_qcert_expr => imp_qcert_expr_eval h σ x) el)); intros;
          unfold imp_qcert_data, ImpEval.imp_expr, imp_qcert_expr, imp_qcert_data, foreign_runtime_data in *;
          rewrite H0; reflexivity].
      (* just one param *)
      apply Forall_inv in H.
      unary_op_cases (destruct u) Case; unfold lift_result, lift, olift; simpl;
        try (rewrite <- H; clear H;
             destruct (imp_qcert_expr_eval h σ i);
             try reflexivity; simpl; unfold unlift_result, lift; simpl).
      - Case "OpNeg"%string.
        destruct d; try reflexivity.
      - Case "OpDot"%string.
        unfold edot.
        apply assoc_lookupr_json_key_encode_comm.
      - Case "OpRecRemove"%string.
        apply rremove_json_key_encode_comm.
      - Case "OpRecProject"%string.
        apply rproject_json_key_encode_comm.
      - Case "OpSingleton"%string.
        destruct d; try reflexivity.
        destruct l; try reflexivity; simpl.
        destruct l; try reflexivity; simpl.
      - Case "OpFlatten"%string.
        destruct d; try reflexivity; simpl.
        apply flat_map_jflatten_roundtrip.
      - Case "OpDistinct"%string.
        destruct d; simpl; try reflexivity.
        rewrite bdistinct_ejson_to_data_comm; reflexivity.
      - Case "OpOrderBy"%string.
        admit. (* XXX Not implemented *)
      - Case "OpCount"%string.
        destruct d; simpl; try reflexivity.
        destruct l; simpl in *; try reflexivity.
        unfold bcount.
        rewrite map_length.
        reflexivity.
      - Case "OpToString"%string.
        admit. (* XXX Not implemented *)
      - Case "OpToText"%string.
        admit. (* XXX Not implemented *)
      - Case "OpLength"%string.
        destruct d; reflexivity.
      - Case "OpSubstring"%string.
        admit. (* XXX Not implemented *)
      - Case "OpLike"%string.
        admit. (* XXX Not implemented *)
      - Case "OpBrand"%string.
        rewrite of_string_list_map_ejstring; simpl.
        reflexivity.
      - Case "OpUnbrand"%string.
        case_eq d; intros; simpl; try reflexivity; try (destruct d0; reflexivity).
        + destruct l; simpl; try reflexivity;
            destruct p; simpl; try reflexivity;
          destruct d0; try reflexivity;
          rewrite_string_dec_from_neq (json_key_encode_not_class s);
          destruct l0; simpl; try reflexivity;
          destruct l; simpl; try reflexivity;
          destruct l; simpl; try reflexivity.
        + rewrite ejson_brands_map_ejstring; reflexivity.
      - Case "OpCast"%string.
        rewrite ejson_brands_map_ejstring.
        case_eq d; intros; simpl; try reflexivity; try (destruct d0; reflexivity).
        + destruct l; simpl; try reflexivity;
            destruct p; simpl; try reflexivity;
          destruct d0; try reflexivity;
          rewrite_string_dec_from_neq (json_key_encode_not_class s);
          destruct l0; simpl; try reflexivity;
          destruct l; simpl; try reflexivity;
          destruct l; simpl; try reflexivity.
        + rewrite ejson_brands_map_ejstring.
          destruct (sub_brands_dec h b0 b); reflexivity.
      - Case "OpNatUnary"%string.
        destruct n; simpl in *;
        destruct d; simpl; trivial.
      - Case "OpNatSum"%string.
        destruct d; simpl; trivial.
        rewrite dsum_to_ejson_sum.
        reflexivity.
      - Case "OpNatMin"%string.
        destruct d; simpl; trivial.
        rewrite dmin_to_ejson_min; reflexivity.
      - Case "OpNatMax"%string.
        destruct d; simpl; trivial.
        rewrite dmax_to_ejson_max; reflexivity.
      - Case "OpNatMean"%string.
        destruct d; simpl; trivial.
        unfold darithmean.
        unfold lift.
        generalize (dsum_to_ejson_sum l); intros.
        rewrite map_length.
        generalize (BinInt.Z.of_nat (Datatypes.length l)); intro len.
        destruct (dsum l); destruct (ejson_bigints (map data_to_ejson l)); try congruence.
        inversion H; subst; reflexivity.
      - Case "OpFloatOfNat"%string.
        destruct d; reflexivity.
      - Case "OpFloatUnary"%string.
        destruct f; simpl;
        destruct d; reflexivity.
      - Case "OpFloatTruncate"%string.
        destruct d; reflexivity.
      - Case "OpFloatSum"%string.
        destruct d; try reflexivity; simpl.
        unfold lifted_fsum, lift; simpl.
        rewrite <- ejson_lifted_fbag_comm.
        destruct (lifted_fbag l); reflexivity.
      - Case "OpFloatMean"%string.
        destruct d; try reflexivity; simpl.
        unfold lifted_farithmean, lift; simpl.
        rewrite <- ejson_lifted_fbag_comm.
        destruct (lifted_fbag l); try reflexivity.
      - Case "OpFloatBagMin"%string.
        admit.
      - Case "OpFloatBagMax"%string.
        admit.
      - Case "OpForeignUnary"%string.
        admit.
        Transparent ejson_to_data.
    Admitted.

    Lemma imp_qcert_binary_op_to_imp_ejson_expr_correct
           (σ:pd_bindings) (b:binary_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           unlift_result (imp_qcert_expr_eval h σ exp) =
           imp_ejson_expr_eval
             h
             (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp)) el -> 
      unlift_result (imp_qcert_expr_eval h σ (ImpExprOp (QcertOpBinary b) el)) =
      imp_ejson_expr_eval h (lift_pd_bindings σ)
                          (imp_qcert_binary_op_to_imp_ejson b (map imp_qcert_expr_to_imp_ejson el)).
    Proof.
      Opaque ejson_to_data.
      intros.
      (* elim no params *)
      destruct el; [reflexivity|].
      (* elim one params *)
      destruct el; [simpl; destruct (imp_qcert_expr_eval h σ i); reflexivity|].
      (* elim two or more params *)
      destruct el; simpl;
        [|destruct (imp_qcert_expr_eval h σ i); [|reflexivity];
          destruct (imp_qcert_expr_eval h σ i0); [|reflexivity];
          destruct (imp_qcert_expr_eval h σ i1); [|reflexivity];
          unfold lift, olift;
          case_eq
            (lift_map (fun x : option imp_qcert_data => x)
                      (map (fun x : imp_qcert_expr => imp_qcert_expr_eval h σ x) el)); intros;
          unfold imp_qcert_data, ImpEval.imp_expr, imp_qcert_expr, imp_qcert_data, foreign_runtime_data in *;
          rewrite H0; reflexivity].
      (* just two param *)
      inversion H; clear H; intros; subst; apply Forall_inv in H3.
      binary_op_cases (destruct b) Case; unfold lift_result, lift, olift; simpl;
        (* try (destruct n; simpl); *)
        try (rewrite <- H2; clear H2;
             destruct (imp_qcert_expr_eval h σ i);
             try reflexivity; simpl; unfold unlift_result, lift; simpl;
             try (destruct n);
             rewrite <- H3; clear H3;
             destruct (imp_qcert_expr_eval h σ i0);
             try reflexivity; simpl; unfold unlift_result, lift; simpl).
      - Case "OpEqual"%string.
        destruct (data_eq_dec d d0);
          destruct (ejson_eq_dec (data_to_ejson d) (data_to_ejson d0));
          try reflexivity; subst.
        + congruence.
        + apply data_to_ejson_inv in e; congruence.
      - Case "OpRecConcat"%string.
        admit.
      - Case "OpRecMerge"%string.
        admit.
      - Case "OpAnd"%string.
        destruct d; destruct d0; reflexivity.
      - Case "OpOr"%string.
        destruct d; destruct d0; reflexivity.
      - Case "OpLt"%string.
        admit.
      - Case "OpLe"%string.
        admit.
      - Case "OpBagUnion"%string.
        unfold rondcoll2, ondcoll2, lift; simpl.
        destruct d; destruct d0; simpl; try reflexivity.
        unfold bunion.
        rewrite map_app.
        reflexivity.
      - Case "OpBagDiff"%string.
        unfold rondcoll2, ondcoll2, lift; simpl.
        destruct d; destruct d0; simpl; try reflexivity.
        unfold bminus.
        admit.
      - Case "OpBagMin"%string.
        admit.
      - Case "OpBagMax"%string.
        admit.
      - Case "OpBagNth"%string.
        admit. (* XXX Not implemented *)
      - Case "OpContains"%string.
        admit. (* XXX Not implemented *)
      - Case "OpStringConcat"%string.
        destruct d; destruct d0; reflexivity.
      - Case "OpStringJoin"%string.
        admit. (* XXX Not implemented *)
      - Case "OpNatBinary"%string.
        destruct n;
          simpl;
          rewrite <- H2; clear H2;
            destruct (imp_qcert_expr_eval h σ i);
            try reflexivity; simpl; unfold unlift_result, lift; simpl;
              try (destruct n);
              rewrite <- H3; clear H3;
                destruct (imp_qcert_expr_eval h σ i0);
                try reflexivity; simpl; unfold unlift_result, lift; simpl;
                  destruct d; destruct d0; try reflexivity.
      - Case "OpFloatBinary"%string.
        admit.
      - Case "OpFloatCompare"%string.
        admit.
      - Case "OpForeignBinary"%string.
        admit.
      Transparent ejson_to_data.
    Admitted.

    Lemma imp_qcert_runtime_call_to_imp_ejson_correct
          (σ:pd_bindings) (rt:imp_qcert_runtime_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           unlift_result (imp_qcert_expr_eval h σ exp) =
           imp_ejson_expr_eval h (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp)) el -> 
      unlift_result (imp_qcert_expr_eval h σ (ImpExprRuntimeCall rt el)) =
      imp_ejson_expr_eval h (lift_pd_bindings σ)
                          (imp_qcert_runtime_call_to_imp_ejson rt (map imp_qcert_expr_to_imp_ejson el)).
    Proof.
      Opaque ejson_to_data. {
        intros.
        imp_qcert_runtime_op_cases(destruct rt) Case; simpl.
        - Case "QcertRuntimeGroupby"%string.
          admit. (* XXX Not implemented *)
        - Case "QcertRuntimeEither"%string.
          admit.
        - Case "QcertRuntimeLeft"%string.
          admit. (* XXX Not implemented *)
        - Case "QcertRuntimeRight"%string.
          admit. (* XXX Not implemented *)
      }
      Transparent ejson_to_data.
    Admitted.

    (* XXX This lemma looses the key assumption that the ejson returned is idempotent to data *)
    Lemma relax_assumption_temp σ el:
      Forall
        (fun exp : imp_expr =>
           unlift_result (imp_qcert_expr_eval h σ exp) =
           imp_ejson_expr_eval h (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp)) el -> 
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_ejson_expr_eval h
                                  (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp))) el.
    Proof.
      intros.
      rewrite Forall_forall;
        rewrite Forall_forall in H; intros.
      specialize (H x H0).
      rewrite <- H.
      unfold unlift_result, lift_result, lift; simpl.
      destruct (imp_qcert_expr_eval h σ x); [rewrite data_to_ejson_idempotent|]; reflexivity.
    Qed.

    Lemma imp_qcert_op_to_imp_ejson_correct
          (σ:pd_bindings) (op:imp_qcert_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           unlift_result (imp_qcert_expr_eval h σ exp) =
           imp_ejson_expr_eval h (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp)) el -> 
      unlift_result (imp_qcert_expr_eval h σ (ImpExprOp op el)) =
      imp_ejson_expr_eval h (lift_pd_bindings σ)
                          (imp_qcert_op_to_imp_ejson op (map imp_qcert_expr_to_imp_ejson el)).
    Proof.
      intros.
      destruct op.
      + rewrite (imp_qcert_unary_op_to_imp_ejson_expr_correct σ u el H); reflexivity.
      + rewrite (imp_qcert_binary_op_to_imp_ejson_expr_correct σ b el H); reflexivity.
    Qed.

    Lemma imp_qcert_expr_to_imp_ejson_expr_correct (σ:pd_bindings) (exp:imp_qcert_expr) :
      unlift_result (imp_qcert_expr_eval h σ exp) =
      imp_ejson_expr_eval h (lift_pd_bindings σ)
                          (imp_qcert_expr_to_imp_ejson exp).
    Proof.
      imp_expr_cases (induction exp) Case; intros; simpl.
      - Case "ImpExprError"%string.
        reflexivity.
      - Case "ImpExprVar"%string.
        unfold unlift_result, lift_result, olift, lift.
        unfold lift_pd_bindings.
        rewrite lookup_map_codomain_unfolded; simpl.
        unfold olift, lift.
        unfold imp_qcert_data.
        destruct (lookup EquivDec.equiv_dec σ v); reflexivity.
      - Case "ImpExprConst"%string.
        reflexivity.
      - Case "ImpExprOp"%string.
        rewrite <- imp_qcert_op_to_imp_ejson_correct; [reflexivity|assumption].
      - Case "ImpExprRuntimeCall"%string.
        rewrite <- imp_qcert_runtime_call_to_imp_ejson_correct; [reflexivity|assumption].
    Qed.

    Lemma map_lift_pd_bindings_eq (σ : pd_bindings) :

      map (fun xy : string * option ejson => (fst xy, lift ejson_to_data (snd xy))) (lift_pd_bindings σ) = σ.
    Proof.
      unfold lift_pd_bindings.
      rewrite map_map.
      induction σ; [reflexivity|]; simpl.
      + destruct a; simpl.
        destruct o; simpl.
        * rewrite data_to_ejson_idempotent.
          f_equal; assumption.
        * f_equal; assumption.
    Qed.      

    Lemma imp_qcert_decls_to_imp_ejson_decls_correct
          (σ:pd_bindings)
          (el:list (string * option imp_qcert_expr)) :
      unlift_result_env
        (imp_qcert_decls_eval h σ el) =
      imp_ejson_decls_eval
        h (lift_pd_bindings σ)
        (map (fun xy : var * option imp_qcert_expr => (fst xy, lift imp_qcert_expr_to_imp_ejson (snd xy))) el).
    Proof.
      revert σ.
      induction el; intros.
      - reflexivity.
      - destruct a; destruct o.
        + specialize (imp_qcert_expr_to_imp_ejson_expr_correct σ i);
          unfold imp_qcert_decls_eval in *;
            unfold imp_ejson_decls_eval in *;
          unfold imp_qcert_expr_eval in *;
            unfold imp_ejson_expr_eval in *;
            unfold ImpEval.imp_decls_eval in *; simpl in *; intros.
          rewrite <- H; clear H.
          unfold unlift_result, lift.
          destruct (@ImpEval.imp_expr_eval (@imp_qcert_data fruntime)
                                           (@imp_qcert_op fruntime) imp_qcert_runtime_op
                                           (@imp_qcert_data_normalize fruntime h)
                                           (@imp_qcert_runtime_eval fruntime)
             (@imp_qcert_op_eval fruntime h) σ i); simpl.
          * rewrite IHel; clear IHel.
            simpl.
            induction el; simpl; try reflexivity.
          * clear IHel.
            induction el; simpl; try reflexivity.
            rewrite <- IHel; simpl. reflexivity.
        + unfold imp_qcert_decls_eval in *;
            unfold imp_ejson_decls_eval in *;
            unfold ImpEval.imp_decls_eval in *; simpl in *.
          apply IHel.
    Qed.

    Lemma imp_fold_qcert_stmt_to_imp_ejson_stmt_correct (σ:pd_bindings) sl :
      (Forall
         (fun stmt : imp_stmt =>
            forall (σ : pd_bindings),
              unlift_result_env (imp_qcert_stmt_eval h stmt σ) =
              imp_ejson_stmt_eval
                h (imp_qcert_stmt_to_imp_ejson stmt) (lift_pd_bindings σ)) sl) ->
      (unlift_result_env
        (fold_left
           (fun (c : option ImpEval.pd_rbindings) (s : ImpEval.imp_stmt) =>
              match c with
              | Some σ' => imp_qcert_stmt_eval h s σ'
              | None => None
              end) sl
           (Some
              (map
                 (fun xy : string * option ejson =>
                    (fst xy, match snd xy with
                             | Some a' => Some (ejson_to_data a')
                             | None => None
                             end)) (lift_pd_bindings σ))))
         =
         fold_left
           (fun (c : option ImpEval.pd_rbindings) (s : ImpEval.imp_stmt) =>
              match c with
              | Some σ' => imp_ejson_stmt_eval h s σ'
              | None => None
              end) (map (imp_qcert_stmt_to_imp_ejson) sl) (Some (lift_pd_bindings σ))).
    Proof.
      intros.
      revert σ.
      induction sl; simpl; intros.
      - rewrite map_lift_pd_bindings_eq; reflexivity.
      - assert (Forall
           (fun stmt : imp_stmt =>
            forall (σ : pd_bindings),
            unlift_result_env (imp_qcert_stmt_eval h stmt σ) =
            imp_ejson_stmt_eval h (imp_qcert_stmt_to_imp_ejson stmt) (lift_pd_bindings σ)) sl)
        by (rewrite Forall_forall in *; intros;
            apply H; simpl; right; assumption).
        assert (unlift_result_env (imp_qcert_stmt_eval h a σ) =
                imp_ejson_stmt_eval h (imp_qcert_stmt_to_imp_ejson a) (lift_pd_bindings σ))
        by (rewrite Forall_forall in H;
            apply (H a); simpl; left; reflexivity).
        specialize (IHsl H0); clear H0 H.
        simpl.
        rewrite <- H1; clear H1; simpl.
        unfold unlift_result_env, lift; simpl.
        rewrite map_lift_pd_bindings_eq.
        destruct (imp_qcert_stmt_eval h a σ); simpl.
        + rewrite <- IHsl.
          unfold unlift_result_env, lift; simpl.
          rewrite map_lift_pd_bindings_eq.
          reflexivity.
        + clear IHsl.
          induction sl; simpl; [reflexivity|].
          clear a a0.
          unfold imp_ejson_data in *.
          assert ((@fold_left (option (@ImpEval.pd_rbindings (@ejson (@foreign_ejson_ejson fruntime ftejson))))
              (@ImpEval.imp_stmt (@ejson (@foreign_ejson_ejson fruntime ftejson)) imp_ejson_op imp_ejson_runtime_op)
              (fun (c : option (@ImpEval.pd_rbindings (@ejson (@foreign_ejson_ejson fruntime ftejson))))
                 (s : @ImpEval.imp_stmt (@ejson (@foreign_ejson_ejson fruntime ftejson)) imp_ejson_op imp_ejson_runtime_op)
               =>
               match c return (option (@ImpEval.pd_rbindings (@ejson (@foreign_ejson_ejson fruntime ftejson)))) with
               | Some σ' => @imp_ejson_stmt_eval (@foreign_ejson_ejson fruntime ftejson) h s σ'
               | None => @None (@ImpEval.pd_rbindings (@ejson (@foreign_ejson_ejson fruntime ftejson)))
               end)
              (@map (@imp_qcert_stmt fruntime)
                 (@imp_ejson_stmt (@foreign_ejson_ejson fruntime ftejson)) imp_qcert_stmt_to_imp_ejson sl)
              (@None (list (prod string (option (@ejson (@foreign_ejson_ejson fruntime ftejson)))))))
              =
              (@fold_left (option (@ImpEval.pd_rbindings (@ejson (@foreign_ejson_ejson fruntime ftejson))))
       (@ImpEval.imp_stmt (@ejson (@foreign_ejson_ejson fruntime ftejson)) imp_ejson_op imp_ejson_runtime_op)
       (fun (c : option (@ImpEval.pd_rbindings (@ejson (@foreign_ejson_ejson fruntime ftejson))))
          (s : @ImpEval.imp_stmt (@ejson (@foreign_ejson_ejson fruntime ftejson)) imp_ejson_op imp_ejson_runtime_op) =>
        match c return (option (@ImpEval.pd_rbindings (@ejson (@foreign_ejson_ejson fruntime ftejson)))) with
        | Some σ' => @imp_ejson_stmt_eval (@foreign_ejson_ejson fruntime ftejson) h s σ'
        | None => @None (@ImpEval.pd_rbindings (@ejson (@foreign_ejson_ejson fruntime ftejson)))
        end)
       (@map (@imp_qcert_stmt fruntime) (@imp_ejson_stmt (@foreign_ejson_ejson fruntime ftejson))
          imp_qcert_stmt_to_imp_ejson sl) (@None (@ImpEval.pd_rbindings (@ejson (@foreign_ejson_ejson fruntime ftejson)))))) by reflexivity.
          rewrite <- H; clear H.
          rewrite <- IHsl; clear IHsl.
          reflexivity.
    Qed.

    Lemma imp_qcert_stmt_to_imp_ejson_stmt_correct (σ:pd_bindings) (stmt:imp_qcert_stmt) :
      unlift_result_env (imp_qcert_stmt_eval h stmt σ) =
      imp_ejson_stmt_eval h (imp_qcert_stmt_to_imp_ejson stmt) (lift_pd_bindings σ).
    Proof.
      revert σ.
      imp_stmt_cases (induction stmt) Case.
      - Case "ImpStmtBlock"%string.
        intros.
        simpl.
        specialize (imp_qcert_decls_to_imp_ejson_decls_correct σ el).
        unfold imp_qcert_decls_eval in *;
        unfold imp_ejson_decls_eval in *; simpl.
        intros Hel.
        rewrite <- Hel; clear Hel.
        unfold unlift_result_env; unfold lift.
        destruct (@ImpEval.imp_decls_eval (@imp_qcert_data fruntime)
              (@imp_qcert_op fruntime) imp_qcert_runtime_op
              (@imp_qcert_data_normalize fruntime h)
              (@imp_qcert_runtime_eval fruntime)
              (@imp_qcert_op_eval fruntime h) σ el
            ); simpl; intros.
        (* Some *)
        + rewrite ImpEval.imp_decls_erase_remove_map.
          rewrite <- (imp_fold_qcert_stmt_to_imp_ejson_stmt_correct); try assumption; clear H.
          unfold unlift_result_env; unfold lift; simpl in *.
          rewrite map_lift_pd_bindings_eq.
          induction el; simpl in *; try reflexivity.
          rewrite <- IHel; clear IHel.
          destruct a; simpl.
          destruct (@ImpEval.imp_decls_erase (@imp_qcert_data fruntime)
          (@fold_left (option (@ImpEval.pd_rbindings (@imp_qcert_data fruntime)))
             (@ImpEval.imp_stmt (@imp_qcert_data fruntime) (@imp_qcert_op fruntime) imp_qcert_runtime_op)
             (fun (c : option (@ImpEval.pd_rbindings (@imp_qcert_data fruntime)))
                (s : @ImpEval.imp_stmt (@imp_qcert_data fruntime) (@imp_qcert_op fruntime) imp_qcert_runtime_op)
              =>
              match c return (option (@ImpEval.pd_rbindings (@imp_qcert_data fruntime))) with
              | Some σ' => @imp_qcert_stmt_eval fruntime h s σ'
              | None => @None (@ImpEval.pd_rbindings (@imp_qcert_data fruntime))
              end) sl (@Some (@ImpEval.pd_rbindings (@imp_qcert_data fruntime)) p))
          (prod var
             (option (@Imp.imp_expr (@imp_qcert_data fruntime) (@imp_qcert_op fruntime) imp_qcert_runtime_op)))
          el); [|reflexivity].
          destruct p0; simpl; try reflexivity.
        + repeat rewrite ImpEval.imp_decls_erase_none; reflexivity.
      - Case "ImpStmtAssign"%string.
        intros σ.
        simpl.
        specialize (imp_qcert_expr_to_imp_ejson_expr_correct σ e).
        unfold imp_ejson_expr_eval in *.
        intros He; rewrite <- He; clear He.
        unfold unlift_result, lift.
        unfold imp_qcert_expr_eval.
        destruct (@ImpEval.imp_expr_eval (@imp_qcert_data fruntime) (@imp_qcert_op fruntime) imp_qcert_runtime_op
          (@imp_qcert_data_normalize fruntime h) (@imp_qcert_runtime_eval fruntime)
          (@imp_qcert_op_eval fruntime h) σ e);
          try reflexivity.
        unfold lift_pd_bindings.
        rewrite lookup_map_codomain_unfolded.
        unfold lift.
        unfold imp_qcert_data, foreign_runtime_data.
        match_destr.
        unfold unlift_result_env, lift.
        assert (forall (x: pd_bindings) y,  x = y -> Some x = Some y) as Hsome; try congruence.
        induction σ; try reflexivity.
        simpl.
        destruct a; simpl.
        destruct (string_dec v s); simpl; try reflexivity.
        + f_equal; f_equal.
          inversion IHσ; clear IHσ; intros.
          rewrite H0; reflexivity.
      - Case "ImpStmtFor"%string.
        intros.
        simpl.
        specialize (imp_qcert_expr_to_imp_ejson_expr_correct σ e).
        unfold imp_ejson_expr_eval in *.
        intros He; rewrite <- He; clear He.
        unfold unlift_result, lift.
        unfold imp_qcert_expr_eval.
        destruct (@ImpEval.imp_expr_eval (@imp_qcert_data fruntime) (@imp_qcert_op fruntime) imp_qcert_runtime_op
          (@imp_qcert_data_normalize fruntime h) (@imp_qcert_runtime_eval fruntime)
          (@imp_qcert_op_eval fruntime h) σ e);
          try reflexivity.
        rewrite imp_ejson_data_to_list_comm; simpl.
        destruct (imp_qcert_data_to_list i); try reflexivity; simpl; clear i.
        revert σ.
        induction l; try reflexivity; simpl; intros.
        specialize (IHstmt ((v, Some a) :: σ)); simpl in IHstmt.
        assert (@imp_ejson_stmt_eval (@foreign_ejson_ejson fruntime ftejson) h (imp_qcert_stmt_to_imp_ejson stmt)
        (@cons (prod var (option (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson))))
           (@pair var (option (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson))) v
              (@Some (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson)) (@data_to_ejson fruntime ftejson a)))
           (lift_pd_bindings σ)) =
                (@imp_ejson_stmt_eval (@foreign_ejson_ejson fruntime ftejson) h (imp_qcert_stmt_to_imp_ejson stmt)
                (@cons (prod string (option (@ejson (@foreign_ejson_ejson fruntime ftejson))))
                   (@pair string (option (@ejson (@foreign_ejson_ejson fruntime ftejson))) v
                      (@Some (@ejson (@foreign_ejson_ejson fruntime ftejson)) (@data_to_ejson fruntime ftejson a)))
                   (lift_pd_bindings σ)))) by reflexivity.
        rewrite <- H in IHstmt; clear H.
        rewrite <- IHstmt; clear IHstmt.
        assert (
            (@imp_qcert_stmt_eval fruntime h stmt
           (@cons (prod string (option (@imp_qcert_data fruntime)))
                  (@pair string (option (@imp_qcert_data fruntime)) v (@Some (@imp_qcert_data fruntime) a)) σ))
            = @imp_qcert_stmt_eval fruntime h stmt
           (@cons (prod var (option (@imp_qcert_data fruntime)))
                  (@pair var (option (@imp_qcert_data fruntime)) v (@Some (@imp_qcert_data fruntime) a)) σ)) by reflexivity.
        rewrite <- H; clear H.
        destruct (imp_qcert_stmt_eval h stmt ((v, Some a) :: σ)); try reflexivity; simpl.
        destruct p; try reflexivity; simpl.
        unfold lift_pd_bindings in IHl.
        rewrite <- IHl.
        reflexivity.
      - Case "ImpStmtForRange"%string.
        intros.
        simpl.
        specialize (imp_qcert_expr_to_imp_ejson_expr_correct σ e1).
        unfold imp_ejson_expr_eval in *.
        intros He; rewrite <- He; clear He.
        unfold unlift_result, lift.
        unfold imp_qcert_expr_eval.
        destruct (@ImpEval.imp_expr_eval (@imp_qcert_data fruntime) (@imp_qcert_op fruntime) imp_qcert_runtime_op
          (@imp_qcert_data_normalize fruntime h) (@imp_qcert_runtime_eval fruntime)
          (@imp_qcert_op_eval fruntime h) σ e1);
          try reflexivity; simpl.
        rewrite data_to_ejson_to_Z_comm;
          destruct (imp_ejson_data_to_Z (data_to_ejson i)); try reflexivity.
        specialize (imp_qcert_expr_to_imp_ejson_expr_correct σ e2).
        unfold imp_ejson_expr_eval in *.
        intros He; rewrite <- He; clear He.
        unfold unlift_result, olift, lift.
        unfold imp_qcert_expr_eval.
        destruct (@ImpEval.imp_expr_eval (@imp_qcert_data fruntime) (@imp_qcert_op fruntime) imp_qcert_runtime_op
          (@imp_qcert_data_normalize fruntime h) (@imp_qcert_runtime_eval fruntime)
          (@imp_qcert_op_eval fruntime h) σ e2);
          try reflexivity; simpl.
        rewrite data_to_ejson_to_Z_comm;
          destruct (imp_ejson_data_to_Z (data_to_ejson i0)); try reflexivity.
        generalize (ImpEval.nb_iter z z0); intros. (* XXX I think we do not care how n is built for this part *)
        revert σ z.
        induction n; try reflexivity; simpl; intros.
        specialize (IHstmt ((v, Some (imp_qcert_Z_to_data z)) :: σ)); simpl in IHstmt.
        assert ((@imp_ejson_stmt_eval (@foreign_ejson_ejson fruntime ftejson) h (imp_qcert_stmt_to_imp_ejson stmt)
                (@cons (prod string (option (@ejson (@foreign_ejson_ejson fruntime ftejson))))
                   (@pair string (option (@ejson (@foreign_ejson_ejson fruntime ftejson))) v
                      (@Some (@ejson (@foreign_ejson_ejson fruntime ftejson)) (@ejbigint (@foreign_ejson_ejson fruntime ftejson) z)))
                   (lift_pd_bindings σ)))
                  = (@imp_ejson_stmt_eval (@foreign_ejson_ejson fruntime ftejson) h (imp_qcert_stmt_to_imp_ejson stmt)
        (@cons (prod var (option (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson))))
           (@pair var (option (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson))) v
              (@Some (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson))
                 (@imp_ejson_Z_to_data (@foreign_ejson_ejson fruntime ftejson) z))) (lift_pd_bindings σ)))) by reflexivity.
        rewrite H in IHstmt; clear H.
        rewrite <- IHstmt; clear IHstmt.
        assert
          (@imp_qcert_stmt_eval
             fruntime h stmt
             (@cons (prod string (option (@imp_qcert_data fruntime)))
                    (@pair string (option (@imp_qcert_data fruntime)) v
                           (@Some (@imp_qcert_data fruntime) (@imp_qcert_Z_to_data fruntime z))) σ)
           =
           @imp_qcert_stmt_eval fruntime h stmt
           (@cons (prod var (option (@imp_qcert_data fruntime)))
              (@pair var (option (@imp_qcert_data fruntime)) v
                 (@Some (@imp_qcert_data fruntime) (@imp_qcert_Z_to_data fruntime z))) σ)) by reflexivity.
        rewrite <- H; clear H.
        destruct (imp_qcert_stmt_eval h stmt ((v, Some (imp_qcert_Z_to_data z)) :: σ)); try reflexivity.
        destruct p; try reflexivity; simpl.
        unfold lift_pd_bindings in IHn.
        rewrite IHn.
reflexivity.
      - Case "ImpStmtIf"%string.
        intros σ.
        simpl.
        specialize (imp_qcert_expr_to_imp_ejson_expr_correct σ e).
        unfold imp_ejson_expr_eval in *.
        intros Hi.
        rewrite <- Hi; clear Hi.
        unfold unlift_result.
        unfold lift.
        unfold imp_ejson_expr_eval.
        unfold imp_qcert_expr_eval.
        destruct (@ImpEval.imp_expr_eval (@imp_qcert_data fruntime) (@imp_qcert_op fruntime) imp_qcert_runtime_op
           (@imp_qcert_data_normalize fruntime h) (@imp_qcert_runtime_eval fruntime)
           (@imp_qcert_op_eval fruntime h) σ e);
          try reflexivity.
        rewrite <- data_to_bool_ejson_to_bool_correct.
        rewrite data_to_ejson_idempotent.
        match_destr.
        match_destr.
    Qed.

    Section CorrectnessForRewrite.
      Lemma imp_qcert_stmt_to_imp_ejson_stmt_combined_correct (σ:pd_bindings) (stmt:imp_qcert_stmt) :
        forall avoid,
          unlift_result_env (imp_qcert_stmt_eval h stmt σ) =
          imp_ejson_stmt_eval h (imp_qcert_stmt_to_imp_ejson_combined avoid stmt) (lift_pd_bindings σ).
      Proof.
        intros.
        rewrite imp_qcert_stmt_to_imp_ejson_combined_idem; simpl.
        rewrite imp_qcert_stmt_to_imp_ejson_stmt_correct.
        rewrite (imp_ejson_stmt_for_rewrite_correct h (lift_pd_bindings σ) _ avoid).
        reflexivity.
      Qed.

    End CorrectnessForRewrite.
    
    Lemma imp_qcert_function_to_imp_ejson_function_correct (d:data) (f:imp_qcert_function) :
      imp_qcert_function_eval h f d =
      lift ejson_to_data (imp_ejson_function_eval h (imp_qcert_function_to_imp_ejson f) (data_to_ejson d)).
    Proof.
      destruct f; simpl.
      generalize (imp_qcert_stmt_to_imp_ejson_stmt_combined_correct [(v0, None); (v, Some d)] i (v::nil)); intros.
      unfold imp_qcert_stmt_eval in H.
      unfold imp_ejson_stmt_eval in H.
      unfold imp_qcert_data in *.
      simpl in H.
      unfold lift.
      Set Printing All.
      
      assert ((@ImpEval.imp_stmt_eval (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson)) imp_ejson_op
           imp_ejson_runtime_op (@imp_ejson_data_normalize (@foreign_ejson_ejson fruntime ftejson))
           (@imp_ejson_data_to_bool (@foreign_ejson_ejson fruntime ftejson))
           (@imp_ejson_data_to_Z (@foreign_ejson_ejson fruntime ftejson))
           (@imp_ejson_data_to_list (@foreign_ejson_ejson fruntime ftejson))
           (@imp_ejson_Z_to_data (@foreign_ejson_ejson fruntime ftejson))
           (@imp_ejson_runtime_eval (@foreign_ejson_ejson fruntime ftejson) h)
           (@imp_ejson_op_eval (@foreign_ejson_ejson fruntime ftejson))
           (imp_qcert_stmt_to_imp_ejson_combined (@cons var v (@nil var)) i)
           (@cons (prod string (option (@ejson (@foreign_ejson_ejson fruntime ftejson))))
              (@pair string (option (@ejson (@foreign_ejson_ejson fruntime ftejson))) v0
                 (@None (@ejson (@foreign_ejson_ejson fruntime ftejson))))
              (@cons (prod string (option (@ejson (@foreign_ejson_ejson fruntime ftejson))))
                 (@pair string (option (@ejson (@foreign_ejson_ejson fruntime ftejson))) v
                    (@Some (@ejson (@foreign_ejson_ejson fruntime ftejson)) (@data_to_ejson fruntime ftejson d)))
                 (@nil (prod string (option (@ejson (@foreign_ejson_ejson fruntime ftejson))))))))
             = @ImpEval.imp_stmt_eval (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson)) imp_ejson_op imp_ejson_runtime_op
          (@imp_ejson_data_normalize (@foreign_ejson_ejson fruntime ftejson))
          (@imp_ejson_data_to_bool (@foreign_ejson_ejson fruntime ftejson))
          (@imp_ejson_data_to_Z (@foreign_ejson_ejson fruntime ftejson))
          (@imp_ejson_data_to_list (@foreign_ejson_ejson fruntime ftejson))
          (@imp_ejson_Z_to_data (@foreign_ejson_ejson fruntime ftejson))
          (@imp_ejson_runtime_eval (@foreign_ejson_ejson fruntime ftejson) h)
          (@imp_ejson_op_eval (@foreign_ejson_ejson fruntime ftejson))
          (imp_qcert_stmt_to_imp_ejson_combined (@cons var v (@nil var)) i)
          (@cons (prod var (option (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson))))
             (@pair var (option (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson))) v0
                (@None (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson))))
             (@cons (prod var (option (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson))))
                (@pair var (option (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson))) v
                   (@Some (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson)) (@data_to_ejson fruntime ftejson d)))
                (@nil (prod var (option (@imp_ejson_data (@foreign_ejson_ejson fruntime ftejson)))))))) by reflexivity.
      rewrite <- H0; clear H0.
      rewrite <- H; clear H.
      unfold unlift_result_env; unfold lift; simpl.
      destruct (ImpEval.imp_stmt_eval i [(v0, None); (v, Some d)]); [|reflexivity].
      unfold olift; simpl in *.
      induction p; simpl; [reflexivity|].
      destruct a; simpl.
      unfold EquivDec.equiv_dec.
      destruct (string_eqdec v0 s); simpl.
      - destruct o; [|reflexivity]; simpl in *.
        rewrite data_to_ejson_idempotent; trivial.
      - assumption.
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
      imp_ejson_eval_top h σc (imp_qcert_to_imp_ejson q).
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
