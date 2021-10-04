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
Require Import JsAst.JsNumber.
Require Import Fresh.
Require Import DataRuntime.
Require Import ImpRuntime.
Require Import ForeignDataToEJson.
Require Import ForeignToEJsonRuntime.
Require Import DataToEJson.

Section ImpDatatoImpEJson.
  Import ListNotations.

  Context {fruntime:foreign_runtime}.
  Context {fejson:foreign_ejson}.
  Context {ftejson:foreign_to_ejson}.
  Context {fejruntime:foreign_ejson_runtime}.
  Context {fejtoruntime:foreign_to_ejson_runtime}.

  Context (h:brand_relation_t). (* We need a brand relation for the Q*cert side *)

  Section Util.
    Definition mk_imp_ejson_expr_error msg : imp_ejson_expr :=
      ImpExprError msg. (* XXX Error should eval to None if we want to prove stuffs! *)
    Definition mk_imp_ejson_op op el : imp_ejson_expr := ImpExprOp op el.
    Definition mk_imp_ejson_runtime_call op el : imp_ejson_expr := ImpExprRuntimeCall op el.

    Definition mk_string s : imp_ejson_expr := ImpExprConst (cejstring s).
    Definition mk_left e : imp_ejson_expr := mk_imp_ejson_op (EJsonOpObject ["$left"%string]) [ e ].
    Definition mk_right e : imp_ejson_expr := mk_imp_ejson_op (EJsonOpObject ["$right"%string]) [ e ].

    Definition mk_array el : imp_ejson_expr := mk_imp_ejson_runtime_call EJsonRuntimeArray el.
    Definition mk_object (el:list (string * imp_ejson_expr)) : imp_ejson_expr :=
      mk_imp_ejson_op (EJsonOpObject (map fst el)) (map snd el).
    Definition mk_string_array sl : imp_ejson_expr := mk_array (map ImpExprConst (map cejstring sl)).

    Fixpoint ejson_to_expr (j:ejson) : imp_ejson_expr
      := match j with
         | ejnull => ImpExprConst cejnull
         | ejnumber f => ImpExprConst (cejnumber f)
         | ejbigint n => ImpExprConst (cejbigint n)
         | ejbool b => ImpExprConst (cejbool b)
         | ejstring s => ImpExprConst (cejstring s)
         | ejarray ls => mk_array (map ejson_to_expr ls)
         | ejobject ls => mk_object (map (fun xy => (fst xy, ejson_to_expr (snd xy))) ls)
         | ejforeign fd => ImpExprConst (cejforeign fd)
         end.

    Definition sortCriterias_to_ejson_expr (scl: list (string * SortDesc)) : imp_ejson_expr :=
      mk_array (map ejson_to_expr (map sortCriteria_to_ejson scl)).

    Definition brands_to_ejson_expr sl : imp_ejson_expr :=
      mk_string_array sl.

    Definition mk_either_expr (el:list imp_ejson_expr) : imp_ejson_expr :=
      mk_imp_ejson_runtime_call EJsonRuntimeEither el.

    Definition mk_to_left_expr (el:list imp_ejson_expr) : imp_ejson_expr :=
      mk_imp_ejson_runtime_call EJsonRuntimeToLeft el.

    Definition mk_to_right_expr (el:list imp_ejson_expr) : imp_ejson_expr :=
      mk_imp_ejson_runtime_call EJsonRuntimeToRight el.

    Lemma imp_data_model_to_list_comm d :
      lift (map ejson_to_data) (imp_ejson_model_to_list (data_to_ejson d)) =
      imp_data_model_to_list d.
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

    Lemma imp_ejson_model_to_list_comm d :
      (imp_ejson_model_to_list (data_to_ejson d)) =
      lift (map data_to_ejson) (imp_data_model_to_list d).
    Proof.
      unfold lift.
      destruct d; simpl; reflexivity.
    Qed.

    Lemma data_to_bool_ejson_to_bool_correct j:
      imp_data_model_to_bool (ejson_to_data j) = imp_ejson_model_to_bool j.
    Proof.
      unfold imp_data_model_to_bool.
      unfold imp_ejson_model_to_bool.
      destruct j; trivial.
      generalize (ejson_to_data_jobj_nbool l); intros HH1.
      match_destr.
      specialize (HH1 b); congruence.
    Qed.

    Lemma ejson_to_data_to_Z_comm j:
      imp_data_model_to_Z (ejson_to_data j) = imp_ejson_model_to_Z j.
    Proof.
      unfold imp_data_model_to_Z.
      unfold imp_ejson_model_to_Z.
      destruct j; trivial.
      case_eq (ejson_to_data (ejobject l)); intros; try reflexivity.
      generalize (ejson_to_data_object_not_nat l z); intros.
      contradiction.
    Qed.

    Lemma data_to_ejson_to_Z_comm d:
      imp_data_model_to_Z d = imp_ejson_model_to_Z (data_to_ejson d).
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

    Lemma ejson_lifted_stringbag_comm l:
      lifted_stringbag l =
      ejson_strings (map data_to_ejson l).
    Proof.
      induction l; simpl; try reflexivity.
      unfold lifted_stringbag in *; simpl.
      rewrite IHl; simpl; clear IHl.
      destruct a; reflexivity.
    Qed.

  End Util.

  Section Translation.
    
    Definition imp_data_unary_op_to_imp_ejson (op:unary_op) el : imp_ejson_expr :=
      match el with
      | [e] =>
        match op with
        | OpIdentity => e
        | OpNeg => mk_imp_ejson_op EJsonOpNot [ e ]
        | OpRec s => mk_imp_ejson_op (EJsonOpObject [key_encode s]) [ e ]
        | OpDot s => mk_imp_ejson_runtime_call EJsonRuntimeRecDot [ e; ImpExprConst (cejstring (key_encode s)) ]
        | OpRecRemove s => mk_imp_ejson_runtime_call EJsonRuntimeRecRemove [ e; mk_string (key_encode s) ]
        | OpRecProject fl =>
          mk_imp_ejson_runtime_call
            EJsonRuntimeRecProject ([ e ] ++ [ mk_string_array (map key_encode fl) ])
        | OpBag => mk_array el
        | OpSingleton => mk_imp_ejson_runtime_call EJsonRuntimeSingleton el
        | OpFlatten => mk_imp_ejson_runtime_call EJsonRuntimeFlatten el
        | OpDistinct => mk_imp_ejson_runtime_call EJsonRuntimeDistinct el
        | OpOrderBy scl =>
          mk_imp_ejson_runtime_call
            EJsonRuntimeSort (sortCriterias_to_ejson_expr scl :: e :: nil)
        | OpCount => mk_imp_ejson_runtime_call EJsonRuntimeCount el
        | OpToString => mk_imp_ejson_runtime_call EJsonRuntimeToString el
        | OpToText => mk_imp_ejson_runtime_call EJsonRuntimeToText el
        | OpLength => mk_imp_ejson_runtime_call EJsonRuntimeLength el
        | OpSubstring start len =>
          let start := ImpExprConst (cejbigint start) in
          match len with
          | Some len =>
            let args :=
                let len := ImpExprConst (cejbigint len) in
                [ e; start; len ]
            in
            mk_imp_ejson_runtime_call EJsonRuntimeSubstring args
          | None =>
            let args := [ e; start ] in
            mk_imp_ejson_runtime_call EJsonRuntimeSubstringEnd args
          end
        | OpLike pat =>
          mk_imp_ejson_runtime_call EJsonRuntimeLike [ ImpExprConst (cejstring pat); e ]
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
        | OpFloatTruncate => mk_imp_ejson_runtime_call EJsonRuntimeNatOfFloat [ e ]
        | OpFloatSum => mk_imp_ejson_runtime_call EJsonRuntimeFloatSum el
        | OpFloatMean => mk_imp_ejson_runtime_call EJsonRuntimeFloatArithMean el
        | OpFloatBagMin => mk_imp_ejson_runtime_call EJsonRuntimeFloatMin [ e ]
        | OpFloatBagMax => mk_imp_ejson_runtime_call EJsonRuntimeFloatMax [ e ]
        | OpForeignUnary fu =>
          mk_imp_ejson_runtime_call (EJsonRuntimeForeign (foreign_to_ejson_runtime_of_unary_op fu)) el
        end
      | _ => mk_imp_ejson_expr_error "wrong number of arguments"
      end.

    Definition imp_data_binary_op_to_imp_ejson (op:binary_op) el : imp_ejson_expr :=
      match el with
      | [e1; e2] =>
        match op with
        | OpEqual => mk_imp_ejson_runtime_call EJsonRuntimeEqual el
        | OpRecConcat => mk_imp_ejson_runtime_call EJsonRuntimeRecConcat el
        | OpRecMerge => mk_imp_ejson_runtime_call EJsonRuntimeRecMerge el
        | OpAnd => mk_imp_ejson_op EJsonOpAnd el
        | OpOr => mk_imp_ejson_op EJsonOpOr el
        | OpLt => mk_imp_ejson_runtime_call EJsonRuntimeNatLt el
        | OpLe => mk_imp_ejson_runtime_call EJsonRuntimeNatLe el
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
          mk_imp_ejson_runtime_call (EJsonRuntimeForeign (foreign_to_ejson_runtime_of_binary_op fb)) el
        end
      | _ => mk_imp_ejson_expr_error "imp_data_binary_op_to_imp_ejson: wrong number of arguments"
      end.

    Definition imp_data_op_to_imp_ejson (op:imp_data_op) el : imp_ejson_expr :=
      match op with
      | DataOpUnary op => imp_data_unary_op_to_imp_ejson op el
      | DataOpBinary op => imp_data_binary_op_to_imp_ejson op el
      end.

    Definition imp_data_runtime_call_to_imp_ejson
               (op:imp_data_runtime_op)
               (el:list imp_ejson_expr) : imp_ejson_expr :=
      match op with
      | DataRuntimeGroupby s ls =>
        mk_imp_ejson_runtime_call
          EJsonRuntimeGroupBy
          ((ImpExprConst (cejstring (key_encode s)))
             :: (mk_string_array (map key_encode ls))
             :: el)
      | DataRuntimeEither => mk_either_expr el
      | DataRuntimeToLeft => mk_to_left_expr el
      | DataRuntimeToRight => mk_to_right_expr el
      end.

    Fixpoint imp_data_expr_to_imp_ejson (exp: imp_data_expr) : imp_ejson_expr :=
      match exp with
      | ImpExprError msg => ImpExprError msg
      | ImpExprVar v => ImpExprVar v
      | ImpExprConst d => ejson_to_expr (data_to_ejson (normalize_data h d))
      | ImpExprOp op el => imp_data_op_to_imp_ejson op (map imp_data_expr_to_imp_ejson el)
      | ImpExprRuntimeCall op el => imp_data_runtime_call_to_imp_ejson op (map imp_data_expr_to_imp_ejson el)
      end.

    Fixpoint imp_data_stmt_to_imp_ejson (stmt: imp_data_stmt): imp_ejson_stmt :=
      match stmt with
      | ImpStmtBlock lv ls =>
        ImpStmtBlock
          (map (fun xy => (fst xy, lift imp_data_expr_to_imp_ejson (snd xy))) lv)
          (map imp_data_stmt_to_imp_ejson ls)
      | ImpStmtAssign v e =>
        ImpStmtAssign v (imp_data_expr_to_imp_ejson e)
      | ImpStmtFor v e s =>
        ImpStmtFor v
                   (imp_data_expr_to_imp_ejson e)
                   (imp_data_stmt_to_imp_ejson s)
      | ImpStmtForRange v e1 e2 s =>
        ImpStmtForRange v
                        (imp_data_expr_to_imp_ejson e1)
                        (imp_data_expr_to_imp_ejson e2)
                        (imp_data_stmt_to_imp_ejson s)
      | ImpStmtIf e s1 s2 =>
        ImpStmtIf (imp_data_expr_to_imp_ejson e)
                  (imp_data_stmt_to_imp_ejson s1)
                  (imp_data_stmt_to_imp_ejson s2)
      end.

    Definition imp_data_function_to_imp_ejson (f:imp_data_function) : imp_ejson_function :=
      match f with
      | ImpFun v s ret => ImpFun v (imp_data_stmt_to_imp_ejson s) ret
      end.

    Definition imp_data_to_imp_ejson (i:imp_data) : imp_ejson :=
      match i with
      | ImpLib l =>
        ImpLib
          (List.map
             (fun (decl: string * imp_data_function) =>
                let (name, def) := decl in (name, imp_data_function_to_imp_ejson def))
             l)
      end.
  End Translation.

  Section Correctness.
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

    Lemma eval_ejson_to_expr_string_array_correct σ l:
      olift (imp_ejson_runtime_eval h EJsonRuntimeArray)
            (lift_map (fun x : option imp_ejson_model => x)
                      (map (fun x : imp_ejson_expr => imp_ejson_expr_eval h (lift_pd_bindings σ) x)
                           (map ImpExprConst (map cejstring l))))
      = Some (ejarray (map ejstring l)).
    Proof.
      rewrite map_map; rewrite map_map; simpl in *.
      unfold olift; rewrite lift_map_map_fusion.
      induction l; simpl; [reflexivity|].
      unfold lift; simpl in *.
      destruct (@lift_map
                  string (@imp_ejson_model fejson)
                  (fun x : string => @Some (@imp_ejson_model fejson) (@ejstring fejson x)) l);
        simpl; try congruence.
      inversion IHl; reflexivity.
    Qed.

    Lemma eval_ejson_to_expr_sort_criteria_correct σ a:
      imp_ejson_expr_eval h (lift_pd_bindings σ) (ejson_to_expr (sortCriteria_to_ejson a))
      = Some (sortCriteria_to_ejson a).
    Proof.
      destruct a; simpl.
      destruct s0; reflexivity.
    Qed.

    Lemma eval_ejson_to_expr_sort_criterias_correct σ s:
      olift (imp_ejson_runtime_eval h EJsonRuntimeArray)
            (lift_map (fun x : option imp_ejson_model => x)
                      (map (fun x : imp_ejson_expr => imp_ejson_expr_eval h (lift_pd_bindings σ) x)
                           (map ejson_to_expr (map sortCriteria_to_ejson s))))
      = Some (ejarray (map sortCriteria_to_ejson s)).
    Proof.
      rewrite map_map.
      rewrite map_map.
      simpl in *.
      unfold olift.
      rewrite lift_map_map_fusion.
      induction s; simpl; [reflexivity|].
      unfold lift; simpl in *.
      destruct (@lift_map (prod string SortDesc) (@imp_ejson_model fejson)
              (fun x : prod string SortDesc =>
               @imp_ejson_expr_eval fejson fejruntime h (@lift_pd_bindings fruntime fejson ftejson σ)
                 (ejson_to_expr (@sortCriteria_to_ejson fejson x))) s);
        simpl; try congruence.
      rewrite eval_ejson_to_expr_sort_criteria_correct; simpl.
      inversion IHs; reflexivity.
    Qed.

    Lemma imp_data_unary_op_to_imp_ejson_expr_correct
           (σ:pd_bindings) (u:unary_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           unlift_result (imp_data_expr_eval h σ exp) =
           imp_ejson_expr_eval
             h (lift_pd_bindings σ) (imp_data_expr_to_imp_ejson exp)) el -> 
      unlift_result (imp_data_expr_eval h σ (ImpExprOp (DataOpUnary u) el)) =
      imp_ejson_expr_eval h
                          (lift_pd_bindings σ)
                          (imp_data_unary_op_to_imp_ejson u (map imp_data_expr_to_imp_ejson el)).
    Proof.
      Opaque ejson_to_data.
      intros.
      (* elim no params *)
      destruct el; [reflexivity|].
      (* elim two or more params *)
      destruct el; simpl;
        [|destruct (imp_data_expr_eval h σ i); [|reflexivity];
          destruct (imp_data_expr_eval h σ i0); [|reflexivity];
          unfold lift, olift;
          case_eq
            (lift_map (fun x : option imp_data_model => x)
                      (map (fun x : imp_data_expr => imp_data_expr_eval h σ x) el)); intros;
          unfold imp_data_model, ImpEval.imp_expr, imp_data_expr, imp_data_model, foreign_runtime_data in *;
          rewrite H0; reflexivity].
      (* just one param *)
      apply Forall_inv in H.
      unary_op_cases (destruct u) Case; unfold lift_result, lift, olift; simpl;
        try (rewrite <- H; clear H;
             destruct (imp_data_expr_eval h σ i);
             try reflexivity; simpl; unfold unlift_result, lift; simpl).
      - Case "OpNeg"%string.
        destruct d; try reflexivity.
      - Case "OpDot"%string.
        apply edot_key_encode_comm.
      - Case "OpRecRemove"%string.
        apply rremove_key_encode_comm.
      - Case "OpRecProject"%string.
        rewrite eval_ejson_to_expr_string_array_correct.
        apply rproject_key_encode_comm.
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
        rewrite eval_ejson_to_expr_sort_criterias_correct; simpl.
        apply order_by_to_ejson_correct.
      - Case "OpOrderBy"%string. (* XXX None case *)
        rewrite eval_ejson_to_expr_sort_criterias_correct; simpl.
        reflexivity.
      - Case "OpCount"%string.
        destruct d; simpl; try reflexivity.
        destruct l; simpl in *; try reflexivity.
        unfold bcount.
        rewrite map_length.
        reflexivity.
      - Case "OpToString"%string.
        rewrite <- foreign_to_ejson_runtime_tostring_correct; reflexivity.
      - Case "OpToText"%string.
        rewrite <- foreign_to_ejson_runtime_totext_correct; reflexivity.
      - Case "OpLength"%string.
        destruct d; reflexivity.
      - Case "OpSubstring"%string.
        destruct o; simpl.
        + rewrite <- H. destruct (imp_data_expr_eval h σ i); try reflexivity. simpl.
          destruct d; reflexivity.
        + rewrite <- H. destruct (imp_data_expr_eval h σ i); try reflexivity. simpl.
          destruct d; reflexivity.
      - Case "OpLike"%string.
        destruct d; simpl; trivial.
      - Case "OpBrand"%string.
        rewrite eval_ejson_to_expr_string_array_correct; simpl.
        rewrite of_string_list_map_ejstring; simpl.
        reflexivity.
      - Case "OpBrand"%string. (* XXX None case *)
        rewrite eval_ejson_to_expr_string_array_correct; simpl.
        reflexivity.
      - Case "OpUnbrand"%string.
        case_eq d; intros; simpl; try reflexivity; try (destruct d0; reflexivity).
        + destruct l; simpl; try reflexivity;
            destruct p; simpl; try reflexivity;
          destruct d0; try reflexivity;
          rewrite_string_dec_from_neq (key_encode_not_class s);
          destruct l0; simpl; try reflexivity;
          destruct l; simpl; try reflexivity;
          destruct l; simpl; try reflexivity.
        + rewrite ejson_brands_map_ejstring; reflexivity.
      - Case "OpCast"%string.
        rewrite eval_ejson_to_expr_string_array_correct; simpl.
        rewrite ejson_brands_map_ejstring.
        case_eq d; intros; simpl; try reflexivity; try (destruct d0; reflexivity).
        + destruct l; simpl; try reflexivity;
            destruct p; simpl; try reflexivity;
          destruct d0; try reflexivity;
          rewrite_string_dec_from_neq (key_encode_not_class s);
          destruct l0; simpl; try reflexivity;
          destruct l; simpl; try reflexivity;
          destruct l; simpl; try reflexivity.
        + rewrite ejson_brands_map_ejstring.
          destruct (sub_brands_dec h b0 b); reflexivity.
      - Case "OpCast"%string. (* XXX None case *)
        rewrite eval_ejson_to_expr_string_array_correct; simpl.
        reflexivity.
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
        destruct d; try reflexivity; simpl.
        unfold lifted_fmin, lift; simpl.
        rewrite <- ejson_lifted_fbag_comm.
        destruct (lifted_fbag l); try reflexivity.
      - Case "OpFloatBagMax"%string.
        destruct d; try reflexivity; simpl.
        unfold lifted_fmax, lift; simpl.
        rewrite <- ejson_lifted_fbag_comm.
        destruct (lifted_fbag l); try reflexivity.
      - Case "OpForeignUnary"%string.
        rewrite <- (foreign_to_ejson_runtime_of_unary_op_correct fu h).
        reflexivity.
        Transparent ejson_to_data.
    Qed.

    Lemma imp_data_binary_op_to_imp_ejson_expr_correct
           (σ:pd_bindings) (b:binary_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           unlift_result (imp_data_expr_eval h σ exp) =
           imp_ejson_expr_eval
             h
             (lift_pd_bindings σ) (imp_data_expr_to_imp_ejson exp)) el -> 
      unlift_result (imp_data_expr_eval h σ (ImpExprOp (DataOpBinary b) el)) =
      imp_ejson_expr_eval h (lift_pd_bindings σ)
                          (imp_data_binary_op_to_imp_ejson b (map imp_data_expr_to_imp_ejson el)).
    Proof.
      Opaque ejson_to_data.
      intros.
      (* elim no params *)
      destruct el; [reflexivity|].
      (* elim one params *)
      destruct el; [simpl; destruct (imp_data_expr_eval h σ i); reflexivity|].
      (* elim two or more params *)
      destruct el; simpl;
        [|destruct (imp_data_expr_eval h σ i); [|reflexivity];
          destruct (imp_data_expr_eval h σ i0); [|reflexivity];
          destruct (imp_data_expr_eval h σ i1); [|reflexivity];
          unfold lift, olift;
          case_eq
            (lift_map (fun x : option imp_data_model => x)
                      (map (fun x : imp_data_expr => imp_data_expr_eval h σ x) el)); intros;
          unfold imp_data_model, ImpEval.imp_expr, imp_data_expr, imp_data_model, foreign_runtime_data in *;
          rewrite H0; reflexivity].
      (* just two param *)
      inversion H; clear H; intros; subst; apply Forall_inv in H3.
      binary_op_cases (destruct b) Case; unfold lift_result, lift, olift; simpl;
        (* try (destruct n; simpl); *)
        try (rewrite <- H2; clear H2;
             destruct (imp_data_expr_eval h σ i);
             try reflexivity; simpl; unfold unlift_result, lift; simpl;
             try (destruct n);
             rewrite <- H3; clear H3;
             destruct (imp_data_expr_eval h σ i0);
             try reflexivity; simpl; unfold unlift_result, lift; simpl).
      - Case "OpEqual"%string.
        destruct (data_eq_dec d d0);
          destruct (ejson_eq_dec (data_to_ejson d) (data_to_ejson d0));
          try reflexivity; subst.
        + congruence.
        + apply data_to_ejson_inj in e; congruence.
      - Case "OpRecConcat"%string.
        apply rconcat_key_encode_comm.
      - Case "OpRecMerge"%string.
        apply rmerge_key_encode_comm.
      - Case "OpAnd"%string.
        destruct d; destruct d0; reflexivity.
      - Case "OpOr"%string.
        destruct d; destruct d0; reflexivity.
      - Case "OpLt"%string.
        destruct d; destruct d0; reflexivity.
      - Case "OpLe"%string.
        destruct d; destruct d0; reflexivity.
      - Case "OpBagUnion"%string.
        unfold rondcoll2, ondcoll2, lift; simpl.
        destruct d; destruct d0; simpl; try reflexivity.
        f_equal; f_equal.
        apply bunion_ejson_to_data_comm.
      - Case "OpBagDiff"%string.
        unfold rondcoll2, ondcoll2, lift; simpl.
        destruct d; destruct d0; simpl; try reflexivity.
        f_equal; f_equal.
        apply bminus_ejson_to_data_comm.
      - Case "OpBagMin"%string.
        unfold rondcoll2, ondcoll2, lift; simpl.
        destruct d; destruct d0; simpl; try reflexivity.
        f_equal; f_equal.
        apply bmin_ejson_to_data_comm.
      - Case "OpBagMax"%string.
        unfold rondcoll2, ondcoll2, lift; simpl.
        destruct d; destruct d0; simpl; try reflexivity.
        f_equal; f_equal.
        apply bmax_ejson_to_data_comm.
      - Case "OpBagNth"%string.
        destruct d; destruct d0; simpl; try reflexivity.
        destruct (fst (ZToSignedNat z)); try reflexivity.
        rewrite <- nth_error_to_ejson_comm; simpl.
        destruct (nth_error l (snd (ZToSignedNat z))); reflexivity.
      - Case "OpContains"%string.
        unfold ondcoll, lift; simpl.
        destruct d0; simpl; try reflexivity.
        destruct (in_dec data_eq_dec d l); destruct (in_dec ejson_eq_dec (data_to_ejson d) (map data_to_ejson l));
          try reflexivity; simpl.
        + rewrite <- in_data_to_ejson_comm in i1; congruence.
        + rewrite in_data_to_ejson_comm in i1; congruence.
      - Case "OpStringConcat"%string.
        destruct d; destruct d0; reflexivity.
      - Case "OpStringJoin"%string.
        destruct d; destruct d0; try reflexivity.
        unfold lifted_join, lift; simpl.
        rewrite <- ejson_lifted_stringbag_comm.
        destruct (lifted_stringbag l); reflexivity.
      - Case "OpNatBinary"%string.
        destruct n;
          simpl;
          rewrite <- H2; clear H2;
            destruct (imp_data_expr_eval h σ i);
            try reflexivity; simpl; unfold unlift_result, lift; simpl;
              try (destruct n);
              rewrite <- H3; clear H3;
                destruct (imp_data_expr_eval h σ i0);
                try reflexivity; simpl; unfold unlift_result, lift; simpl;
                  destruct d; destruct d0; try reflexivity.
      - Case "OpFloatBinary"%string.
        destruct f;
          simpl;
          rewrite <- H2; clear H2;
            destruct (imp_data_expr_eval h σ i);
            try reflexivity; simpl; unfold unlift_result, lift; simpl;
              try (destruct n);
              rewrite <- H3; clear H3;
                destruct (imp_data_expr_eval h σ i0);
                try reflexivity; simpl; unfold unlift_result, lift; simpl;
                  destruct d; destruct d0; try reflexivity.
      - Case "OpFloatCompare"%string.
        destruct f;
          simpl;
          rewrite <- H2; clear H2;
            destruct (imp_data_expr_eval h σ i);
            try reflexivity; simpl; unfold unlift_result, lift; simpl;
              try (destruct n);
              rewrite <- H3; clear H3;
                destruct (imp_data_expr_eval h σ i0);
                try reflexivity; simpl; unfold unlift_result, lift; simpl;
                  destruct d; destruct d0; try reflexivity.
      - Case "OpForeignBinary"%string.
        rewrite <- (foreign_to_ejson_runtime_of_binary_op_correct fb h).
        reflexivity.
      Transparent ejson_to_data.
    Qed.

    (* XXX To generalize, move somewhere esle *)
    Lemma Forall_lift_map σ el :
      Forall
        (fun exp : imp_expr =>
           unlift_result (imp_data_expr_eval h σ exp) =
           imp_ejson_expr_eval h (lift_pd_bindings σ) (imp_data_expr_to_imp_ejson exp)) el ->
      lift (map data_to_ejson) (lift_map (fun x : ImpEval.imp_expr => imp_data_expr_eval h σ x) el)
      =
      (lift_map
         (fun x : imp_data_expr =>
            imp_ejson_expr_eval h (lift_pd_bindings σ) (imp_data_expr_to_imp_ejson x)) el).
    Proof.
      intros.
      induction el; [reflexivity|]; simpl.
      inversion H; subst; clear H.
      rewrite <- H2; clear H2.
      specialize (IHel H3); clear H3.
      rewrite <- IHel.
      unfold lift; simpl.
      destruct (imp_data_expr_eval h σ a); try reflexivity.
      destruct (lift_map (fun x : ImpEval.imp_expr => imp_data_expr_eval h σ x) el); reflexivity.
    Qed.

    Lemma data_to_ejson_drec_not_left l jl:
      data_to_ejson (drec l) <> ejobject [("$left"%string, jl)].
    Proof.
      unfold not; intros.
      destruct l; simpl in *; try congruence.
      destruct p; simpl in *; try congruence.
      inversion H; subst.
      rewrite H1 in *.
      specialize (key_encode_not_left s); intros.
      congruence.
    Qed.

    Lemma data_to_ejson_drec_not_right l jl:
      data_to_ejson (drec l) <> ejobject [("$right"%string, jl)].
    Proof.
      unfold not; intros.
      destruct l; simpl in *; try congruence.
      destruct p; simpl in *; try congruence.
      inversion H; subst.
      rewrite H1 in *.
      specialize (key_encode_not_right s); intros.
      congruence.
    Qed.

    Lemma imp_data_runtime_call_to_imp_ejson_correct
          (σ:pd_bindings) (rt:imp_data_runtime_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           unlift_result (imp_data_expr_eval h σ exp) =
           imp_ejson_expr_eval h (lift_pd_bindings σ) (imp_data_expr_to_imp_ejson exp)) el -> 
      unlift_result (imp_data_expr_eval h σ (ImpExprRuntimeCall rt el)) =
      imp_ejson_expr_eval h (lift_pd_bindings σ)
                          (imp_data_runtime_call_to_imp_ejson rt (map imp_data_expr_to_imp_ejson el)).
    Proof.
      Opaque ejson_to_data. {
        intros.
        imp_data_runtime_op_cases(destruct rt) Case; simpl in *;
        repeat rewrite lift_map_map_fusion;
        rewrite <- (Forall_lift_map _ _ H); clear H;
          unfold unlift_result, olift, lift;
          assert (@lift_map (@ImpEval.imp_expr (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op)
          (@imp_data_model fruntime)
          (fun x : @ImpEval.imp_expr (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op =>
           @imp_data_expr_eval fruntime h σ x) el
                  =
                  @lift_map
              (@ImpEval.imp_expr (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op)
              (@data (@foreign_runtime_data fruntime))
              (fun
                 x : @ImpEval.imp_expr (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op
               => @imp_data_expr_eval fruntime h σ x) el) by reflexivity;
          rewrite H; clear H;
          destruct ((lift_map (fun x : ImpEval.imp_expr => imp_data_expr_eval h σ x) el));
            try reflexivity; simpl.
        - Case "DataRuntimeGroupby"%string.
          rewrite lift_map_map.
          destruct l0; try reflexivity; simpl.
          destruct l0; [|destruct d; reflexivity]; simpl.
          destruct d; try reflexivity; simpl.
          rewrite of_string_list_map_ejstring_f.
          unfold lift.
          apply group_by_data_to_ejson_correct.
        - Case "DataRuntimeGroupby"%string. (* XXX None case *)
          rewrite lift_map_map; reflexivity.
        - Case "DataRuntimeEither"%string.
          destruct l; try reflexivity; simpl.
          destruct l; simpl in *; [|destruct d; congruence].
          case_eq d; intros;
            try (destruct d; simpl in *; congruence).
          case_eq (data_to_ejson (drec l)); intros; try reflexivity.
          destruct l0; simpl; try reflexivity.
          destruct p; simpl; try reflexivity.
          destruct l0; simpl; try reflexivity; [|repeat match_destr].
          specialize (data_to_ejson_drec_not_left l e);
            specialize (data_to_ejson_drec_not_right l e); intros.
          rewrite H0 in *; clear H0.
          case_eq (string_dec s "$right"%string); intros; subst; try congruence.
          case_eq (string_dec s "$left"%string); intros; subst; try congruence.
          rewrite match_neither_left_nor_right; try reflexivity; assumption.
        - Case "DataRuntimeLeft"%string.
          destruct l; try reflexivity; simpl.
          destruct l; simpl in *; [|destruct d; congruence].
          case_eq d; intros;
            try (destruct d; simpl in *; congruence).
          case_eq (data_to_ejson (drec l)); intros; try reflexivity.
          destruct l0; simpl; try reflexivity.
          destruct p; simpl; try reflexivity.
          destruct l0; simpl; try reflexivity; [|repeat match_destr].
          specialize (data_to_ejson_drec_not_left l e); intros.
          rewrite H0 in *; clear H0.
          case_eq (string_dec s "$left"%string); intros; subst; try congruence.
          rewrite match_not_left; try reflexivity; assumption.
        - Case "DataRuntimeRight"%string.
          destruct l; try reflexivity; simpl.
          destruct l; simpl in *; [|destruct d; congruence].
          case_eq d; intros;
            try (destruct d; simpl in *; congruence).
          case_eq (data_to_ejson (drec l)); intros; try reflexivity.
          destruct l0; simpl; try reflexivity.
          destruct p; simpl; try reflexivity.
          destruct l0; simpl; try reflexivity; [|repeat match_destr].
          specialize (data_to_ejson_drec_not_right l e); intros.
          rewrite H0 in *; clear H0.
          case_eq (string_dec s "$right"%string); intros; subst; try congruence.
          rewrite match_not_right; try reflexivity; assumption.
      }
      Transparent ejson_to_data.
    Qed.

    Lemma imp_data_op_to_imp_ejson_correct
          (σ:pd_bindings) (op:imp_data_op) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           unlift_result (imp_data_expr_eval h σ exp) =
           imp_ejson_expr_eval h (lift_pd_bindings σ) (imp_data_expr_to_imp_ejson exp)) el -> 
      unlift_result (imp_data_expr_eval h σ (ImpExprOp op el)) =
      imp_ejson_expr_eval h (lift_pd_bindings σ)
                          (imp_data_op_to_imp_ejson op (map imp_data_expr_to_imp_ejson el)).
    Proof.
      intros.
      destruct op.
      + rewrite (imp_data_unary_op_to_imp_ejson_expr_correct σ u el H); reflexivity.
      + rewrite (imp_data_binary_op_to_imp_ejson_expr_correct σ b el H); reflexivity.
    Qed.

    Lemma ejson_to_expr_string_array_to_constant (l:list string) :
      map ejson_to_expr (map ejstring l)
      = map ImpExprConst (map cejstring l).
    Proof.
      induction l; [reflexivity|]; simpl.
      rewrite IHl; reflexivity.
    Qed.

    Lemma zip_both_map {A} {B} (l:list (A * B)) :
      zip (map fst l) (map snd l) = Some l.
    Proof.
      induction l; [reflexivity|].
      simpl.
      rewrite IHl; simpl.
      destruct a; reflexivity.
    Qed.
      
    Lemma eval_map_snd_ejson_constant_to_expr_correct σ r:
      Forall
        (fun ab : string * ejson =>
           imp_ejson_expr_eval h (lift_pd_bindings σ) (ejson_to_expr (snd ab)) = Some (snd ab)) r ->
      lift_map
        (fun x : string * ejson => imp_ejson_expr_eval h (lift_pd_bindings σ) (ejson_to_expr (snd x))) r
      =
      Some (map snd r).
    Proof.
      intros.
      induction r; [reflexivity|].
      inversion H; intros; subst; clear H.
      specialize (IHr H3); clear H3.
      simpl.
      rewrite H2.
      rewrite IHr.
      reflexivity.
    Qed.

    Lemma eval_ejson_constant_to_expr_correct σ j:
      imp_ejson_expr_eval h (lift_pd_bindings σ) (ejson_to_expr j)
      = Some j.
    Proof.
      induction j; simpl in *; try reflexivity.
      - repeat rewrite map_map.
        rewrite lift_map_map_fusion; simpl.
        unfold olift; simpl.
        induction c; simpl in *; [reflexivity|].
        inversion H; intros; clear H; subst.
        specialize (IHc H3); clear H3.
        destruct (lift_map (fun x : ejson => imp_ejson_expr_eval h (lift_pd_bindings σ) (ejson_to_expr x)) c)
        ; try congruence.
        rewrite H2; clear H2.
        inversion IHc; subst; reflexivity.
      - repeat rewrite map_map; simpl.
        unfold olift.
        rewrite lift_map_map_fusion.
        simpl.
        rewrite (eval_map_snd_ejson_constant_to_expr_correct _ _ H); clear H.
        unfold lift; simpl.
        rewrite zip_both_map; reflexivity.
    Qed.

    Lemma imp_data_expr_to_imp_ejson_expr_correct (σ:pd_bindings) (exp:imp_data_expr) :
      unlift_result (imp_data_expr_eval h σ exp) =
      imp_ejson_expr_eval h (lift_pd_bindings σ)
                          (imp_data_expr_to_imp_ejson exp).
    Proof.
      imp_expr_cases (induction exp) Case; intros; simpl.
      - Case "ImpExprError"%string.
        reflexivity.
      - Case "ImpExprVar"%string.
        unfold unlift_result, lift_result, olift, lift.
        unfold lift_pd_bindings.
        rewrite lookup_map_codomain_unfolded; simpl.
        unfold olift, lift.
        unfold imp_data_model.
        destruct (lookup EquivDec.equiv_dec σ v); reflexivity.
      - Case "ImpExprConst"%string.
        rewrite eval_ejson_constant_to_expr_correct.
        reflexivity.
      - Case "ImpExprOp"%string.
        rewrite <- imp_data_op_to_imp_ejson_correct; [reflexivity|assumption].
      - Case "ImpExprRuntimeCall"%string.
        rewrite <- imp_data_runtime_call_to_imp_ejson_correct; [reflexivity|assumption].
    Qed.

    Lemma map_lift_pd_bindings_unfold_eq (σ : pd_bindings) :
      map (fun xy : string * option ejson => (fst xy, lift ejson_to_data (snd xy)))
          (map (fun xy : string * option data => (fst xy, lift data_to_ejson (snd xy))) σ) = σ.
    Proof.
      rewrite map_map.
      induction σ; [reflexivity|]; simpl.
      + destruct a; simpl.
        destruct o; simpl.
        * rewrite data_to_ejson_idempotent.
          f_equal; assumption.
        * f_equal; assumption.
    Qed.

    Lemma map_lift_pd_bindings_eq (σ : pd_bindings) :
      map (fun xy : string * option ejson => (fst xy, lift ejson_to_data (snd xy))) (lift_pd_bindings σ) = σ.
    Proof.
      apply map_lift_pd_bindings_unfold_eq.
    Qed.      

    Lemma imp_data_decls_to_imp_ejson_decls_correct
          (σ:pd_bindings)
          (el:list (string * option imp_data_expr)) :
      unlift_result_env
        (imp_data_decls_eval h σ el) =
      imp_ejson_decls_eval
        h (lift_pd_bindings σ)
        (map (fun xy : var * option imp_data_expr => (fst xy, lift imp_data_expr_to_imp_ejson (snd xy))) el).
    Proof.
      revert σ.
      induction el; intros.
      - reflexivity.
      - destruct a; destruct o.
        + specialize (imp_data_expr_to_imp_ejson_expr_correct σ i);
          unfold imp_data_decls_eval in *;
            unfold imp_ejson_decls_eval in *;
          unfold imp_data_expr_eval in *;
            unfold imp_ejson_expr_eval in *;
            unfold ImpEval.imp_decls_eval in *; simpl in *; intros.
          rewrite <- H; clear H.
          unfold unlift_result, lift.
          destruct (@ImpEval.imp_expr_eval (@imp_data_model fruntime)
                                           (@imp_data_constant fruntime)
                                           (@imp_data_op fruntime) imp_data_runtime_op
                                           (@imp_data_model_normalize fruntime h)
                                           (@imp_data_runtime_eval fruntime)
             (@imp_data_op_eval fruntime h) σ i); simpl.
          * rewrite IHel; clear IHel.
            simpl.
            induction el; simpl; try reflexivity.
          * clear IHel.
            induction el; simpl; try reflexivity.
            rewrite <- IHel; simpl. reflexivity.
        + unfold imp_data_decls_eval in *;
            unfold imp_ejson_decls_eval in *;
            unfold ImpEval.imp_decls_eval in *; simpl in *.
          apply IHel.
    Qed.

    Lemma imp_fold_qcert_stmt_to_imp_ejson_stmt_correct (σ:pd_bindings) sl :
      (Forall
         (fun stmt : imp_stmt =>
            forall (σ : pd_bindings),
              unlift_result_env (imp_data_stmt_eval h stmt σ) =
              imp_ejson_stmt_eval
                h (imp_data_stmt_to_imp_ejson stmt) (lift_pd_bindings σ)) sl) ->
      (unlift_result_env
        (fold_left
           (fun (c : option ImpEval.pd_rbindings) (s : ImpEval.imp_stmt) =>
              match c with
              | Some σ' => imp_data_stmt_eval h s σ'
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
              end) (map (imp_data_stmt_to_imp_ejson) sl) (Some (lift_pd_bindings σ))).
    Proof.
      intros.
      revert σ.
      induction sl; simpl; intros.
      - rewrite map_lift_pd_bindings_eq; reflexivity.
      - assert (Forall
           (fun stmt : imp_stmt =>
            forall (σ : pd_bindings),
            unlift_result_env (imp_data_stmt_eval h stmt σ) =
            imp_ejson_stmt_eval h (imp_data_stmt_to_imp_ejson stmt) (lift_pd_bindings σ)) sl)
        by (rewrite Forall_forall in *; intros;
            apply H; simpl; right; assumption).
        assert (unlift_result_env (imp_data_stmt_eval h a σ) =
                imp_ejson_stmt_eval h (imp_data_stmt_to_imp_ejson a) (lift_pd_bindings σ))
        by (rewrite Forall_forall in H;
            apply (H a); simpl; left; reflexivity).
        specialize (IHsl H0); clear H0 H.
        simpl.
        rewrite <- H1; clear H1; simpl.
        unfold unlift_result_env, lift; simpl.
        rewrite map_lift_pd_bindings_eq.
        destruct (imp_data_stmt_eval h a σ); simpl.
        + unfold lift_pd_bindings in IHsl.
          rewrite <- IHsl.
          rewrite map_lift_pd_bindings_unfold_eq.
          reflexivity.
        + clear IHsl.
          induction sl; simpl; [reflexivity|].
          clear a a0.
          unfold imp_ejson_constant in *.
          Set Printing All.
          assert ((@fold_left (option (@ImpEval.pd_rbindings (@ejson fejson)))
              (@ImpEval.imp_stmt (@cejson fejson) imp_ejson_op (@imp_ejson_runtime_op fejson fejruntime))
              (fun (c : option (@ImpEval.pd_rbindings (@ejson fejson)))
                 (s : @ImpEval.imp_stmt (@cejson fejson) imp_ejson_op (@imp_ejson_runtime_op fejson fejruntime))
               =>
               match c return (option (@ImpEval.pd_rbindings (@ejson fejson))) with
               | Some σ' => @imp_ejson_stmt_eval fejson fejruntime h s σ'
               | None => @None (@ImpEval.pd_rbindings (@ejson fejson))
               end)
              (@map (@imp_data_stmt fruntime) (@imp_ejson_stmt fejson fejruntime) imp_data_stmt_to_imp_ejson sl)
              (@None (list (prod string (option (@ejson fejson))))))
              =
              (@fold_left (option (@ImpEval.pd_rbindings (@ejson fejson)))
       (@ImpEval.imp_stmt (@cejson fejson) imp_ejson_op (@imp_ejson_runtime_op fejson fejruntime))
       (fun (c : option (@ImpEval.pd_rbindings (@ejson fejson)))
          (s : @ImpEval.imp_stmt (@cejson fejson) imp_ejson_op (@imp_ejson_runtime_op fejson fejruntime)) =>
        match c return (option (@ImpEval.pd_rbindings (@ejson fejson))) with
        | Some σ' => @imp_ejson_stmt_eval fejson fejruntime h s σ'
        | None => @None (@ImpEval.pd_rbindings (@ejson fejson))
        end) (@map (@imp_data_stmt fruntime) (@imp_ejson_stmt fejson fejruntime) imp_data_stmt_to_imp_ejson sl)
       (@None (@ImpEval.pd_rbindings (@ejson fejson))))
) by reflexivity.
          rewrite <- H; clear H.
          rewrite <- IHsl; clear IHsl.
          reflexivity.
    Qed.

    Lemma imp_data_stmt_to_imp_ejson_stmt_correct (σ:pd_bindings) (stmt:imp_data_stmt) :
      unlift_result_env (imp_data_stmt_eval h stmt σ) =
      imp_ejson_stmt_eval h (imp_data_stmt_to_imp_ejson stmt) (lift_pd_bindings σ).
    Proof.
      revert σ.
      imp_stmt_cases (induction stmt) Case.
      - Case "ImpStmtBlock"%string.
        intros.
        simpl.
        specialize (imp_data_decls_to_imp_ejson_decls_correct σ el).
        unfold imp_data_decls_eval in *;
        unfold imp_ejson_decls_eval in *; simpl.
        intros Hel.
        rewrite <- Hel; clear Hel.
        unfold unlift_result_env; unfold lift.
        destruct (@ImpEval.imp_decls_eval (@imp_data_model fruntime) (@imp_data_constant fruntime)
              (@imp_data_op fruntime) imp_data_runtime_op
              (@imp_data_model_normalize fruntime h)
              (@imp_data_runtime_eval fruntime)
              (@imp_data_op_eval fruntime h) σ el
            ); simpl; intros.
        (* Some *)
        + rewrite ImpEval.imp_decls_erase_remove_map; simpl.
          unfold unlift_result_env; unfold lift; simpl in *.
          unfold ImpEval.pd_rbindings in p.
          assert ((map
             (fun xy : string * option data =>
              (fst xy, match snd xy with
                       | Some a' => Some (data_to_ejson a')
                       | None => None
                       end)) p = lift_pd_bindings p)) by reflexivity.
          rewrite H0.
          rewrite <- (imp_fold_qcert_stmt_to_imp_ejson_stmt_correct); try assumption; clear H.
          rewrite map_lift_pd_bindings_eq.
          induction el; simpl in *; try reflexivity.
          rewrite <- IHel; clear IHel.
          destruct a; simpl.
          destruct (@ImpEval.imp_decls_erase (@imp_data_model fruntime)
          (@fold_left (option (@ImpEval.pd_rbindings (@imp_data_model fruntime)))
             (@ImpEval.imp_stmt (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op)
             (fun (c : option (@ImpEval.pd_rbindings (@imp_data_model fruntime)))
                (s : @ImpEval.imp_stmt (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op)
              =>
              match c return (option (@ImpEval.pd_rbindings (@imp_data_model fruntime))) with
              | Some σ' => @imp_data_stmt_eval fruntime h s σ'
              | None => @None (@ImpEval.pd_rbindings (@imp_data_model fruntime))
              end) sl (@Some (@ImpEval.pd_rbindings (@imp_data_model fruntime)) p))
          (prod var
             (option (@Imp.imp_expr (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op)))
          el); [|reflexivity].
          destruct p0; simpl; try reflexivity.
        + repeat rewrite ImpEval.imp_decls_erase_none; reflexivity.
      - Case "ImpStmtAssign"%string.
        intros σ.
        simpl.
        specialize (imp_data_expr_to_imp_ejson_expr_correct σ e).
        unfold imp_ejson_expr_eval in *.
        intros He; rewrite <- He; clear He.
        unfold unlift_result, lift.
        unfold imp_data_expr_eval.
        destruct (@ImpEval.imp_expr_eval (@imp_data_model fruntime) (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op
          (@imp_data_model_normalize fruntime h) (@imp_data_runtime_eval fruntime)
          (@imp_data_op_eval fruntime h) σ e);
          try reflexivity.
        unfold lift_pd_bindings.
        rewrite lookup_map_codomain_unfolded.
        unfold lift.
        unfold imp_data_model, foreign_runtime_data.
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
        specialize (imp_data_expr_to_imp_ejson_expr_correct σ e).
        unfold imp_ejson_expr_eval in *.
        intros He; rewrite <- He; clear He.
        unfold unlift_result, lift.
        unfold imp_data_expr_eval.
        destruct (@ImpEval.imp_expr_eval (@imp_data_model fruntime) (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op
          (@imp_data_model_normalize fruntime h) (@imp_data_runtime_eval fruntime)
          (@imp_data_op_eval fruntime h) σ e);
          try reflexivity.
        rewrite imp_ejson_model_to_list_comm; simpl.
        destruct (imp_data_model_to_list i); try reflexivity; simpl; clear i.
        revert σ.
        induction l; try reflexivity; simpl; intros.
        specialize (IHstmt ((v, Some a) :: σ)); simpl in IHstmt.
        Set Printing All.
        assert (@imp_ejson_stmt_eval fejson _ h (imp_data_stmt_to_imp_ejson stmt)
        (@cons (prod var (option (@imp_ejson_model fejson)))
           (@pair var (option (@imp_ejson_model fejson)) v
              (@Some (@imp_ejson_model fejson) (@data_to_ejson fruntime fejson ftejson a)))
           (lift_pd_bindings σ)) =
                (@imp_ejson_stmt_eval fejson _ h (imp_data_stmt_to_imp_ejson stmt)
                (@cons (prod string (option (@ejson fejson)))
                   (@pair string (option (@ejson fejson)) v
                      (@Some (@ejson fejson) (@data_to_ejson fruntime fejson ftejson a)))
                   (lift_pd_bindings σ)))) by reflexivity.
        rewrite <- H in IHstmt; clear H.
        rewrite <- IHstmt; clear IHstmt.
        assert (
            (@imp_data_stmt_eval fruntime h stmt
           (@cons (prod string (option (@imp_data_model fruntime)))
                  (@pair string (option (@imp_data_model fruntime)) v (@Some (@imp_data_model fruntime) a)) σ))
            = @imp_data_stmt_eval fruntime h stmt
           (@cons (prod var (option (@imp_data_model fruntime)))
                  (@pair var (option (@imp_data_model fruntime)) v (@Some (@imp_data_model fruntime) a)) σ)) by reflexivity.
        rewrite <- H; clear H.
        destruct (imp_data_stmt_eval h stmt ((v, Some a) :: σ)); try reflexivity; simpl.
        destruct p; try reflexivity; simpl.
        unfold lift_pd_bindings in IHl.
        rewrite <- IHl.
        reflexivity.
      - Case "ImpStmtForRange"%string.
        intros.
        simpl.
        specialize (imp_data_expr_to_imp_ejson_expr_correct σ e1).
        unfold imp_ejson_expr_eval in *.
        intros He; rewrite <- He; clear He.
        unfold unlift_result, lift.
        unfold imp_data_expr_eval.
        destruct (@ImpEval.imp_expr_eval (@imp_data_model fruntime) (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op
          (@imp_data_model_normalize fruntime h) (@imp_data_runtime_eval fruntime)
          (@imp_data_op_eval fruntime h) σ e1);
          try reflexivity; simpl.
        rewrite data_to_ejson_to_Z_comm;
          destruct (imp_ejson_model_to_Z (data_to_ejson i)); try reflexivity.
        specialize (imp_data_expr_to_imp_ejson_expr_correct σ e2).
        unfold imp_ejson_expr_eval in *.
        intros He; rewrite <- He; clear He.
        unfold unlift_result, olift, lift.
        unfold imp_data_expr_eval.
        destruct (@ImpEval.imp_expr_eval (@imp_data_model fruntime) (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op
          (@imp_data_model_normalize fruntime h) (@imp_data_runtime_eval fruntime)
          (@imp_data_op_eval fruntime h) σ e2);
          try reflexivity; simpl.
        rewrite data_to_ejson_to_Z_comm;
          destruct (imp_ejson_model_to_Z (data_to_ejson i0)); try reflexivity.
        generalize (ImpEval.nb_iter z z0); intros. (* XXX I think we do not care how n is built for this part *)
        revert σ z.
        induction n; try reflexivity; simpl; intros.
        specialize (IHstmt ((v, Some (imp_data_Z_to_data z)) :: σ)); simpl in IHstmt.
        assert ((@imp_ejson_stmt_eval fejson _ h (imp_data_stmt_to_imp_ejson stmt)
                (@cons (prod string (option (@ejson fejson)))
                   (@pair string (option (@ejson fejson)) v
                      (@Some (@ejson fejson) (@ejbigint fejson z)))
                   (lift_pd_bindings σ)))
                  = (@imp_ejson_stmt_eval fejson _ h (imp_data_stmt_to_imp_ejson stmt)
        (@cons (prod var (option (@imp_ejson_model fejson)))
           (@pair var (option (@imp_ejson_model fejson)) v
              (@Some (@imp_ejson_model fejson)
                 (@imp_ejson_Z_to_data fejson z))) (lift_pd_bindings σ)))) by reflexivity.
        rewrite H in IHstmt; clear H.
        rewrite <- IHstmt; clear IHstmt.
        assert
          (@imp_data_stmt_eval
             fruntime h stmt
             (@cons (prod string (option (@imp_data_model fruntime)))
                    (@pair string (option (@imp_data_model fruntime)) v
                           (@Some (@imp_data_model fruntime) (@imp_data_Z_to_data fruntime z))) σ)
           =
           @imp_data_stmt_eval fruntime h stmt
           (@cons (prod var (option (@imp_data_model fruntime)))
              (@pair var (option (@imp_data_model fruntime)) v
                 (@Some (@imp_data_model fruntime) (@imp_data_Z_to_data fruntime z))) σ)) by reflexivity.
        rewrite <- H; clear H.
        destruct (imp_data_stmt_eval h stmt ((v, Some (imp_data_Z_to_data z)) :: σ)); try reflexivity.
        destruct p; try reflexivity; simpl.
        unfold lift_pd_bindings in IHn.
        rewrite IHn.
reflexivity.
      - Case "ImpStmtIf"%string.
        intros σ.
        simpl.
        specialize (imp_data_expr_to_imp_ejson_expr_correct σ e).
        unfold imp_ejson_expr_eval in *.
        intros Hi.
        rewrite <- Hi; clear Hi.
        unfold unlift_result.
        unfold lift.
        unfold imp_ejson_expr_eval.
        unfold imp_data_expr_eval.
        destruct (@ImpEval.imp_expr_eval (@imp_data_model fruntime) (@imp_data_constant fruntime) (@imp_data_op fruntime) imp_data_runtime_op
           (@imp_data_model_normalize fruntime h) (@imp_data_runtime_eval fruntime)
           (@imp_data_op_eval fruntime h) σ e);
          try reflexivity.
        rewrite <- data_to_bool_ejson_to_bool_correct.
        rewrite data_to_ejson_idempotent.
        match_destr.
        match_destr.
    Qed.

    Lemma imp_data_function_to_imp_ejson_function_correct (d:data) (f:imp_data_function) :
      imp_data_function_eval h f d =
      lift ejson_to_data (imp_ejson_function_eval h (imp_data_function_to_imp_ejson f) (data_to_ejson d)).
    Proof.
      destruct f; simpl.
      generalize (imp_data_stmt_to_imp_ejson_stmt_correct [(v0, None); (v, Some d)] i); intros.
      unfold imp_data_stmt_eval in H.
      unfold imp_ejson_stmt_eval in H.
      unfold imp_data_model in *.
      simpl in H.
      unfold lift.
      assert ((@ImpEval.imp_stmt_eval (@imp_ejson_model fejson) (@imp_ejson_constant fejson) imp_ejson_op
           imp_ejson_runtime_op (@imp_ejson_model_normalize fejson)
           (@imp_ejson_model_to_bool fejson)
           (@imp_ejson_model_to_Z fejson)
           (@imp_ejson_model_to_list fejson)
           (@imp_ejson_Z_to_data fejson)
           (@imp_ejson_runtime_eval fejson _ h)
           (@imp_ejson_op_eval fejson)
           (imp_data_stmt_to_imp_ejson i)
           (@cons (prod string (option (@ejson fejson)))
              (@pair string (option (@ejson fejson)) v0
                 (@None (@ejson fejson)))
              (@cons (prod string (option (@ejson fejson)))
                 (@pair string (option (@ejson fejson)) v
                    (@Some (@ejson fejson) (@data_to_ejson fruntime fejson ftejson d)))
                 (@nil (prod string (option (@ejson fejson)))))))
             = @ImpEval.imp_stmt_eval (@imp_ejson_model fejson) (@imp_ejson_constant fejson) imp_ejson_op imp_ejson_runtime_op
          (@imp_ejson_model_normalize fejson)
          (@imp_ejson_model_to_bool fejson)
          (@imp_ejson_model_to_Z fejson)
          (@imp_ejson_model_to_list fejson)
          (@imp_ejson_Z_to_data fejson)
          (@imp_ejson_runtime_eval fejson _ h)
          (@imp_ejson_op_eval fejson)
          (imp_data_stmt_to_imp_ejson i)
          (@cons (prod var (option (@imp_ejson_model fejson)))
             (@pair var (option (@imp_ejson_model fejson)) v0
                (@None (@imp_ejson_model fejson)))
             (@cons (prod var (option (@imp_ejson_model fejson)))
                (@pair var (option (@imp_ejson_model fejson)) v
                   (@Some (@imp_ejson_model fejson) (@data_to_ejson fruntime fejson ftejson d)))
                (@nil (prod var (option (@imp_ejson_model fejson))))))) by reflexivity.
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

    Lemma imp_data_function_to_imp_ejson_function_aux_correct (d:data) (f:imp_data_function) :
      lift data_to_ejson (imp_data_function_eval h f d) =
      imp_ejson_function_eval h (imp_data_function_to_imp_ejson f) (data_to_ejson d).
    Proof.
      destruct f; simpl.
      generalize (imp_data_stmt_to_imp_ejson_stmt_correct [(v0, None); (v, Some d)] i); intros.
      unfold imp_data_stmt_eval in H.
      unfold imp_ejson_stmt_eval in H.
      unfold imp_data_model in *.
      simpl in H.
      unfold lift.
      assert ((@ImpEval.imp_stmt_eval (@imp_ejson_model fejson) (@imp_ejson_constant fejson) imp_ejson_op
           imp_ejson_runtime_op (@imp_ejson_model_normalize fejson)
           (@imp_ejson_model_to_bool fejson)
           (@imp_ejson_model_to_Z fejson)
           (@imp_ejson_model_to_list fejson)
           (@imp_ejson_Z_to_data fejson)
           (@imp_ejson_runtime_eval fejson _ h)
           (@imp_ejson_op_eval fejson)
           (imp_data_stmt_to_imp_ejson i)
           (@cons (prod string (option (@ejson fejson)))
              (@pair string (option (@ejson fejson)) v0
                 (@None (@ejson fejson)))
              (@cons (prod string (option (@ejson fejson)))
                 (@pair string (option (@ejson fejson)) v
                    (@Some (@ejson fejson) (@data_to_ejson fruntime fejson ftejson d)))
                 (@nil (prod string (option (@ejson fejson)))))))
             = @ImpEval.imp_stmt_eval (@imp_ejson_model fejson) (@imp_ejson_constant fejson) imp_ejson_op imp_ejson_runtime_op
          (@imp_ejson_model_normalize fejson)
          (@imp_ejson_model_to_bool fejson)
          (@imp_ejson_model_to_Z fejson)
          (@imp_ejson_model_to_list fejson)
          (@imp_ejson_Z_to_data fejson)
          (@imp_ejson_runtime_eval fejson _ h)
          (@imp_ejson_op_eval fejson)
          (imp_data_stmt_to_imp_ejson i)
          (@cons (prod var (option (@imp_ejson_model fejson)))
             (@pair var (option (@imp_ejson_model fejson)) v0
                (@None (@imp_ejson_model fejson)))
             (@cons (prod var (option (@imp_ejson_model fejson)))
                (@pair var (option (@imp_ejson_model fejson)) v
                   (@Some (@imp_ejson_model fejson) (@data_to_ejson fruntime fejson ftejson d)))
                (@nil (prod var (option (@imp_ejson_model fejson))))))) by reflexivity.
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
        reflexivity.
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

    Theorem imp_data_to_imp_ejson_correct (σc:bindings) (q:imp_data) :
      imp_data_eval_top h σc q =
      imp_ejson_eval_top h σc (imp_data_to_imp_ejson q).
    Proof.
      unfold imp_data_eval_top.
      unfold imp_ejson_eval_top.
      unfold imp_ejson_eval_top_on_ejson.
      unfold imp_ejson_eval.
      destruct q; simpl.
      destruct l; try reflexivity; simpl.
      destruct p; simpl.
      destruct l; try reflexivity; simpl.
      generalize (imp_data_function_to_imp_ejson_function_correct (drec (rec_sort σc)) i); intros.
      unfold imp_data_eval_top.
      unfold imp_ejson_eval_top.
      unfold imp_ejson_eval_top_on_ejson.
      unfold imp_ejson_eval.
      unfold id; simpl.
      simpl in H.
      unfold imp_data_function_eval in H.
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

End ImpDatatoImpEJson.
