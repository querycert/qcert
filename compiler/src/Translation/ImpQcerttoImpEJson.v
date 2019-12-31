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

  Definition imp_qcert_unary_op_to_imp_ejson (op:unary_op) el : imp_ejson_expr :=
    match el with
    | [e] =>
      match op with
      | OpIdentity => e
      | OpNeg => mk_imp_ejson_op EJsonOpNot [ e ]
      | OpRec s => mk_imp_ejson_op (EJsonOpObject [json_key_encode s]) [ e ]
      | OpDot s => mk_imp_ejson_runtime_call EJsonRuntimeDeref [ e; ImpExprConst (ejstring (json_key_encode s)) ]
      | OpRecRemove s => mk_imp_ejson_runtime_call EJsonRuntimeRemove [ e; mk_string (json_key_encode s) ]
      | OpRecProject fl =>
        mk_imp_ejson_runtime_call
          EJsonRuntimeProject ([ e ] ++ [ mk_string_array fl ])
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
      | OpFloatSum => mk_imp_ejson_runtime_call EJsonRuntimeSum el
      | OpFloatMean => mk_imp_ejson_runtime_call EJsonRuntimeArithMean el
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
        (*** XXX Why change the avoid list here ? *)
        (* (map (fun xy => (fst xy, *)
        (*                  lift imp_qcert_expr_to_imp_ejson (snd xy))) lv) *)
        (* (map (imp_qcert_stmt_to_imp_ejson ((List.map fst lv) ++ avoid)) ls) *)
        (map (fun xy => (fst xy, lift imp_qcert_expr_to_imp_ejson (snd xy))) lv)
        (map (imp_qcert_stmt_to_imp_ejson avoid) ls)
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
    Definition unlift_result (res:option data) : option ejson :=
      lift data_to_ejson res.
    Definition lift_result_env (res:option pd_jbindings) : option pd_bindings :=
      lift (fun env => List.map (fun xy => (fst xy, lift ejson_to_data (snd xy))) env) res.
    Definition unlift_result_env (res:option pd_bindings) : option pd_jbindings :=
      lift (fun env => List.map (fun xy => (fst xy, lift data_to_ejson (snd xy))) env) res.
  End Lift.

  Section Correctness.
    Lemma map_qcert_ejson_eval
          (σ:pd_bindings) (el:list imp_expr) :
      Forall
        (fun exp : imp_expr =>
           imp_qcert_expr_eval h σ exp =
           lift_result
             (imp_ejson_expr_eval h (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp))) el -> 
      map (fun x : imp_qcert_expr => imp_qcert_expr_eval h σ x) el =
      map (fun x : imp_qcert_expr => lift_result
             (imp_ejson_expr_eval h (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson x))) el.
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
           unlift_result (imp_qcert_expr_eval h σ exp) =
           imp_ejson_expr_eval h (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson exp)) [i]
      -> unlift_result (imp_qcert_expr_eval h σ i)
         = imp_ejson_expr_eval h (lift_pd_bindings σ) (imp_qcert_expr_to_imp_ejson i).
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
      match match oflatten l with
            | Some a' => Some (dcoll a')
            | None => None
            end with
      | Some a' => Some (data_to_ejson a')
      | None => None
      end = match jflatten (map data_to_ejson l) with
            | Some a' => Some (ejarray a')
            | None => None
            end.
    Proof.
      induction l; [reflexivity|].
      destruct a; try reflexivity.
      simpl.
      unfold jflatten, oflatten in *; simpl.
      destruct (lift_flat_map (fun x : data => match x with
                                               | dcoll y => Some y
                                               | _ => None
                                               end) l);
        destruct (lift_flat_map (fun x : ejson => match x with
                                          | ejarray y => Some y
                                          | _ => None
                                                  end) (map data_to_ejson l)); simpl; try congruence.
      simpl in IHl.
      inversion IHl; clear IHl.
      subst.
      f_equal.
      f_equal.
      apply map_app.
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

    Lemma ejson_to_data_jobj_nbrand s e b d: (ejson_to_data (ejobject [(s, e)])) <> dbrand b d.
    Proof.
      simpl.
      repeat match_destr.
    Qed.

    Lemma ejson_to_data_jobj_nbrand_long s e p p0 l b d:
      (ejson_to_data (ejobject ((s, e) :: p :: p0 :: l))) <> dbrand b d.
    Proof.
      simpl.
      repeat match_destr.
    Qed.

    Lemma ejson_to_data_jobj_nbrand_no_data e s0 e0 b d:
      s0 <> "$data"%string ->
      ejson_to_data (ejobject [("$class"%string, e); (s0, e0)]) <> dbrand b d.
    Proof.
      intros; simpl.
      repeat match_destr; try congruence.
    Qed.
      
    Lemma ejson_to_data_jobj_nbrand_no_class e s e0 b d:
      s <> "$class"%string ->
      ejson_to_data (ejobject [(s, e); ("$data"%string, e0)]) <> dbrand b d.
    Proof.
      intros; simpl.
      repeat match_destr; try congruence.
    Qed.

    Lemma ejson_to_data_jobj_nbrand_no_class_no_data s e s0 e0 b d:
      s <> "$class"%string ->
      s0 <> "$data"%string ->
      ejson_to_data (ejobject [(s, e); (s0, e0)]) <> dbrand b d.
    Proof.
      intros; simpl.
      repeat match_destr; try congruence.
    Qed.

    Lemma ejson_data_maybe_brand s s0 e e0 :
      match ejson_to_data (ejobject [(s, e); (s0, e0)]) with
      | dbrand _ d' => Some d'
      | _ => None
      end =
      match
        match e with
        | ejarray j1 =>
          if string_dec s "$class"
          then
            if string_dec s0 "$data"
            then match ejson_brands j1 with
                 | Some _ => Some e0
                 | None => None
                 end
            else None
          else None
        | _ => None
        end
      with
      | Some a' => Some (ejson_to_data a')
      | None => None
      end.
    Proof.
      case_eq (string_dec s "$class"); intros; subst;
      case_eq (string_dec s0 "$data"); intros; subst.
      - destruct e; simpl;
          try (destruct e0; simpl; reflexivity).
        destruct (ejson_brands l); reflexivity.
      - case_eq (ejson_to_data (ejobject [("$class"%string, e); (s0, e0)])); intros;
          try (destruct e; simpl; reflexivity);
          specialize (ejson_to_data_jobj_nbrand_no_data e s0 e0 b d n);
          intros; contradiction.
      - case_eq (ejson_to_data (ejobject [(s, e); ("$data"%string, e0)])); intros;
          try (destruct e; simpl; reflexivity);
          specialize (ejson_to_data_jobj_nbrand_no_class e s e0 b d n);
          intros; contradiction.
      - case_eq (ejson_to_data (ejobject [(s, e); (s0, e0)])); intros;
          try (destruct e; reflexivity);
          specialize (ejson_to_data_jobj_nbrand_no_class_no_data s e s0 e0 b d n n0);
          intros; contradiction.
    Qed.

    Lemma ejson_data_maybe_cast b s s0 e e0 :
      match ejson_to_data (ejobject [(s, e); (s0, e0)]) with
      | dbrand b' _ =>
        if sub_brands_dec h b' b then Some (dsome (ejson_to_data (ejobject [(s, e); (s0, e0)]))) else Some dnone
      | _ => None
      end =
      match
        match e with
        | ejarray jl2 =>
          if string_dec s "$class"
          then
            if string_dec s0 "$data"
            then
              match ejson_brands jl2 with
              | Some b2 =>
                if sub_brands_dec h b2 b
                then Some (ejobject [("$left"%string, ejobject [(s, e); (s0, e0)])])
                else Some (ejobject [("$right"%string, ejnull)])
              | None => None
              end
            else None
          else None
        | _ => None
        end
      with
      | Some a' => Some (ejson_to_data a')
      | None => None
      end.
    Proof.
      case_eq (string_dec s "$class"); intros; subst;
      case_eq (string_dec s0 "$data"); intros; subst.
      - destruct e; simpl;
          try (destruct e0; simpl; reflexivity).
        case_eq (ejson_brands l); intros; [|reflexivity].
        destruct (sub_brands_dec h l0 b); [|reflexivity].
        f_equal; simpl; unfold dsome; f_equal.
        rewrite H1.
        reflexivity.
      - case_eq (ejson_to_data (ejobject [("$class"%string, e); (s0, e0)])); intros;
          try (destruct e; simpl; reflexivity).
          specialize (ejson_to_data_jobj_nbrand_no_data e s0 e0 b0 d n);
          intros; contradiction.
      - case_eq (ejson_to_data (ejobject [(s, e); ("$data"%string, e0)])); intros;
          try (destruct e; simpl; reflexivity);
          specialize (ejson_to_data_jobj_nbrand_no_class e s e0 b0 d n);
          intros; contradiction.
      - case_eq (ejson_to_data (ejobject [(s, e); (s0, e0)])); intros;
          try (destruct e; reflexivity);
          specialize (ejson_to_data_jobj_nbrand_no_class_no_data s e s0 e0 b0 d n n0);
          intros; contradiction.
    Qed.

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
      apply Forall_singleton in H.
      unary_op_cases (destruct u) Case; unfold lift_result, lift, olift; simpl;
        try (rewrite <- H; clear H;
             destruct (imp_qcert_expr_eval h σ i);
             try reflexivity; simpl; unfold unlift_result, lift; simpl).
      - Case "OpNeg"%string.
        destruct d; try reflexivity.
      - Case "OpDot"%string.
        admit.
      - Case "OpRecRemove"%string.
        admit.
      - Case "OpRecProject"%string.
        admit. (** XXX This one looks more complicated *)
      - Case "OpSingleton"%string.
        destruct d; try reflexivity.
        destruct l; try reflexivity; simpl.
        destruct l; try reflexivity; simpl.
      - Case "OpFlatten"%string.
        destruct d; try reflexivity; simpl.
        apply oflatten_jflatten_roundtrip.
      - Case "OpDistinct"%string.
        admit.
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
        rewrite of_string_list_over_strings_idempotent; simpl.
        reflexivity.
      - Case "OpUnbrand"%string.
        admit.
      - Case "OpCast"%string.
        rewrite json_brands_of_brands_idempotent.
        admit.
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
        admit.
      - Case "OpFloatOfNat"%string.
        destruct d; reflexivity.
      - Case "OpFloatUnary"%string.
        destruct f; simpl;
        destruct d; reflexivity.
      - Case "OpFloatTruncate"%string.
        destruct d; reflexivity.
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
      Opaque ejson_to_data.
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

    Lemma false_lift_idem j:
      unlift_result
        (lift_result j) = j.
    Proof.
      unfold unlift_result, lift_result, lift.
      destruct j; [|reflexivity].
      admit.
    Admitted.

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
          destruct (@ImpEval.imp_expr_eval (@imp_qcert_data fruntime) (@imp_qcert_op fruntime) imp_qcert_runtime_op
             (@imp_qcert_data_normalize fruntime h) (@imp_qcert_runtime_eval fruntime)
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

    Lemma imp_fold_qcert_stmt_to_imp_ejson_stmt_correct avoid (σ:pd_bindings) sl :
      (Forall
         (fun stmt : imp_stmt =>
            forall (σ : pd_bindings) (avoid : list string),
              unlift_result_env (imp_qcert_stmt_eval h stmt σ) =
              imp_ejson_stmt_eval
                h (imp_qcert_stmt_to_imp_ejson avoid stmt) (lift_pd_bindings σ)) sl) ->
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
              end) (map (imp_qcert_stmt_to_imp_ejson avoid) sl) (Some (lift_pd_bindings σ))).
    Proof.
      intros.
      revert σ.
      induction sl; simpl; intros.
      - rewrite map_lift_pd_bindings_eq; reflexivity.
      - assert (Forall
           (fun stmt : imp_stmt =>
            forall (σ : pd_bindings) (avoid : list string),
            unlift_result_env (imp_qcert_stmt_eval h stmt σ) =
            imp_ejson_stmt_eval h (imp_qcert_stmt_to_imp_ejson avoid stmt) (lift_pd_bindings σ)) sl)
        by (rewrite Forall_forall in *; intros;
            apply H; simpl; right; assumption).
        assert (unlift_result_env (imp_qcert_stmt_eval h a σ) =
                imp_ejson_stmt_eval h (imp_qcert_stmt_to_imp_ejson avoid a) (lift_pd_bindings σ))
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
          assert (@fold_left (option (@ImpEval.pd_rbindings (@imp_ejson_data (@foreign_runtime_ejson fruntime))))
              (@ImpEval.imp_stmt (@imp_ejson_data (@foreign_runtime_ejson fruntime)) imp_ejson_op
                 imp_ejson_runtime_op)
              (fun (c : option (@ImpEval.pd_rbindings (@imp_ejson_data (@foreign_runtime_ejson fruntime))))
                 (s : @ImpEval.imp_stmt (@imp_ejson_data (@foreign_runtime_ejson fruntime)) imp_ejson_op
                        imp_ejson_runtime_op) =>
               match
                 c return (option (@ImpEval.pd_rbindings (@imp_ejson_data (@foreign_runtime_ejson fruntime))))
               with
               | Some σ' => @imp_ejson_stmt_eval (@foreign_runtime_ejson fruntime) h s σ'
               | None => @None (@ImpEval.pd_rbindings (@imp_ejson_data (@foreign_runtime_ejson fruntime)))
               end)
              (@map (@imp_qcert_stmt fruntime) (@imp_ejson_stmt (@foreign_runtime_ejson fruntime))
                 (imp_qcert_stmt_to_imp_ejson avoid) sl)
              (@None (list (prod string (option (@ejson (@foreign_runtime_ejson fruntime)))))) =
(@fold_left (option (@ImpEval.pd_rbindings (@imp_ejson_data (@foreign_runtime_ejson fruntime))))
       (@ImpEval.imp_stmt (@imp_ejson_data (@foreign_runtime_ejson fruntime)) imp_ejson_op imp_ejson_runtime_op)
       (fun (c : option (@ImpEval.pd_rbindings (@imp_ejson_data (@foreign_runtime_ejson fruntime))))
          (s : @ImpEval.imp_stmt (@imp_ejson_data (@foreign_runtime_ejson fruntime)) imp_ejson_op
                 imp_ejson_runtime_op) =>
        match c return (option (@ImpEval.pd_rbindings (@imp_ejson_data (@foreign_runtime_ejson fruntime)))) with
        | Some σ' => @imp_ejson_stmt_eval (@foreign_runtime_ejson fruntime) h s σ'
        | None => @None (@ImpEval.pd_rbindings (@imp_ejson_data (@foreign_runtime_ejson fruntime)))
        end)
       (@map (@imp_qcert_stmt fruntime) (@imp_ejson_stmt (@foreign_runtime_ejson fruntime))
          (imp_qcert_stmt_to_imp_ejson avoid) sl)
       (@None (@ImpEval.pd_rbindings (@imp_ejson_data (@foreign_runtime_ejson fruntime)))))) by reflexivity.
          rewrite <- H; clear H.
          rewrite <- IHsl; clear IHsl.
          reflexivity.
    Qed.

    Lemma imp_qcert_stmt_to_imp_ejson_stmt_correct (σ:pd_bindings) (stmt:imp_qcert_stmt) :
      forall avoid: list string,
         (* (fres_var stmt) avoid -> *)
        unlift_result_env (imp_qcert_stmt_eval h stmt σ) =
        imp_ejson_stmt_eval h (imp_qcert_stmt_to_imp_ejson avoid stmt) (lift_pd_bindings σ).
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
        destruct (@ImpEval.imp_decls_eval
                    (@imp_qcert_data fruntime) (@imp_qcert_op fruntime) imp_qcert_runtime_op
                    (@imp_qcert_data_normalize fruntime h) (@imp_qcert_runtime_eval fruntime)
                    (@imp_qcert_op_eval fruntime h) σ el); simpl; intros.
        (* Some *)
        + rewrite ImpEval.imp_decls_erase_remove_map.
          rewrite <- (imp_fold_qcert_stmt_to_imp_ejson_stmt_correct avoid); try assumption; clear H.
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
          (prod var (option (@imp_expr (@imp_qcert_data fruntime) (@imp_qcert_op fruntime) imp_qcert_runtime_op)))
          el); [|reflexivity].
          destruct p0; simpl; try reflexivity.
        + repeat rewrite ImpEval.imp_decls_erase_none; reflexivity.
      - Case "ImpStmtAssign"%string.
        intros σ avoid.
        simpl.
        specialize (imp_qcert_expr_to_imp_ejson_expr_correct σ e).
        unfold imp_ejson_expr_eval in *.
        intros He.
        rewrite <- He.
        unfold unlift_result.
        unfold lift.
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
        clear He.
        induction σ; try reflexivity.
        simpl.
        destruct a; simpl.
        destruct (string_dec v s); simpl; try reflexivity.
        + f_equal; f_equal.
          inversion IHσ; clear IHσ; intros.
          rewrite H0; reflexivity.
      - Case "ImpStmtFor"%string.
        admit.
      - Case "ImpStmtForRange"%string.
        intros avoid.
        admit. (* XXX TODO: eval XXX *)
      - Case "ImpStmtIf"%string.
        intros σ avoid.
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
    (* Qed. *)
    Admitted.

    Lemma imp_qcert_function_to_imp_ejson_function_correct (d:data) (f:imp_qcert_function) :
      imp_qcert_function_eval h f d =
      lift ejson_to_data (imp_ejson_function_eval h (imp_qcert_function_to_imp_ejson f) (data_to_ejson d)).
    Proof.
      destruct f; simpl.
      generalize (imp_qcert_stmt_to_imp_ejson_stmt_correct [(v0, None); (v, Some d)] i (v::nil)); intros.
      unfold imp_qcert_stmt_eval in H.
      unfold imp_ejson_stmt_eval in H.
      unfold imp_qcert_data in *.
      simpl in H.
      unfold lift.
      assert (@ImpEval.imp_stmt_eval (@imp_ejson_data (@foreign_runtime_ejson fruntime)) imp_ejson_op
          imp_ejson_runtime_op (@imp_ejson_data_normalize (@foreign_runtime_ejson fruntime))
          (@imp_ejson_data_to_bool (@foreign_runtime_ejson fruntime))
          (@imp_ejson_data_to_Z (@foreign_runtime_ejson fruntime))
          (@imp_ejson_data_to_list (@foreign_runtime_ejson fruntime))
          (@imp_ejson_Z_to_data (@foreign_runtime_ejson fruntime))
          (@imp_ejson_runtime_eval (@foreign_runtime_ejson fruntime) h)
          (@imp_ejson_op_eval (@foreign_runtime_ejson fruntime))
          (imp_qcert_stmt_to_imp_ejson (@cons var v (@nil var)) i)
          (@cons (prod var (option (@imp_ejson_data (@foreign_runtime_ejson fruntime))))
             (@pair var (option (@imp_ejson_data (@foreign_runtime_ejson fruntime))) v0
                (@None (@imp_ejson_data (@foreign_runtime_ejson fruntime))))
             (@cons (prod var (option (@imp_ejson_data (@foreign_runtime_ejson fruntime))))
                (@pair var (option (@imp_ejson_data (@foreign_runtime_ejson fruntime))) v
                   (@Some (@imp_ejson_data (@foreign_runtime_ejson fruntime))
                      (@data_to_ejson (@foreign_runtime_data fruntime) (@foreign_runtime_ejson fruntime) ftejson
                                      d))) (@nil (prod var (option (@imp_ejson_data (@foreign_runtime_ejson fruntime))))))) =
              (@ImpEval.imp_stmt_eval (@imp_ejson_data (@foreign_runtime_ejson fruntime)) imp_ejson_op
           imp_ejson_runtime_op (@imp_ejson_data_normalize (@foreign_runtime_ejson fruntime))
           (@imp_ejson_data_to_bool (@foreign_runtime_ejson fruntime))
           (@imp_ejson_data_to_Z (@foreign_runtime_ejson fruntime))
           (@imp_ejson_data_to_list (@foreign_runtime_ejson fruntime))
           (@imp_ejson_Z_to_data (@foreign_runtime_ejson fruntime))
           (@imp_ejson_runtime_eval (@foreign_runtime_ejson fruntime) h)
           (@imp_ejson_op_eval (@foreign_runtime_ejson fruntime))
           (imp_qcert_stmt_to_imp_ejson (@cons var v (@nil var)) i)
           (@cons (prod string (option (@ejson (@foreign_runtime_ejson fruntime))))
              (@pair string (option (@ejson (@foreign_runtime_ejson fruntime))) v0
                 (@None (@ejson (@foreign_runtime_ejson fruntime))))
              (@cons (prod string (option (@ejson (@foreign_runtime_ejson fruntime))))
                 (@pair string (option (@ejson (@foreign_runtime_ejson fruntime))) v
                    (@Some (@ejson (@foreign_runtime_ejson fruntime))
                       (@data_to_ejson (@foreign_runtime_data fruntime) (@foreign_runtime_ejson fruntime) ftejson
                                       d))) (@nil (prod string (option (@ejson (@foreign_runtime_ejson fruntime))))))))) by reflexivity.
      rewrite H0; clear H0.
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
