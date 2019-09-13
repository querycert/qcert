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
Require Import NNRSimpRuntime.
Require Import Imp.
Require Import ImpQcert.
Require Import ImpQcertEval.

Section NNRSimptoImpQcert.
  Import ListNotations.

  Context {fruntime:foreign_runtime}.

  (** Translation *)

  Fixpoint nnrs_imp_expr_to_imp_qcert (exp: nnrs_imp_expr): imp_qcert_expr :=
    match exp with
    | NNRSimpGetConstant x =>
      ImpExprGetConstant x
    | NNRSimpVar x =>
      ImpExprVar x
    | NNRSimpConst d =>
      ImpExprConst d
    | NNRSimpBinop op e1 e2 =>
      let e1' := nnrs_imp_expr_to_imp_qcert e1 in
      let e2' := nnrs_imp_expr_to_imp_qcert e2 in
      ImpExprOp (QcertOpBinary op) [e1'; e2']
    | NNRSimpUnop op e =>
      let e' := nnrs_imp_expr_to_imp_qcert e in
      ImpExprOp (QcertOpUnary op) [e']
    | NNRSimpGroupBy g fields e =>
      let e' := nnrs_imp_expr_to_imp_qcert e in
      ImpExprRuntimeCall (QcertRuntimeGroupby g fields) [ e' ]
    end.

  Lemma nnrs_imp_expr_to_imp_qcert_correct h (σc:bindings) (σ:pd_bindings) (exp:nnrs_imp_expr) :
    nnrs_imp_expr_eval h σc σ exp = imp_qcert_expr_eval h σc σ (nnrs_imp_expr_to_imp_qcert exp).
  Proof.
    nnrs_imp_expr_cases (induction exp) Case; simpl.
    - Case "NNRSimpGetConstant"%string.
      reflexivity.
    - Case "NNRSimpVar"%string.
      unfold edot.
      reflexivity.
    - Case "NNRSimpConst"%string.
      reflexivity.
    - Case "NNRSimpBinop"%string.
      rewrite <- IHexp1.
      rewrite <- IHexp2.
      match_destr. match_destr.
    - Case "NNRSimpUnop"%string.
      rewrite <- IHexp.
      match_destr.
    - Case "NNRSimpGroupBy"%string.
      rewrite <- IHexp.
      match_destr.
  Qed.
  
  Fixpoint nnrs_imp_stmt_to_imp_qcert (stmt: nnrs_imp_stmt): imp_qcert_stmt :=
    match stmt with
    | NNRSimpSkip =>
      @ImpStmtBlock imp_qcert_data imp_qcert_op imp_qcert_runtime_op  [] []
    | NNRSimpSeq s1 s2 =>
      ImpStmtBlock
        []
        [ nnrs_imp_stmt_to_imp_qcert s1;
          nnrs_imp_stmt_to_imp_qcert s2 ]
    | NNRSimpLet x e s =>
      ImpStmtBlock
        [ (x, lift nnrs_imp_expr_to_imp_qcert e) ]
        [ nnrs_imp_stmt_to_imp_qcert s ]
    | NNRSimpAssign x e =>
      ImpStmtAssign x (nnrs_imp_expr_to_imp_qcert e)
    (* | NNRSimpPush x e => *)
    (*   stat_expr (array_push (expr_identifier x) (nnrs_imp_expr_to_imp_qcert e)) *)
    | NNRSimpFor x e s =>
      ImpStmtFor x (nnrs_imp_expr_to_imp_qcert e) (nnrs_imp_stmt_to_imp_qcert s)
    | NNRSimpIf e s1 s2 =>
      ImpStmtIf
        (nnrs_imp_expr_to_imp_qcert e)
        (nnrs_imp_stmt_to_imp_qcert s1)
        (nnrs_imp_stmt_to_imp_qcert s2)
    (* | NNRSimpEither (NNRSimpVar x) x1 s1 x2 s2 => *)
    (*   let e' := ImpExprVar x  in *)
    (*   ImpStmtIf *)
    (*     (ImpExprRuntimeCall QcertRuntimeEither [e']) *)
    (*     (ImpStmtBlock (* var x1 = toLeft(e); s1 *) *)
    (*        [ (x1, Some (ImpExprRuntimeCall QcertRuntimeToLeft [e'])) ] *)
    (*        [ nnrs_imp_stmt_to_imp_qcert s1 ]) *)
    (*     (ImpStmtBlock (* var x2 = toRight(e); s2 *) *)
    (*        [ (x2, Some (ImpExprRuntimeCall QcertRuntimeToRight [e'])) ] *)
    (*        [ nnrs_imp_stmt_to_imp_qcert s2 ]) *)
    | NNRSimpEither e x1 s1 x2 s2 =>
      (* XXX TODO: introduce a variable for e here or earlier in compilation? XXX *)
      let e' := nnrs_imp_expr_to_imp_qcert e in
      ImpStmtIf
        (ImpExprRuntimeCall QcertRuntimeEither [e'])
        (ImpStmtBlock (* var x1 = toLeft(e); s1 *)
           [ (x1, Some (ImpExprRuntimeCall QcertRuntimeToLeft [e'])) ]
           [ nnrs_imp_stmt_to_imp_qcert s1 ])
        (ImpStmtBlock (* var x2 = toRight(e); s2 *)
           [ (x2, Some (ImpExprRuntimeCall QcertRuntimeToRight [e'])) ]
           [ nnrs_imp_stmt_to_imp_qcert s2 ])
    end.

  Lemma nnrs_imp_stmt_to_imp_qcert_correct h (σc:bindings) (σ:pd_bindings) (stmt:nnrs_imp_stmt) :
    nnrs_imp_stmt_eval h σc stmt σ = imp_qcert_stmt_eval h σc (nnrs_imp_stmt_to_imp_qcert stmt) σ.
  Proof.
    revert σ.
    nnrs_imp_stmt_cases (induction stmt) Case; intros; simpl in *.
    - Case "NNRSimpSkip"%string.
      reflexivity.
    - Case "NNRSimpSeq"%string.
      simpl; rewrite <- IHstmt1.
      match_destr; simpl; auto.
    - Case "NNRSimpAssign"%string.
      rewrite nnrs_imp_expr_to_imp_qcert_correct.
      unfold imp_qcert_expr_eval.
      match_destr.
    - Case "NNRSimpLet"%string.
      destruct o; simpl.
      + rewrite nnrs_imp_expr_to_imp_qcert_correct.
        unfold imp_qcert_expr_eval.
        unfold lift.
        match_destr; simpl.
        rewrite IHstmt.
        reflexivity.
      + rewrite IHstmt.
        reflexivity.
    - Case "NNRSimpFor"%string.
      rewrite nnrs_imp_expr_to_imp_qcert_correct.
      unfold imp_qcert_expr_eval.
      match_destr.
      destruct i; simpl; try reflexivity.
      revert σ.
      induction l; try reflexivity.
      intro.
      rewrite IHstmt.
      unfold Var.var in *.
      unfold var in *.
      unfold imp_qcert_data in *.
      match_destr.
      match_destr.
    - Case "NNRSimpIf"%string.
      rewrite nnrs_imp_expr_to_imp_qcert_correct.
      unfold imp_qcert_expr_eval.
      match_destr; simpl.
      destruct i; simpl; try reflexivity.
      destruct b; simpl; auto.
    - Case "NNRSimpEither"%string.
      rewrite nnrs_imp_expr_to_imp_qcert_correct.
      unfold imp_qcert_expr_eval.
      match_destr.
      simpl.
      match_destr; simpl.
      * rewrite IHstmt1.
        unfold Var.var in *.
        unfold imp_qcert_data in *.
        match_destr; simpl.
      * rewrite IHstmt2.
        unfold Var.var in *.
        unfold imp_qcert_data in *.
        match_destr; simpl.
  Qed.

  (* XXX Danger: string hypotheys on the encoding of the queries XXX *)
  Definition nnrs_imp_to_imp_qcert_function globals (q: nnrs_imp): imp_function :=
    let constants := "constants"%string in
    let (stmt, ret) := q in
    let body :=
        ImpStmtBlock
          ((List.map
              (fun x => (x, Some (ImpExprRuntimeCall (QcertRuntimeDeref) [ ImpExprVar constants; ImpExprConst (dstring x) ])))
              globals)
             ++ [ (ret, None) ])
          [ nnrs_imp_stmt_to_imp_qcert stmt ]
    in
    ImpFun [ constants ] body ret.

  (* XXX Danger: string hypothesis on the encoding of the queries XXX *)
  Definition nnrs_imp_to_imp_qcert_top (qname: string) globals (q: nnrs_imp): imp :=
    ImpLib [ ((* qname *)"query"%string, nnrs_imp_to_imp_qcert_function globals q) ].

End NNRSimptoImpQcert.
