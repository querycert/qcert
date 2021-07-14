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
Require Import EquivDec.
Require Import Morphisms.
Require Import Permutation.
Require Import Eqdep_dec.
Require Import Utils.
Require Import DataRuntime.
Require Import NNRSimpRuntime.
Require Import Imp.
Require Import ImpData.
Require Import ImpDataEval.

Section NNRSimptoImpData.
  Import ListNotations.

  Context {fruntime:foreign_runtime}.

  (** Translation *)
  Section Translation.
    Fixpoint nnrs_imp_expr_to_imp_data (constants: string) (exp: nnrs_imp_expr): imp_data_expr :=
      match exp with
      | NNRSimpGetConstant x =>
        ImpExprOp (DataOpUnary (OpDot x)) [ ImpExprVar constants ]
      | NNRSimpVar x =>
        ImpExprVar x
      | NNRSimpConst d =>
        ImpExprConst d
      | NNRSimpBinop op e1 e2 =>
        let e1' := nnrs_imp_expr_to_imp_data constants e1 in
        let e2' := nnrs_imp_expr_to_imp_data constants e2 in
        ImpExprOp (DataOpBinary op) [e1'; e2']
      | NNRSimpUnop op e =>
        let e' := nnrs_imp_expr_to_imp_data constants e in
        ImpExprOp (DataOpUnary op) [e']
      | NNRSimpGroupBy g fields e =>
        let e' := nnrs_imp_expr_to_imp_data constants e in
        ImpExprRuntimeCall (DataRuntimeGroupby g fields) [ e' ]
      end.

    Fixpoint nnrs_imp_stmt_to_imp_data (constants: string) (stmt: nnrs_imp_stmt): imp_data_stmt :=
      match stmt with
      | NNRSimpSkip =>
        @ImpStmtBlock imp_data_model imp_data_op imp_data_runtime_op  [] []
      | NNRSimpSeq s1 s2 =>
        ImpStmtBlock
          []
          [ nnrs_imp_stmt_to_imp_data constants s1;
              nnrs_imp_stmt_to_imp_data constants s2 ]
      | NNRSimpLet x e s =>
        ImpStmtBlock
          [ (x, lift (nnrs_imp_expr_to_imp_data constants) e) ]
          [ nnrs_imp_stmt_to_imp_data constants s ]
      | NNRSimpAssign x e =>
        ImpStmtAssign x (nnrs_imp_expr_to_imp_data constants e)
      (* | NNRSimpPush x e => *)
      (*   stat_expr (array_push (expr_identifier x) (nnrs_imp_expr_to_imp_data e)) *)
      | NNRSimpFor x e s =>
        ImpStmtFor x (nnrs_imp_expr_to_imp_data constants e) (nnrs_imp_stmt_to_imp_data constants s)
      | NNRSimpIf e s1 s2 =>
        ImpStmtIf
          (nnrs_imp_expr_to_imp_data constants e)
          (nnrs_imp_stmt_to_imp_data constants s1)
          (nnrs_imp_stmt_to_imp_data constants s2)
      (* | NNRSimpEither (NNRSimpVar x) x1 s1 x2 s2 => *)
      (*   let e' := ImpExprVar x  in *)
      (*   ImpStmtIf *)
      (*     (ImpExprRuntimeCall DataRuntimeEither [e']) *)
      (*     (ImpStmtBlock (* var x1 = getLeft(e); s1 *) *)
      (*        [ (x1, Some (ImpExprRuntimeCall DataRuntimeToLeft [e'])) ] *)
      (*        [ nnrs_imp_stmt_to_imp_data s1 ]) *)
      (*     (ImpStmtBlock (* var x2 = getRight(e); s2 *) *)
      (*        [ (x2, Some (ImpExprRuntimeCall DataRuntimeToRight [e'])) ] *)
      (*        [ nnrs_imp_stmt_to_imp_data s2 ]) *)
      | NNRSimpEither e x1 s1 x2 s2 =>
        (* XXX TODO: introduce a variable for e here or earlier in compilation? XXX *)
        let e' := nnrs_imp_expr_to_imp_data constants e in
        ImpStmtIf
          (ImpExprRuntimeCall DataRuntimeEither [e'])
          (ImpStmtBlock (* var x1 = getLeft(e); s1 *)
             [ (x1, Some (ImpExprRuntimeCall DataRuntimeToLeft [e'])) ]
             [ nnrs_imp_stmt_to_imp_data constants s1 ])
          (ImpStmtBlock (* var x2 = getRight(e); s2 *)
             [ (x2, Some (ImpExprRuntimeCall DataRuntimeToRight [e'])) ]
             [ nnrs_imp_stmt_to_imp_data constants s2 ])
      end.

    Definition nnrs_imp_to_imp_data_function (q: nnrs_imp): imp_function :=
      let (stmt, ret) := q in
      let constants :=
          let fv := nnrs_imp_stmt_free_vars stmt in
          let bv := nnrs_imp_stmt_bound_vars stmt in
          fresh_var "constants"%string (ret :: fv ++ bv)
      in
      let body := nnrs_imp_stmt_to_imp_data constants stmt in
      ImpFun constants body ret.

    (* XXX Danger: string hypothesis on the encoding of the queries XXX *)
    Definition nnrs_imp_to_imp_data_top (qname: string) (q: nnrs_imp): imp :=
      ImpLib [ (qname, nnrs_imp_to_imp_data_function q) ].

  End Translation.

  Section Correctness.
    Lemma nnrs_imp_expr_to_imp_data_correct h (σc:bindings) (σ:pd_bindings) (exp:nnrs_imp_expr) :
      forall constants: string,
        let σ0 : pd_bindings :=
            σ ++ [(constants,  Some (drec σc))]
        in
        ~ In constants (nnrs_imp_expr_free_vars exp) ->
        lookup equiv_dec σ constants = None ->
        nnrs_imp_expr_eval h σc σ exp = imp_data_expr_eval h σ0 (nnrs_imp_expr_to_imp_data constants exp).
    Proof.
      intros constants.
      nnrs_imp_expr_cases (induction exp) Case; simpl.
      - Case "NNRSimpGetConstant"%string.
        intros Hfv Hσ.
        rewrite (lookup_app equiv_dec constants).
        unfold olift.
        unfold Var.var.
        unfold imp_data_model.
        case_eq (lookup equiv_dec σ constants); try congruence.
        intros.
        unfold lookup.
        case (equiv_dec constants constants); try congruence.
        intros.
        reflexivity.
      - Case "NNRSimpVar"%string.
        intros Hfv Hσ.
        rewrite (lookup_app equiv_dec v).
        unfold id.
        unfold olift.
        unfold Var.var.
        unfold imp_data_model.
        case_eq (lookup equiv_dec σ v); try reflexivity.
        intros Hv.
        case_eq (lookup equiv_dec [(constants, Some (drec σc))] v); try congruence.
        intros.
        simpl in H.
        destruct Hfv.
        left.
        case_eq (equiv_dec v constants); try congruence.
        intros.
        unfold Var.var in *.
        rewrite H0 in H.
        congruence.
      - Case "NNRSimpConst"%string.
        reflexivity.
      - Case "NNRSimpBinop"%string.
        intros Hfv Hσ.
        simpl in *.
        rewrite app_or_in_iff in Hfv.
        apply notand in Hfv.
        destruct Hfv as [ Hfv1 Hfv2 ].
        rewrite <- (IHexp1 Hfv1 Hσ).
        rewrite <- (IHexp2 Hfv2 Hσ).
        match_destr. match_destr.
      - Case "NNRSimpUnop"%string. 
        intros Hfv Hσ.
        simpl in *.
        rewrite <- IHexp; trivial.
        match_destr.
      - Case "NNRSimpGroupBy"%string.
        intros Hfv Hσ.
        simpl in *.
        rewrite <- IHexp; trivial.
        match_destr.
    Qed.

    Lemma nnrs_imp_stmt_to_imp_data_correct h (σc:bindings) (σ:pd_bindings) (stmt:nnrs_imp_stmt) :
      forall constants: string,
        let σ0 : pd_bindings :=
            σ ++ [(constants,  Some (drec σc))]
        in
        ~ In constants (nnrs_imp_stmt_free_vars stmt) ->
        ~ In constants (nnrs_imp_stmt_bound_vars stmt) ->
        lookup equiv_dec σ constants = None ->
        olift (fun σr => Some (σr ++ [(constants,  Some (drec σc))]))
              (nnrs_imp_stmt_eval h σc stmt σ) =
        imp_data_stmt_eval h (nnrs_imp_stmt_to_imp_data constants stmt) σ0.
    Proof.
      intros constants.
      simpl.
      revert σ.
      nnrs_imp_stmt_cases (induction stmt) Case; intros σ Hfv Hbv Hσ; simpl in *.
      - Case "NNRSimpSkip"%string.
        reflexivity.
      - Case "NNRSimpSeq"%string.
        unfold olift.
        rewrite app_or_in_iff in Hfv.
        apply notand in Hfv.
        destruct Hfv as [ Hfv1 Hfv2 ].
        rewrite app_or_in_iff in Hbv.
        apply notand in Hbv.
        destruct Hbv as [ Hbv1 Hbv2 ].
        simpl; rewrite <- IHstmt1; trivial.
        unfold olift.
        case_eq (nnrs_imp_stmt_eval h σc stmt1 σ); try reflexivity.
        intros σ' Hstmt1.
        simpl; rewrite <- IHstmt2; trivial.
        rewrite <- (nnrs_imp_stmt_eval_lookup_preserves_unwritten (h:=h) (σc:=σc) (s:=stmt1) [] [] σ σ'); trivial.
        right.
        rewrite nnrs_imp_stmt_free_vars_readwrite_equiv in Hfv1.
        rewrite nin_app_or in Hfv1.
        destruct Hfv1.
        trivial.
      - Case "NNRSimpAssign"%string.
        unfold olift.
        apply notand in Hfv.
        destruct Hfv as [ Hv Hfv ].
        rewrite (nnrs_imp_expr_to_imp_data_correct h _ _ _ constants); trivial.
        case_eq (imp_data_expr_eval h (σ ++ [(constants, Some (drec σc))]) (nnrs_imp_expr_to_imp_data constants n)).
        + unfold imp_data_expr_eval.
          intros d Hn; rewrite Hn.
          rewrite (lookup_remove_nin); trivial.
          rewrite app_nil_r.
          unfold imp_data_model.
          case_eq (lookup string_dec σ v); try reflexivity.
          intros.
          rewrite update_app_in; try reflexivity.
          apply (lookup_in_domain equiv_dec σ H).
        + unfold imp_data_expr_eval.
          intros Hn; rewrite Hn; try reflexivity.
      - Case "NNRSimpLet"%string.
        unfold olift.
        unfold ImpEval.imp_decls_eval in *.
        apply notand in Hbv.
        destruct Hbv as [ Hv Hbv ].
        destruct o; simpl.
        + rewrite app_or_in_iff in Hfv.
          apply notand in Hfv.
          destruct Hfv as [ Hfvn Hfvs ].
          rewrite (nnrs_imp_expr_to_imp_data_correct _ _ _ _ constants); trivial.
          unfold lift.
          case_eq (imp_data_expr_eval h (σ ++ [(constants, Some (drec σc))]) (nnrs_imp_expr_to_imp_data constants n)).
          * intros d Hn.
            unfold imp_data_expr_eval in *.
            rewrite Hn.
            unfold olift in *.
            rewrite app_comm_cons.
            rewrite <- IHstmt; trivial.
            ** case_eq (nnrs_imp_stmt_eval h σc stmt ((v, Some d) :: σ)).
               *** unfold Var.var.
                   unfold imp_data_model.
                   intros σ' Hs.
                   rewrite Hs.
                   case_eq σ'; try reflexivity.
                   intros Hσ'.
                   rewrite Hσ' in *.
                   apply nnrs_imp_stmt_eval_domain_stack in Hs.
                   simpl in Hs; congruence.
               *** unfold Var.var.
                   unfold imp_data_model.
                   intros Hs.
                   rewrite Hs.
                   reflexivity.
            ** apply (not_in_remove_impl_not_in constants v); trivial.
               congruence.
            ** simpl.
               match_destr.
               congruence.
          * intros Hn.
            unfold imp_data_expr_eval in *.
            rewrite Hn.
            reflexivity.
        + rewrite app_comm_cons.
          rewrite <- IHstmt; trivial.
          * unfold olift.
            case_eq (nnrs_imp_stmt_eval h σc stmt ((v, None) :: σ)).
            ** unfold Var.var.
               unfold imp_data_model.
               intros σ' Hs.
               rewrite Hs.
               case_eq σ'; try reflexivity.
               intros Hσ'.
               rewrite Hσ' in *.
               apply nnrs_imp_stmt_eval_domain_stack in Hs.
               simpl in Hs; congruence.
            ** unfold Var.var.
               unfold imp_data_model.
               intros Hs.
               rewrite Hs.
               reflexivity.
          * apply (not_in_remove_impl_not_in constants v); trivial.
            congruence.
          * simpl.
            match_destr.
            congruence.
      - Case "NNRSimpFor"%string.
        apply notand in Hbv.
        destruct Hbv as [ Hv Hbv ].
        rewrite app_or_in_iff in Hfv.
        apply notand in Hfv.
        destruct Hfv as [ Hfvn Hfvs ].
        rewrite (nnrs_imp_expr_to_imp_data_correct _ _ _ _ constants); trivial.
        unfold imp_data_expr_eval.
        match_destr.
        destruct i; simpl; try reflexivity.
        revert Hσ.
        revert σ.
        induction l; try reflexivity.
        intros σ Hσ.
        unfold olift.
        rewrite app_comm_cons.
        rewrite <- IHstmt; trivial.
        * unfold olift.
          case_eq (nnrs_imp_stmt_eval h σc stmt ((v, Some a) :: σ)).
          ** unfold Var.var in *.
             unfold var in *.
             unfold imp_data_model in *.
             intros σ' Hs.
             rewrite Hs.
             case_eq σ'.
             *** intros Hσ'.
                 rewrite Hσ' in *.
                 apply nnrs_imp_stmt_eval_domain_stack in Hs.
                 simpl in Hs; congruence.
             *** intros p l0 Hσ'. simpl.
                 unfold olift in *.
                 rewrite IHl; trivial.
                 rewrite Hσ' in *; clear Hσ'; clear σ'.
                 apply nnrs_imp_stmt_eval_domain_stack in Hs.
                 apply lookup_nin_none.
                 apply lookup_none_nin in Hσ.
                 rewrite domain_cons in Hs.
                 rewrite domain_cons in Hs.
                 inversion Hs.
                 trivial.
          ** unfold Var.var in *.
             unfold var in *.
             unfold imp_data_model in *.
             intros Hs.
             rewrite Hs.
             reflexivity.
        * apply (not_in_remove_impl_not_in constants v); trivial.
          congruence.
        * simpl.
          match_destr.
          congruence.
      - Case "NNRSimpIf"%string.
        rewrite app_or_in_iff in Hbv.
        apply notand in Hbv.
        destruct Hbv as [ Hbv1 Hbv2 ].
        rewrite app_or_in_iff in Hfv.
        apply notand in Hfv.
        rewrite app_or_in_iff in Hfv.
        destruct Hfv as [ Hfvn Hfvs ].
        apply notand in Hfvs.
        destruct Hfvs as [ Hfvs1 Hfvs2 ].
        rewrite (nnrs_imp_expr_to_imp_data_correct _ _ _ _ constants); auto.
        unfold imp_data_expr_eval.
        match_destr; simpl.
        destruct i; simpl; try reflexivity.
        destruct b; simpl; auto.
      - Case "NNRSimpEither"%string.
        unfold ImpEval.imp_decls_eval in *; simpl.
        rewrite app_or_in_iff in Hbv.
        apply notand in Hbv.
        destruct Hbv as [ Hv Hbv ].
        apply notand in Hbv.
        destruct Hbv as [ Hbv1 Hbv2 ].
        rewrite app_or_in_iff in Hfv.
        apply notand in Hfv.
        rewrite app_or_in_iff in Hfv.
        destruct Hfv as [ Hfvn Hfvs ].
        apply notand in Hfvs.
        destruct Hfvs as [ Hfvs1 Hfvs2 ].
        rewrite (nnrs_imp_expr_to_imp_data_correct _ _ _ _ constants); auto.
        unfold imp_data_expr_eval in *.
        match_destr.
        simpl.
        unfold olift.
        case_eq i; trivial; intros d Hi; clear Hi; clear i; simpl.
        * rewrite app_comm_cons.
          rewrite <- IHstmt1; auto.
          ** unfold olift.
             case_eq (nnrs_imp_stmt_eval h σc stmt1 ((v, Some d) :: σ)).
             *** unfold Var.var in *.
                 unfold imp_data_model in *.
                 unfold NNRSimp.pd_bindings.
                 intros σ' Hs.
                 rewrite Hs.
                 case_eq σ'; try reflexivity.
                 intros Hσ'.
                 rewrite Hσ' in *.
                 apply nnrs_imp_stmt_eval_domain_stack in Hs.
                 simpl in Hs; congruence.
             *** unfold Var.var.
                 unfold imp_data_model.
                 intros Hs.
                 rewrite Hs.
                 reflexivity.
          ** apply (not_in_remove_impl_not_in constants v); congruence.
          ** simpl.
             match_destr.
             congruence.
        * rewrite app_comm_cons.
          rewrite <- IHstmt2; auto.
          ** case_eq (nnrs_imp_stmt_eval h σc stmt2 ((v0, Some d) :: σ)).
             *** unfold olift.
                 unfold Var.var in *.
                 unfold imp_data_model in *.
                 intros σ' Hs.
                 rewrite Hs.
                 case_eq σ'; try reflexivity.
                 intros Hσ'.
                 rewrite Hσ' in *.
                 apply nnrs_imp_stmt_eval_domain_stack in Hs.
                 simpl in Hs; congruence.
             *** unfold Var.var.
                 unfold imp_data_model.
                 intros Hs.
                 rewrite Hs.
                 reflexivity.
          ** apply (not_in_remove_impl_not_in constants v0); try congruence.
             rewrite not_in_cons in Hbv2.
             destruct Hbv2; trivial.
          ** rewrite not_in_cons in Hbv2.
             destruct Hbv2; trivial.
          ** simpl.
             match_destr.
             rewrite not_in_cons in Hbv2.
             destruct Hbv2; trivial.
             congruence.
    Qed.

    Lemma nnrs_imp_to_imp_data_function_correct h (σc:bindings) (q:nnrs_imp) :
      olift id (nnrs_imp_eval h (rec_sort σc) q) =
      imp_data_function_eval h (nnrs_imp_to_imp_data_function q) (drec (rec_sort σc)).
    Proof.
      unfold olift, id.
      elim q; intros stmt ret.
      simpl.
      specialize (fresh_var_fresh "constants" (ret :: nnrs_imp_stmt_free_vars stmt ++ nnrs_imp_stmt_bound_vars stmt)).
      rewrite not_in_cons.
      rewrite nin_app_or.
      set (constants := (fresh_var "constants" (ret :: nnrs_imp_stmt_free_vars stmt ++ nnrs_imp_stmt_bound_vars stmt))).
      intros Hfresh.
      destruct Hfresh as [Hret Hfresh].
      destruct Hfresh as [Hfv Hbv].
      specialize (nnrs_imp_stmt_to_imp_data_correct h (rec_sort σc) [(ret, None)] stmt constants).
      simpl.
      unfold imp_data_stmt_eval.
      unfold Var.var.
      unfold var.
      unfold imp_data_model.
      intros Hstmt.
      rewrite <- Hstmt; clear Hstmt; trivial;
        [ | case (equiv_dec constants ret); congruence ];
        unfold Var.var;
        unfold var;
        unfold imp_data_model.
      unfold olift.
      unfold lift.
      case_eq (nnrs_imp_stmt_eval h (rec_sort σc) stmt [(ret, None)]);
        unfold Var.var;
        unfold var;
        unfold imp_data_model;
        [ | intros Hstmt; rewrite  Hstmt; reflexivity].
      intros σ Hstmt.
      rewrite  Hstmt.
      specialize (nnrs_imp_stmt_eval_domain_stack Hstmt).
      case_eq σ; simpl; try congruence.
      intros p σ' Hσ Hdom.
      destruct p.
      simpl in Hdom.
      inversion Hdom.
      case (equiv_dec s s); try congruence.
    Qed.

    Theorem nnrs_imp_to_imp_data_top_correct h (σc:bindings) (qname: string) (q:nnrs_imp) :
      nnrs_imp_eval_top h σc q =
      imp_data_eval_top h σc (nnrs_imp_to_imp_data_top qname q).
    Proof.
      unfold nnrs_imp_eval_top.
      unfold nnrs_imp_eval.
      unfold imp_data_eval_top.
      unfold imp_data_eval.
      unfold nnrs_imp_to_imp_data_top.
      generalize (nnrs_imp_to_imp_data_function_correct h σc q); intros.
      simpl in *.
      unfold nnrs_imp_eval in *.
      auto.
    Qed.
  End Correctness.

End NNRSimptoImpData.
