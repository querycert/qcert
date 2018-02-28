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

Section NNRCtoNNRCimp.
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
  Require Import cNNRC.
  Require Import NNRC.
  Require Import cNNRCNorm.
  Require Import cNNRCVars.
  Require Import NNRCimpRuntime.
  Require Import NNRCStratify.
  Require Import Fresh.

  Context {fruntime:foreign_runtime}.

  Section from_stratified.

    Fixpoint nnrc_expr_to_nnrc_imp_expr (e: nnrc) :
      option nnrc_imp_expr
      := match e with
         | NNRCGetConstant c => Some (NNRCimpGetConstant c)
         | NNRCVar x => Some (NNRCimpVar x)
         | NNRCConst d => Some (NNRCimpConst d)
         | NNRCBinop b e1 e2 =>
           lift2 (NNRCimpBinop b)
                 (nnrc_expr_to_nnrc_imp_expr e1)
                 (nnrc_expr_to_nnrc_imp_expr e2)
         | NNRCUnop u e1 =>
           lift (NNRCimpUnop u)
                (nnrc_expr_to_nnrc_imp_expr e1)
         | NNRCGroupBy s ls e1 =>
           lift (NNRCimpGroupBy s ls)
                (nnrc_expr_to_nnrc_imp_expr e1)
         | _ => None
         end.

    Lemma nnrc_expr_to_nnrc_imp_expr_stratified_some e :
      stratifiedLevel nnrcExpr e  ->
      { e' | nnrc_expr_to_nnrc_imp_expr e = Some e'}.
    Proof.
      induction e; simpl; intuition; eauto 2; try discriminate.
      - destruct H; destruct H2.
        rewrite e, e0.
        simpl; eauto.
      - destruct H0.
        rewrite e0.
        simpl; eauto.
    Defined.

    Definition stratified_nnrc_expr_to_nnrc_imp_expr (e:nnrc)
               (strate:stratifiedLevel nnrcExpr e) : nnrc_imp_expr
      := proj1_sig (nnrc_expr_to_nnrc_imp_expr_stratified_some e strate).

    Definition pd_bindings_lift (σ:bindings) : pd_bindings
      := map_codomain Some σ.

    Lemma lookup_pd_bindings_lift σ v :
      lookup equiv_dec (pd_bindings_lift σ) v = lift Some (lookup equiv_dec σ v).
    Proof.
      apply lookup_map_codomain.
    Qed.

    Lemma nnrc_expr_to_nnrc_imp_expr_some_correct (e:nnrc) (ei:nnrc_imp_expr) :
      nnrc_expr_to_nnrc_imp_expr e = Some ei ->
      forall h σc σ,
        @nnrc_eval _ h σc σ e = nnrc_imp_expr_eval h σc (pd_bindings_lift σ) ei.
    Proof.
      revert ei.
      unfold nnrc_eval.
      induction e; intros ei eqq h σc σ; try solve [invcs eqq; simpl; trivial].
      - invcs eqq; simpl; trivial.
        rewrite lookup_pd_bindings_lift; simpl.
        rewrite olift_id_lift_some; trivial.
      - simpl in eqq; trivial.
        apply some_lift2 in eqq.
        destruct eqq as [?[??[??]]]; subst; simpl.
        f_equal; auto.
      - simpl in eqq.
        apply some_lift in eqq.
        destruct eqq as [??]; subst; simpl.
        f_equal; auto.
      - simpl in eqq.
        apply some_lift in eqq.
        destruct eqq as [??]; subst.
        simpl nnrc_to_nnrc_base.
        simpl nnrc_imp_expr_eval.
        rewrite <- (IHe _ e0).
        case_eq (nnrc_core_eval h σc σ (nnrc_to_nnrc_base e));
          [intros ? eqq | intros eqq].
        + destruct d; try solve [simpl; rewrite eqq; trivial].
          apply nnrc_group_by_correct; trivial.
        + simpl.
          rewrite eqq; trivial.
    Qed.

    Inductive terminator :=
    | Term_assign : var -> terminator
    | Term_push : var -> terminator
    .

    Definition terminate (terminator: terminator) (e: nnrc_imp_expr) :=
      match terminator with
      | Term_assign result => NNRCimpAssign result e
      | Term_push result => NNRCimpPush result e
      end.

    Fixpoint nnrc_stmt_to_nnrc_imp_stmt_aux (fvs: list var) (terminator: terminator) (stmt: nnrc) :
      option nnrc_imp_stmt
      := match stmt with
         | NNRCLet v s1 s2 =>
           match nnrc_stmt_to_nnrc_imp_stmt_aux (v::fvs) (Term_assign v) s1,
                 nnrc_stmt_to_nnrc_imp_stmt_aux (v::fvs) terminator s2
           with
           | Some s1', Some s2' =>
             Some (NNRCimpLetMut v s1' s2')
           | _, _ => None
           end
         | NNRCFor v e s =>
           let tmp := fresh_var "tmp" fvs in
           match nnrc_expr_to_nnrc_imp_expr e,
                 nnrc_stmt_to_nnrc_imp_stmt_aux (tmp::v::fvs) (Term_push tmp) s
           with
           | Some e', Some s' =>
             Some (NNRCimpLetMut
                     tmp
                     (NNRCimpFor v e' s')
                     (terminate terminator (NNRCimpVar tmp)))
           | _, _ => None
           end
         | NNRCIf e s1 s2 =>
           let tmp := fresh_var "tmp" fvs in
           match nnrc_expr_to_nnrc_imp_expr e,
                 nnrc_stmt_to_nnrc_imp_stmt_aux (tmp::fvs) (Term_assign tmp) s1,
                 nnrc_stmt_to_nnrc_imp_stmt_aux (tmp::fvs) (Term_assign tmp) s2
           with
           | Some e', Some s1', Some s2' =>
             Some (NNRCimpLetMut
                     tmp 
                        (NNRCimpIf e' s1' s2')
                        (terminate terminator (NNRCimpVar tmp)))
           | _, _, _ => None
           end
         | NNRCEither e x1 s1 x2 s2 =>
           let tmp := fresh_var "tmp" fvs in
           match nnrc_expr_to_nnrc_imp_expr e,
                 nnrc_stmt_to_nnrc_imp_stmt_aux (tmp::x1::fvs) (Term_assign tmp) s1,
                 nnrc_stmt_to_nnrc_imp_stmt_aux (tmp::x2::fvs) (Term_assign tmp) s2
           with
           | Some e', Some s1', Some s2' =>
             Some (NNRCimpLetMut
                     tmp 
                        (NNRCimpEither e' x1 s1' x2 s2')
                        (terminate terminator (NNRCimpVar tmp)))
           | _, _, _ => None
           end
         | NNRCGroupBy _ _ _
         | NNRCGetConstant _
         | NNRCVar _
         | NNRCConst _
         | NNRCBinop _ _ _
         | NNRCUnop _ _ =>
           match nnrc_expr_to_nnrc_imp_expr stmt with
           | Some e => Some (terminate terminator e)
           | None => None
           end
         end.

    Definition nnrc_stmt_to_nnrc_imp_stmt (globals: list var) (stmt: nnrc) :
      option (nnrc_imp_stmt * var)
      :=
        let ret := fresh_var "ret" globals in
        match nnrc_stmt_to_nnrc_imp_stmt_aux (ret::globals) (Term_assign ret) stmt with
        | Some stmt => Some (stmt, ret)
        | None => None
        end.

    Definition nnrc_stratified_to_nnrc_imp_top (globals: list var) (q: nnrc) :
      option nnrc_imp
      :=
        nnrc_stmt_to_nnrc_imp_stmt globals q.

    Lemma nnrc_stmt_to_nnrc_imp_stmt_aux_stratified_some fvs term s :
      stratifiedLevel nnrcStmt s  ->
      { s' | nnrc_stmt_to_nnrc_imp_stmt_aux fvs term s = Some s'}.
    Proof.
      revert fvs term;
        induction s; intros fvs term; simpl; intuition; eauto 2; try discriminate
        ; try unfold nnrc_stmt_to_nnrc_imp_stmt; simpl; eauto 2.
      - destruct (nnrc_expr_to_nnrc_imp_expr_stratified_some _ H0) as [e1 eqe1].
        destruct (nnrc_expr_to_nnrc_imp_expr_stratified_some _ H1) as [e2 eqe2].
        rewrite eqe1, eqe2; simpl.
        eauto 2.
      - destruct (nnrc_expr_to_nnrc_imp_expr_stratified_some _ H) as [e eqe].
        rewrite eqe; simpl.
        eauto 2.
      - destruct (IHs1 (v :: fvs) (Term_assign v) H)  as [s1' eqs1'].
        destruct (IHs2 (v :: fvs) term H2)  as [s2' eqs2'].
        rewrite eqs1', eqs2'; simpl.
        eauto 2.
      - destruct (nnrc_expr_to_nnrc_imp_expr_stratified_some _ H) as [e1 eqe1].
        destruct (IHs2 (fresh_var "tmp" fvs :: v :: fvs)
                       (Term_push (fresh_var "tmp" fvs)) H2)  as [s1' eqs1'].
        rewrite eqe1, eqs1'; simpl.
        eauto 2.
      - destruct (nnrc_expr_to_nnrc_imp_expr_stratified_some _ H) as [e1 eqe1].
        destruct (IHs2 (fresh_var "tmp" fvs :: fvs)
                       (Term_assign (fresh_var "tmp" fvs)) H1)  as [s2' eqs2'].
        destruct (IHs3 (fresh_var "tmp" fvs :: fvs)
                       (Term_assign (fresh_var "tmp" fvs)) H3)  as [s3' eqs3'].
        rewrite eqe1, eqs2', eqs3'; simpl.
        eauto 2.
      - destruct (nnrc_expr_to_nnrc_imp_expr_stratified_some _ H) as [e1 eqe1].
        destruct (IHs2 (fresh_var "tmp" fvs :: v :: fvs)
                       (Term_assign (fresh_var "tmp" fvs)) H1)  as [s2' eqs2'].
        destruct (IHs3 (fresh_var "tmp" fvs :: v0 :: fvs)
                       (Term_assign (fresh_var "tmp" fvs)) H3)  as [s3' eqs3'].
        rewrite eqe1, eqs2', eqs3'; simpl.
        eauto 2.
      - destruct (nnrc_expr_to_nnrc_imp_expr_stratified_some _ H1) as [e1 eqe1].
        rewrite eqe1; simpl.
        eauto 2.
    Defined.

    Lemma nnrc_stmt_to_nnrc_imp_stmt_stratified_some fvs s :
      stratifiedLevel nnrcStmt s  ->
      { s' | nnrc_stmt_to_nnrc_imp_stmt fvs s = Some s'}.
    Proof.
      case_eq (nnrc_stmt_to_nnrc_imp_stmt fvs s).
      - eauto.
      - unfold nnrc_stmt_to_nnrc_imp_stmt.
        intros cpf strats.
        destruct (nnrc_stmt_to_nnrc_imp_stmt_aux_stratified_some
                    ((fresh_var "ret" fvs)::fvs)
                    (Term_assign (fresh_var "ret" fvs)) _ strats) as [s' eqs'].
      rewrite eqs' in cpf.
      eauto 2.
    Defined.
    
    Definition stratified_nnrc_stmt_to_nnrc_imp_stmt fvs (s:nnrc)
               (strats:stratifiedLevel nnrcStmt s) : nnrc_imp
      := proj1_sig (nnrc_stmt_to_nnrc_imp_stmt_stratified_some fvs s strats).

    Definition nnrc_to_nnrc_imp_top (globals: list var) (q: nnrc) :
      nnrc_imp
      := let nnrc_stratified := NNRCStratify.stratify q in
         let nnrc_stratified_pf := NNRCStratify.stratify_stratified q in
         stratified_nnrc_stmt_to_nnrc_imp_stmt globals nnrc_stratified nnrc_stratified_pf.

  End from_stratified.

End NNRCtoNNRCimp.
