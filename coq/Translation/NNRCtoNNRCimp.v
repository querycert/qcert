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

    Corollary nnrc_expr_to_nnrc_imp_expr_some_correct'
              (e:nnrc) (ei:nnrc_imp_expr) :
      nnrc_expr_to_nnrc_imp_expr e = Some ei ->
      forall h σc σ,
        @nnrc_core_eval _ h σc σ (nnrc_to_nnrc_base e) = nnrc_imp_expr_eval h σc (pd_bindings_lift σ) ei.
    Proof.
      apply nnrc_expr_to_nnrc_imp_expr_some_correct.
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
           match nnrc_stmt_to_nnrc_imp_stmt_aux fvs (Term_assign v) s1,
                 nnrc_stmt_to_nnrc_imp_stmt_aux fvs terminator s2
           with
           | Some s1', Some s2' =>
             Some (NNRCimpLetMut v s1' s2')
           | _, _ => None
           end
         | NNRCFor v e s =>
           let tmp := fresh_var "tmp" fvs in
           match nnrc_expr_to_nnrc_imp_expr e,
                 nnrc_stmt_to_nnrc_imp_stmt_aux (tmp::fvs) (Term_push tmp) s
           with
           | Some e', Some s' =>
             Some (NNRCimpLetMutColl
                     tmp
                     (NNRCimpFor v e' s')
                     (terminate terminator (NNRCimpVar tmp)))
           | _, _ => None
           end
         | NNRCIf e s1 s2 =>
           match nnrc_expr_to_nnrc_imp_expr e,
                 nnrc_stmt_to_nnrc_imp_stmt_aux fvs terminator s1,
                 nnrc_stmt_to_nnrc_imp_stmt_aux fvs terminator s2
           with
           | Some e', Some s1', Some s2' =>
             Some (NNRCimpIf e' s1' s2')
           | _, _, _ => None
           end
         | NNRCEither e x1 s1 x2 s2 =>
           match nnrc_expr_to_nnrc_imp_expr e,
                 nnrc_stmt_to_nnrc_imp_stmt_aux fvs terminator s1,
                 nnrc_stmt_to_nnrc_imp_stmt_aux fvs terminator s2
           with
           | Some e', Some s1', Some s2' =>
             Some (NNRCimpEither e' x1 s1' x2 s2')
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
        let fvs := globals ++ nnrc_bound_vars stmt in
        let ret := fresh_var "ret" fvs in
        match nnrc_stmt_to_nnrc_imp_stmt_aux (ret::fvs) (Term_assign ret) stmt with
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
      - destruct (IHs1 fvs (Term_assign v) H)  as [s1' eqs1'].
        destruct (IHs2 fvs term H2)  as [s2' eqs2'].
        rewrite eqs1', eqs2'; simpl.
        eauto 2.
      - destruct (nnrc_expr_to_nnrc_imp_expr_stratified_some _ H) as [e1 eqe1].
        destruct (IHs2 (fresh_var "tmp" fvs :: fvs)
                       (Term_push (fresh_var "tmp" fvs)) H2)  as [s1' eqs1'].
        rewrite eqe1, eqs1'; simpl.
        eauto 2.
      - destruct (nnrc_expr_to_nnrc_imp_expr_stratified_some _ H) as [e1 eqe1].
        destruct (IHs2 fvs term H1)  as [s2' eqs2'].
        destruct (IHs3 fvs term H3)  as [s3' eqs3'].
        rewrite eqe1, eqs2', eqs3'; simpl.
        eauto 2.
      - destruct (nnrc_expr_to_nnrc_imp_expr_stratified_some _ H) as [e1 eqe1].
        destruct (IHs2 fvs term H1)  as [s2' eqs2'].
        destruct (IHs3 fvs term H3)  as [s3' eqs3'].
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
                    ((fresh_var "ret" (fvs ++ nnrc_bound_vars s))::fvs ++ nnrc_bound_vars s)
                    (Term_assign (fresh_var "ret" (fvs ++ nnrc_bound_vars s))) _ strats) as [s' eqs'].
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

    (* Given a terminator and the returned states, 
       determine what value was computed by the statement 
     *)
    
    Definition get_terminator_result
               (term:terminator)
               (mc:mc_bindings)
               (md:pd_bindings) : option data :=
      match term with
      | Term_assign v => olift id (lookup equiv_dec md v)
      | Term_push v =>
        match lookup equiv_dec mc v with
        | Some xl => match rev xl with
                     | x::xs => Some x
                     | _ => None
                     end
        | _ => None
        end
      end.

    Definition safe_terminator_result
               (term:terminator)
               (mc:mc_bindings)
               (md:pd_bindings) : Prop :=
      match term with
      | Term_assign v => In v (domain md)
      | Term_push v => In v (domain mc)
      end.
    
    Lemma nnrc_imp_stmt_eval_terminator h σc pd mc md term e :
      safe_terminator_result term mc md ->
      match nnrc_imp_stmt_eval h σc pd mc md (terminate term e) with
      | Some (pd', mc', md') =>
        match get_terminator_result term mc' md' with
        | Some res => nnrc_imp_expr_eval h σc pd e = Some res
        | None => False
        end
      | None => nnrc_imp_expr_eval h σc pd e = None
      end.
    Proof.
      destruct term; simpl; intros inn;
        destruct (in_dom_lookup string_dec inn) as [dd eqdd];
        rewrite eqdd
        ; destruct (nnrc_imp_expr_eval h σc pd e); simpl; trivial
        ; replace string_dec with
              (@equiv_dec string (@eq string) (@eq_equivalence string) string_eqdec) by trivial
        ;  rewrite lookup_update_eq_in by trivial
        ; simpl; trivial.
      rewrite rev_app_distr; simpl; trivial.
    Qed.

    Lemma nnrc_expr_to_nnrc_imp_expr_free_vars e ei :
      nnrc_expr_to_nnrc_imp_expr e = Some ei ->
      nnrc_free_vars e = nnrc_imp_expr_free_vars ei.
    Proof.
      revert ei.
      induction e; simpl; intros ei eqq; invcs eqq; simpl; trivial.
      - apply some_lift2 in H0.
        destruct H0 as [? [??[??]]]; subst; simpl.
        erewrite IHe1 by eauto.
        erewrite IHe2 by eauto.
        trivial.
      - apply some_lift in H0.
        destruct H0 as [???]; subst; simpl.
        eauto.
      - apply some_lift in H0.
        destruct H0 as [???]; subst; simpl.
        eauto.
    Qed.

    Local Open Scope string.
    Require Import List.

    Ltac expr_push_finisher ev x
      := match_destr_in ev
         ; simpl in ev
         ; destruct (string_dec x x); [| congruence]
         ; invcs ev
         ; eauto.
    
    Lemma nnrc_stmt_to_nnrc_imp_stmt_aux_push1_assign_eq_mc 
          s {si:nnrc_imp_stmt} {h σc pd mc md pd' mc' md'}:
      nnrc_imp_stmt_eval h σc pd mc md si = Some (pd', mc', md') ->
      (forall x fvs, nnrc_stmt_to_nnrc_imp_stmt_aux fvs (Term_push x) s = Some si ->
                     forall mc2 old, mc = (x,old)::mc2 ->
                                     exists n, mc' = ((x,old++n::nil)::mc2))
      /\ 
      (forall x fvs, nnrc_stmt_to_nnrc_imp_stmt_aux fvs (Term_assign x) s = Some si ->
                     mc' = mc).
    Proof.
      revert si pd mc md pd' mc' md'.
      nnrc_cases (induction s) Case;
        intros si pd mc md pd' mc' md' ev;
        (split; intros x fvs eqsi
         ; [ intros mc2 old ?; subst; rename mc2 into mc | ])
        ; simpl in eqsi; invcs eqsi
        ; try solve [unfold nnrc_imp_stmt_eval in ev
                     ; expr_push_finisher ev x
                    | unfold nnrc_imp_stmt_eval in ev
                      ; repeat match_destr_in ev
                      ; invcs ev; trivial].
      - Case "NNRCBinop".
        match_option_in H0; try congruence.
        apply some_lift2 in eqq.
        destruct eqq as [?[? eqq1 [eqq2 H3]]].
        invcs H0.
        simpl in ev.
        expr_push_finisher ev x.
      - Case "NNRCBinop".
        match_option_in H0.
        invcs H0.
        simpl in ev.
        repeat match_option_in ev; try congruence.
      - Case "NNRCUnop".
        match_option_in H0.
        apply some_lift in eqq.
        destruct eqq as [? eq1 ?].
        invcs H0.
        simpl in ev.
        expr_push_finisher ev x.
      - Case "NNRCUnop".
        match_option_in H0.
        invcs H0.
        simpl in ev.
        repeat match_option_in ev; try congruence.
      - Case "NNRCLet".
        repeat match_option_in H0.
        invcs H0.
        simpl in ev.
        repeat match_option_in ev.
        destruct p as [[??]?].
        destruct m0; try discriminate.
        destruct p0.
        repeat match_option_in ev.
        destruct p0 as [[??]?].
        destruct p0; try discriminate.
        invcs ev.
        destruct (IHs1 _ _ _ _ _ _ _ eqq1) as [IHs1p IHs1e].
        destruct (IHs2 _ _ _ _ _ _ _ eqq2) as [IHs2p IHs2e].
        eauto.
      - Case "NNRCLet".
        repeat match_option_in H0.
        invcs H0.
        simpl in ev.
        repeat match_option_in ev.
        destruct p as [[??]?].
        destruct m0; try discriminate.
        destruct p0.
        repeat match_option_in ev.
        destruct p0 as [[??]?].
        destruct p0; try discriminate.
        invcs ev.
        destruct (IHs1 _ _ _ _ _ _ _ eqq1) as [IHs1p IHs1e].
        destruct (IHs2 _ _ _ _ _ _ _ eqq2) as [IHs2p IHs2e].
        specialize (IHs1e _ _ eqq).
        specialize (IHs2e _ _ eqq0).
        congruence.
      - Case "NNRCFor".
        repeat match_option_in H0.
        invcs H0.
        simpl in ev.
        repeat match_option_in ev.
        destruct p as [[??]?].
        destruct m; try discriminate.
        destruct p0.
        repeat match_option_in ev.
        destruct p0 as [[??]?].
        destruct p0; try discriminate.
        invcs ev.
        destruct (equiv_dec (fresh_var "tmp" fvs) (fresh_var "tmp" fvs)); try congruence.
        clear e.
        unfold id in eqq2; simpl in eqq2.
        match_option_in eqq2.
        invcs eqq2.
        match_option_in eqq1.
        destruct d; try discriminate.
        clear IHs1.
        specialize (IHs2 n0).

        cut ((forall l old s pd mc md pd' m md',
                 (fix
                  for_fun (dl : list data) (σ₁ : list (var * option data)) 
                  (ψc₁ : mc_bindings) (ψd₁ : md_bindings) {struct dl} :
                  option (list (var * option data) * mc_bindings * md_bindings) :=
                  match dl with
                  | nil => Some (σ₁, ψc₁, ψd₁)
                  | d :: dl' =>
                    match nnrc_imp_stmt_eval h σc ((v, Some d) :: σ₁) ψc₁ ψd₁ n0 with
                    | Some (nil, _, _) => None
                    | Some (_ :: σ₂, ψc₂, ψd₂) => for_fun dl' σ₂ ψc₂ ψd₂
                    | None => None
                    end
                  end) l1 pd ((fresh_var "tmp" fvs, old) :: mc) md =
               Some (pd', (s, l) :: m, md') ->
                 exists n : list data, (s,l)::m = (fresh_var "tmp" fvs, old ++ n) :: mc)).
        + intros HH.
          apply (HH l nil) in eqq1.
          destruct eqq1 as [? eqq5].
          invcs eqq5.
          simpl.
          simpl in eqq3.
          destruct (string_dec x x); [ | congruence].
          invcs eqq3.
          eauto.
        + {
            clear l pd pd' md md' old mc s n m l0 eqq1 eqq eqq2 eqq3.
            induction l1; simpl; intros l old s pd mc md pd' m md' eqsi.
            - invcs eqsi.
              exists nil.
              rewrite app_nil_r.
              trivial.
            - match_option_in eqsi.
              destruct p as [[??]?].
              destruct p; try discriminate.
              specialize (IHs2 _ _ _ _ _ _ eqq).
              destruct IHs2 as [IHs2p IHs2e].
              specialize (IHs2p _ _ eqq0).
              specialize (IHs2p _ _ (eq_refl)).
              destruct IHs2p as [??]; subst.
              specialize (IHl1 _ _ _ _ _ _ _ _ _ eqsi).
              destruct IHl1 as [? eqq1].
              invcs eqq1.
              exists (x0::x1).
              rewrite app_ass; simpl; trivial.
            }
      - Case "NNRCFor".
        repeat match_option_in H0.
        invcs H0.
        simpl in ev.
        repeat match_option_in ev.
        destruct p as [[??]?].
        destruct m; try discriminate.
        destruct p0.
        repeat match_option_in ev.
        destruct p0 as [[??]?].
        destruct p0; try discriminate.
        invcs ev.
        destruct (equiv_dec (fresh_var "tmp" fvs) (fresh_var "tmp" fvs)); try congruence.
        clear e.
        unfold id in eqq2; simpl in eqq2.
        match_option_in eqq2.
        invcs eqq2.
        match_option_in eqq1.
        destruct d; try discriminate.
        clear IHs1.
        specialize (IHs2 n0).

        cut ((forall l old s pd mc md pd' m md',
                 (fix
                  for_fun (dl : list data) (σ₁ : list (var * option data)) 
                  (ψc₁ : mc_bindings) (ψd₁ : md_bindings) {struct dl} :
                  option (list (var * option data) * mc_bindings * md_bindings) :=
                  match dl with
                  | nil => Some (σ₁, ψc₁, ψd₁)
                  | d :: dl' =>
                    match nnrc_imp_stmt_eval h σc ((v, Some d) :: σ₁) ψc₁ ψd₁ n0 with
                    | Some (nil, _, _) => None
                    | Some (_ :: σ₂, ψc₂, ψd₂) => for_fun dl' σ₂ ψc₂ ψd₂
                    | None => None
                    end
                  end) l0 pd ((fresh_var "tmp" fvs, old) :: mc) md =
                 Some (pd', (s, l) :: m, md') ->
                 exists n : list data, (s,l)::m = (fresh_var "tmp" fvs, old ++ n) :: mc)).
        + intros HH.
          apply (HH l nil) in eqq1.
          destruct eqq1 as [? eqq5].
          invcs eqq5.
          simpl.
          simpl in eqq3.
          destruct (string_dec x x); [ | congruence].
          invcs eqq3.
          eauto.
        +
            clear l pd pd' md m0 mc s n eqq1 eqq eqq2 eqq3. 
          {
            induction l0; simpl; intros l old s pd mc md pd' m md' eqsi.
            - invcs eqsi.
              exists nil.
              rewrite app_nil_r.
              trivial.
            - match_option_in eqsi.
              destruct p as [[??]?].
              destruct p; try discriminate.
              specialize (IHs2 _ _ _ _ _ _ eqq).
              destruct IHs2 as [IHs2p IHs2e].
              specialize (IHs2p _ _ eqq0).
              specialize (IHs2p _ _ (eq_refl)).
              destruct IHs2p as [??]; subst.
              specialize (IHl0 _ _ _ _ _ _ _ _ _ eqsi).
              destruct IHl0 as [? eqq1].
              invcs eqq1.
              exists (x0::x1).
              rewrite app_ass; simpl; trivial.
            }
      - Case "NNRCIf".
        repeat match_option_in H0.
        invcs H0.
        simpl in ev.
        repeat match_option_in ev.
        destruct d; try discriminate.
        destruct b.
        + destruct (IHs2 _ _ _ _ _ _ _ ev) as [IHs2p IHs2e]; eauto.
        + destruct (IHs3 _ _ _ _ _ _ _ ev) as [IHs3p IHs3e]; eauto.
      - Case "NNRCIf".
        repeat match_option_in H0.
        invcs H0.
        simpl in ev.
        repeat match_option_in ev.
        destruct d; try discriminate.
        destruct b.
        + destruct (IHs2 _ _ _ _ _ _ _ ev) as [IHs2p IHs2e]; eauto.
        + destruct (IHs3 _ _ _ _ _ _ _ ev) as [IHs3p IHs3e]; eauto.
      - Case "NNRCEither".
        repeat match_option_in H0.
        invcs H0.
        simpl in ev.
        repeat match_option_in ev.
        destruct d; try discriminate
        ; repeat match_option_in ev
        ; destruct p as [[??]?]; destruct p; try discriminate
        ; invcs ev.
        + destruct (IHs2 _ _ _ _ _ _ _ eqq3) as [IHs2p IHs2e]; eauto.
        + destruct (IHs3 _ _ _ _ _ _ _ eqq3) as [IHs3p IHs3e]; eauto.
      - Case "NNRCEither".
        repeat match_option_in H0.
        invcs H0.
        simpl in ev.
        repeat match_option_in ev.
        destruct d; try discriminate
        ; repeat match_option_in ev
        ; destruct p as [[??]?]; destruct p; try discriminate
        ; invcs ev.
        + destruct (IHs2 _ _ _ _ _ _ _ eqq3) as [IHs2p IHs2e]; eauto.
        + destruct (IHs3 _ _ _ _ _ _ _ eqq3) as [IHs3p IHs3e]; eauto.
      - Case "NNRCGroupBy".
        match_option_in H0.
        invcs H0.
        unfold nnrc_imp_stmt_eval in ev.
        expr_push_finisher ev x.
      - Case "NNRCGroupBy".
        match_option_in H0.
        invcs H0.
        unfold nnrc_imp_stmt_eval in ev.
        repeat match_destr_in ev.
        invcs ev; trivial.
    Qed.

    Lemma nnrc_stmt_to_nnrc_imp_stmt_aux_assign_eq 
          {s:nnrc} {fvs} {si:nnrc_imp_stmt} {h σc pd mc md x pd' mc' md'}:
      nnrc_imp_stmt_eval h σc pd mc md si = Some (pd', mc', md') ->
      nnrc_stmt_to_nnrc_imp_stmt_aux fvs (Term_assign x) s = Some si ->
      mc' = mc.
    Proof.
      intros eqsi ev.
      destruct (nnrc_stmt_to_nnrc_imp_stmt_aux_push1_assign_eq_mc s eqsi).
      eauto.
    Qed.
    
    Lemma nnrc_stmt_to_nnrc_imp_stmt_aux_push1 
          {s:nnrc} {fvs} {si:nnrc_imp_stmt} {h σc pd mc md x pd' mc' md' old}:
      nnrc_imp_stmt_eval h σc pd ((x,old)::mc) md si = Some (pd', mc', md') ->
      nnrc_stmt_to_nnrc_imp_stmt_aux fvs (Term_push x) s = Some si ->
      exists n, mc' = ((x,old++n::nil)::mc).
    Proof.
      intros eqsi ev.
      destruct (nnrc_stmt_to_nnrc_imp_stmt_aux_push1_assign_eq_mc s eqsi).
      eauto.
    Qed.

    Lemma nnrc_stmt_to_nnrc_imp_stmt_aux_some_correct
          {s:nnrc} {fvs term} {si:nnrc_imp_stmt} :
      nnrc_stmt_to_nnrc_imp_stmt_aux fvs term s = Some si ->
      forall h σc σ mc md,
        incl (domain σ) fvs ->
        incl (domain mc) fvs ->
        incl (nnrc_bound_vars s) fvs ->
        safe_terminator_result term mc md ->
        let ne := @nnrc_eval _ h σc σ s in
        match nnrc_imp_stmt_eval h σc (pd_bindings_lift σ) mc md si with
        | None => ne = None
        | Some (pd', mc', md') =>
          match get_terminator_result term mc' md' with
          | Some res => ne = Some res
          | None => False
          end
        end.
    Proof.
      unfold nnrc_eval.
      intros eqsi h σc.
      revert fvs term si eqsi; simpl.
      nnrc_cases (induction s) Case; intros fvs term si eqsi σ mc md inclσ inclmc inclbvars safe_term.
      - Case "NNRCGetConstant".
        invcs eqsi; simpl; intros.
        apply nnrc_imp_stmt_eval_terminator; trivial.
      - Case "NNRCVar".
        invcs eqsi.
        generalize (nnrc_imp_stmt_eval_terminator h σc (pd_bindings_lift σ) mc md term (NNRCimpVar v) safe_term); intros eterm.
        match_destr; simpl in *.
        + destruct p as [[??]?].
          match_destr.
          rewrite lookup_pd_bindings_lift, olift_id_lift_some in eterm; trivial.
        + rewrite lookup_pd_bindings_lift, olift_id_lift_some in eterm; trivial.
      - Case "NNRCConst".
        invcs eqsi.
        apply nnrc_imp_stmt_eval_terminator; trivial.
      - Case "NNRCBinop".
        simpl in *.
        case_eq (nnrc_expr_to_nnrc_imp_expr s1); [intros s1' s1'eq | intros s1'eq]
        ; rewrite s1'eq in eqsi; try discriminate.
        case_eq (nnrc_expr_to_nnrc_imp_expr s2); [intros s2' s2'eq | intros s2'eq]
        ; rewrite s2'eq in eqsi; try discriminate.
        simpl in eqsi; invcs eqsi.
        generalize (nnrc_imp_stmt_eval_terminator h σc (pd_bindings_lift σ) mc md term (NNRCimpBinop b s1' s2') safe_term); intros eterm.
        rewrite (nnrc_expr_to_nnrc_imp_expr_some_correct' _ _ s1'eq).
        rewrite (nnrc_expr_to_nnrc_imp_expr_some_correct' _ _ s2'eq).
        eauto.
      - Case "NNRCUnop".
        simpl in *.
        case_eq (nnrc_expr_to_nnrc_imp_expr s); [intros s1' s1'eq | intros s1'eq]
        ; rewrite s1'eq in eqsi; try discriminate.
        simpl in eqsi; invcs eqsi.
        generalize (nnrc_imp_stmt_eval_terminator h σc (pd_bindings_lift σ) mc md term (NNRCimpUnop u s1' ) safe_term); intros eterm.
        rewrite (nnrc_expr_to_nnrc_imp_expr_some_correct' _ _ s1'eq).
        eauto.
      - Case "NNRCLet".
        simpl in *.
        match_case_in eqsi; [ intros ? eqq1 | intros eqq1]
        ; rewrite eqq1 in eqsi; try discriminate.
        match_case_in eqsi; [ intros ? eqq2 | intros eqq2]
        ; rewrite eqq2 in eqsi; try discriminate.
        invcs eqsi; simpl.
        specialize (IHs1 _ _ _ eqq1).
        specialize (IHs1 σ mc ((v, None) :: md)).
        cut_to IHs1; simpl; eauto 4.
        + match_case_in IHs1; [intros ? eqq3 | intros eqq3]
          ; rewrite eqq3 in IHs1; [ | rewrite IHs1; trivial].
          destruct p as [[??]?].
          simpl in IHs1.
          match_case_in IHs1; [intros ? eqq4 | intros eqq4]
          ; rewrite eqq4 in IHs1; [| tauto].
          unfold id in eqq4; apply some_olift in eqq4; simpl in eqq4.
          destruct eqq4 as [? eqq4 ?]; subst.
          rewrite IHs1.
          generalize (nnrc_imp_stmt_eval_env_stack eqq3); intros; subst.
          generalize (nnrc_imp_stmt_eval_mcenv_domain_stack eqq3); intros eqq5.
          generalize (nnrc_imp_stmt_eval_mdenv_domain_stack eqq3); intros eqq6.
          destruct m0; simpl in *; try discriminate.
          destruct p; simpl in *.
          invcs eqq6.
          match_destr_in eqq4; [clear e | congruence].
          invcs eqq4.
          specialize (IHs2 _ _ _ eqq2).
          specialize (IHs2 ((s, d) :: σ) m m0).
          cut_to IHs2.
          * {
              match_case_in IHs2; [intros ? eqq7 | intros eqq7]
              ; rewrite eqq7 in IHs2; simpl in eqq7
              ; unfold var in *; rewrite eqq7; trivial.
              destruct p as [[??]?].
              match_case_in IHs2;
                [intros ? eqq8 | intros eqq8]
                ; rewrite eqq8 in IHs2; try tauto.
              rewrite IHs2.
              generalize (nnrc_imp_stmt_eval_env_stack eqq7); intros; subst.
              rewrite eqq8; trivial.
            }
          * simpl; intuition.
          * unfold var in *.
            rewrite <- eqq5; trivial.
          * unfold incl in *; simpl in inclbvars.
            intros ??; apply inclbvars.
            rewrite in_app_iff; intuition.
          * unfold safe_terminator_result in *.
            rewrite <- eqq5.
            rewrite <- H1.
            trivial.
        + unfold incl in *; simpl in inclbvars.
          intros ??; apply inclbvars.
          rewrite in_app_iff; intuition.
      - Case "NNRCFor".
        simpl in *.
        case_eq (nnrc_expr_to_nnrc_imp_expr s1); [intros s1' s1'eq | intros s1'eq]
        ; rewrite s1'eq in eqsi; try discriminate.
        rewrite (nnrc_expr_to_nnrc_imp_expr_some_correct' _ _ s1'eq).
        match_case_in eqsi; [ intros ? eqq1 | intros eqq1]
        ; rewrite eqq1 in eqsi; try discriminate.
        invcs eqsi.
        simpl.
        destruct (nnrc_imp_expr_eval h σc (pd_bindings_lift σ) s1'); trivial.
        destruct d; trivial.
        clear s1' IHs1 s1'eq.
        specialize (IHs2 _ _ _ eqq1).

        cut (forall old, match
                  match
                    (fix
                       for_fun (dl : list data) (σ₁ : list (var * option data)) 
                       (ψc₁ : mc_bindings) (ψd₁ : md_bindings) {struct dl} :
                       option (list (var * option data) * mc_bindings * md_bindings) :=
                       match dl with
                       | nil => Some (σ₁, ψc₁, ψd₁)
                       | d :: dl' =>
                         match nnrc_imp_stmt_eval h σc ((v, Some d) :: σ₁) ψc₁ ψd₁ n with
                         | Some (nil, _, _) => None
                         | Some (_ :: σ₂, ψc₂, ψd₂) => for_fun dl' σ₂ ψc₂ ψd₂
                         | None => None
                         end
                       end) l (pd_bindings_lift σ) ((fresh_var "tmp" fvs, old) :: mc) md
                  with
                  | Some (σ₁, nil, _) => None
                  | Some (σ₁, (_, dl) :: ψc₁, ψd₁) =>
                    match
                      nnrc_imp_stmt_eval h σc ((fresh_var "tmp" fvs, Some (dcoll dl)) :: σ₁) ψc₁ ψd₁
                                         (terminate term (NNRCimpVar (fresh_var "tmp" fvs)))
                    with
                    | Some (nil, _, _) => None
                    | Some (_ :: σ₂, ψc₂, ψd₂) => Some (σ₂, ψc₂, ψd₂)
                    | None => None
                    end
                  | None => None
                  end
                with
                | Some (_, mc', md') =>
                  match get_terminator_result term mc' md' with
                  | Some res =>
                    lift (fun x => dcoll (old ++ x))
                         (lift_map
                            (fun d1 : data => nnrc_core_eval h σc ((v, d1) :: σ) (nnrc_to_nnrc_base s2))
                            l) = Some res
                  | None => False
                  end
                | None =>
                  lift dcoll
                       (lift_map
                          (fun d1 : data => nnrc_core_eval h σc ((v, d1) :: σ) (nnrc_to_nnrc_base s2)) l) =
                  None
                end).
        { unfold var in *.
          intros HH; specialize (HH nil); simpl in HH.
          trivial.
        } 
        revert σ mc md inclσ inclmc safe_term.
        induction l; simpl; intros.
        + generalize (nnrc_imp_stmt_eval_terminator h σc ((fresh_var "tmp" fvs, Some (dcoll old)) :: pd_bindings_lift σ) mc md term (NNRCimpVar (fresh_var "tmp" fvs)) safe_term); intros eterm.
          unfold var in *.
          match_case_in eterm; [intros ? eqq2 | intros eqq2]
          ; rewrite eqq2 in eterm; try tauto.
          * destruct p as [[??]?].
            match_case_in eterm; [intros ? eqq3 | intros eqq3]
            ; rewrite eqq3 in eterm; try tauto.
            generalize (nnrc_imp_stmt_eval_env_stack eqq2); intros; subst.
            rewrite eqq3.
            simpl in eterm.
            rewrite app_nil_r.
            match_destr_in eterm.
            unfold id in eterm.
            congruence.
          * simpl in eterm.
            unfold id in eterm.
            match_destr_in eterm.
            congruence.
        + specialize (IHs2 ((v, a) :: σ) ((fresh_var "tmp" fvs, old) :: mc) md).
          cut_to IHs2.
          * simpl in IHs2.
            match_case_in IHs2; [intros ? eqq7 | intros eqq7]
            ; rewrite eqq7 in IHs2; simpl in eqq7
            ; unfold var in *; rewrite eqq7
            ; [ | rewrite IHs2; simpl; trivial].
            destruct p as [[??]?].
            match_case_in IHs2;
              [intros ? eqq8 | intros eqq8]
              ; rewrite eqq8 in IHs2; try tauto.
            rewrite IHs2.
            generalize (nnrc_imp_stmt_eval_env_stack eqq7); intros; subst.            
            generalize (nnrc_imp_stmt_eval_mcenv_domain_stack eqq7); intros mceqq.
            destruct m; simpl in mceqq; try discriminate.
            destruct p; simpl in *.
            invcs mceqq.
            destruct (equiv_dec (fresh_var "tmp" fvs) (fresh_var "tmp" fvs)); [| congruence].
            destruct l0; try discriminate.
            invcs eqq8.
            match_case_in H0
            ; [intros eqq0 | intros ? ? eqq0]
            ; rewrite eqq0 in H0; try discriminate.
            invcs H0.
            assert (eqq0':d0::l0 = rev (d :: l1)).
            { rewrite <- eqq0.
              rewrite rev_app_distr.
              rewrite rev_involutive; simpl; trivial.
            }
            rewrite eqq0'.
            generalize (nnrc_stmt_to_nnrc_imp_stmt_aux_push1 eqq7 eqq1); intros [? eqqq].
            invcs eqqq.
            rewrite eqq0' in H0.
            assert (eqqq':d::l1 = rev (old ++ x :: nil)).
            { rewrite <- H0; rewrite rev_involutive; trivial. }
            rewrite rev_app_distr in eqqq'; simpl in eqqq'.
            clear H0.
            invcs eqqq'.
            specialize (IHl σ mc m0).
            {
              cut_to IHl; trivial.
              - unfold var in *.
                simpl.
                rewrite rev_involutive.
                specialize (IHl (old ++ x :: nil)).
                match goal with
                  [H:match (match ?x with | _ => _ end ) with | _ => _ end |- _] =>
                  let eqq := (fresh "eqq") in
                  case_eq x
                  ;           [intros ? eqq | intros eqq]
                  ; rewrite eqq in H; try tauto
                end.
                + destruct p as [[??]?].
                  destruct m.
                  * apply none_lift in IHl.
                    rewrite IHl; simpl; trivial.
                  * destruct p.
                    { 
                      match goal with
                        [H:match (match ?x with | _ => _ end ) with | _ => _ end |- _] =>
                        let eqq := (fresh "eqq") in
                        case_eq x
                        ;           [intros ? eqq | intros eqq]
                        ; rewrite eqq in H; try tauto
                      end.
                      - destruct p as [[??]?].
                        destruct p.
                        + apply none_lift in IHl.
                          rewrite IHl; simpl; trivial.
                        + match_case_in IHl;
                            [intros ? eqq3 | intros eqq3]
                            ; rewrite eqq3 in IHl; try tauto.
                          apply some_lift in IHl.
                          destruct IHl as [? eqq4 ?]; subst.
                          rewrite eqq4.
                          simpl.
                          rewrite <- app_assoc; simpl; trivial.
                      - apply none_lift in IHl.
                        rewrite IHl; simpl; trivial.
                    } 
                + apply none_lift in IHl.
                  rewrite IHl; simpl; trivial.
              - generalize (nnrc_imp_stmt_eval_mdenv_domain_stack eqq7); intros mdeqq.
                unfold safe_terminator_result in *; rewrite <- mdeqq; trivial.
            }
          * unfold incl in *; simpl in *; intuition.
          * unfold incl in *; simpl in *; intuition.
          * unfold incl in *; simpl in inclbvars; intros.
            right. apply inclbvars.
            rewrite in_app_iff; intuition.
          * simpl; intuition.
      - Case "NNRCIf".
        simpl in *.
        case_eq (nnrc_expr_to_nnrc_imp_expr s1); [intros s1' s1'eq | intros s1'eq]
        ; rewrite s1'eq in eqsi; try discriminate.
        rewrite (nnrc_expr_to_nnrc_imp_expr_some_correct' _ _ s1'eq).
        match_case_in eqsi; [ intros ? eqq1 | intros eqq1]
        ; rewrite eqq1 in eqsi; try discriminate.
        match_case_in eqsi; [ intros ? eqq2 | intros eqq2]
        ; rewrite eqq2 in eqsi; try discriminate.
        invcs eqsi.
        simpl.
        destruct (nnrc_imp_expr_eval h σc (pd_bindings_lift σ) s1' )
        ; simpl; trivial.
        destruct d; simpl; trivial.
        destruct b.
        + eapply IHs2; eauto.
          unfold incl in *; simpl in inclbvars.
          intros ??; apply inclbvars.
          rewrite in_app_iff; intuition.
        + eapply IHs3; eauto. 
          unfold incl in *; simpl in inclbvars.
          intros ??; apply inclbvars.
          rewrite in_app_iff; intuition.
      - Case "NNRCEither".
        simpl in *.
        case_eq (nnrc_expr_to_nnrc_imp_expr s1); [intros s1' s1'eq | intros s1'eq]
        ; rewrite s1'eq in eqsi; try discriminate.
        rewrite (nnrc_expr_to_nnrc_imp_expr_some_correct' _ _ s1'eq).
        match_case_in eqsi; [ intros ? eqq1 | intros eqq1]
        ; rewrite eqq1 in eqsi; try discriminate.
        match_case_in eqsi; [ intros ? eqq2 | intros eqq2]
        ; rewrite eqq2 in eqsi; try discriminate.
        invcs eqsi.
        simpl.
        destruct (nnrc_imp_expr_eval h σc (pd_bindings_lift σ) s1' )
        ; simpl; trivial.
        destruct d; simpl; trivial.
        + specialize (IHs2 _ _ _ eqq1).
          specialize (IHs2 ((v, d) :: σ) mc md).
          cut_to IHs2; intuition.
          * match_case_in IHs2; [intros ? eqq3 | intros eqq3]
            ; rewrite eqq3 in IHs2
            ; simpl in eqq3; unfold var in *; rewrite eqq3; trivial.
            destruct p as [[??]?].
            generalize (nnrc_imp_stmt_eval_env_stack eqq3); intros; subst.
            eauto.
          * simpl; unfold incl in *.
            simpl in *; intuition.
          * simpl; unfold incl in *.
            intros; apply inclbvars.
            simpl; repeat rewrite in_app_iff; intuition.
        + specialize (IHs3 _ _ _ eqq2).
          specialize (IHs3 ((v0, d) :: σ) mc md).
          cut_to IHs3; intuition.
          * match_case_in IHs3; [intros ? eqq3 | intros eqq3]
            ; rewrite eqq3 in IHs3
            ; simpl in eqq3; unfold var in *; rewrite eqq3; trivial.
            destruct p as [[??]?].
            generalize (nnrc_imp_stmt_eval_env_stack eqq3); intros; subst.
            eauto.
          * simpl; unfold incl in *.
            simpl in *; intuition.
          * simpl; unfold incl in *.
            intros; apply inclbvars.
            simpl; repeat rewrite in_app_iff; intuition.
      - Case "NNRCGroupBy".
        simpl in eqsi.
        case_eq (nnrc_expr_to_nnrc_imp_expr s0); [intros s1' s1'eq | intros s1'eq]
        ; rewrite s1'eq in eqsi; simpl in eqsi; try discriminate.
        invcs eqsi.
        generalize (nnrc_imp_stmt_eval_terminator h σc (pd_bindings_lift σ) mc md term (NNRCimpGroupBy s l s1') safe_term); intros eterm.
        simpl nnrc_to_nnrc_base.
        match_destr_in eterm.
        + destruct p as [[??]?].
          match_destr.
          simpl nnrc_to_nnrc_base.
          simpl in eterm.
          rewrite <- (nnrc_expr_to_nnrc_imp_expr_some_correct' _ _ s1'eq) in eterm.
          match_case_in eterm; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in eterm
          ; simpl in eqq1; try discriminate.
          destruct d0; try discriminate.
          erewrite nnrc_group_by_correct; eauto.
        + simpl in eterm.
          match_case_in eterm; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in eterm
          ; simpl in eqq1.
          * rewrite <- (nnrc_expr_to_nnrc_imp_expr_some_correct' _ _ s1'eq) in eqq1.
            destruct d;
              (try solve[
                     eapply nnrc_group_by_correct_some_ncoll; eauto; intros; discriminate]).
            erewrite nnrc_group_by_correct; eauto.
          * rewrite <- (nnrc_expr_to_nnrc_imp_expr_some_correct' _ _ s1'eq) in eqq1.
            eapply nnrc_group_by_correct_none; eauto.
    Qed.
    
    Lemma nnrc_to_nnrc_imp_some_correct
          h σc {s:nnrc} {globals} {si:nnrc_imp} {ret:var} :
      nnrc_stmt_to_nnrc_imp_stmt globals s = Some si ->
      @nnrc_eval _ h σc nil s = nnrc_imp_eval_top h σc si.
    Proof.
      unfold nnrc_stmt_to_nnrc_imp_stmt, nnrc_imp_eval_top.
      intros eqsi.
      destruct si.
      match_option_in eqsi.
      invcs eqsi.
      generalize (nnrc_stmt_to_nnrc_imp_stmt_aux_some_correct
                    eqq
                    h σc nil nil
                    ((fresh_var "ret" (globals ++ nnrc_bound_vars s), None) :: nil)
                 ); intros HH.
      simpl in HH.
      unfold var in *.
      cut_to HH; try solve [ unfold incl; simpl; tauto].
      - match_option_in HH.
        destruct p as [[??]?].
        generalize (nnrc_imp_stmt_eval_mdenv_domain_stack eqq0); intros mceqq.
        simpl in mceqq.
        destruct m0; try discriminate.
        simpl in mceqq; invcs mceqq.
        destruct m0; try discriminate.
        destruct p0; simpl in *; subst.
        destruct ( equiv_dec (fresh_var "ret" (globals ++ nnrc_bound_vars s))
                             (fresh_var "ret" (globals ++ nnrc_bound_vars s))); try congruence.
        unfold id in HH; simpl in HH.
        destruct o; try tauto.
      - unfold incl; simpl; intros.
        repeat rewrite in_app_iff; intuition.
    Qed.
    
    Section tests.
      Local Open Scope nnrc_scope.
      Local Open Scope string_scope.

      Example nnrc1 := (‵abs ‵ (dnat 3) ‵+ ‵(dnat 5)) ‵+ ((‵(dnat 4) ‵+ ‵(dnat 7)) ‵+‵`(dnat  3)).
      (*    Eval vm_compute in (stratify nnrc1). *)

      Example nnrc2 := NNRCLet "x" (NNRCLet "x" (‵ (dnat 3) ‵+ ‵(dnat 5)) (NNRCVar "x")) (NNRCVar "x").
      (* Eval vm_compute in (nnrc_to_nnrc_imp_top nil nnrc2). *)
    End tests.

  End from_stratified.


  
End NNRCtoNNRCimp.
