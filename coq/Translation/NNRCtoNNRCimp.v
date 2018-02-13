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

  End from_stratified.

End NNRCtoNNRCimp.
