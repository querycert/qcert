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
Require Import Compare_dec.
Require Import Program.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonSystem.
Require Import LambdaNRA.

Section TLambdaNRA.
  (** Typing for LambdaNRA *)
  Section typ.
    Context {m:basic_model}.
    Context (τconstants:tbindings).    
    Inductive lambda_nra_type : lambda_nra -> tbindings -> rtype -> Prop :=
    | LTVar {Γ τ} v :
        tdot Γ v = Some τ ->
        lambda_nra_type (LNRAVar v) Γ τ
    | TLTable {Γ τ} s :
      tdot τconstants s = Some τ ->
      lambda_nra_type (LNRATable s) Γ τ
  | TLConst {Γ τ} c :
      data_type (normalize_data brand_relation_brands c) τ ->
      lambda_nra_type (LNRAConst c) Γ τ
  | TLBinop {Γ τ₁ τ₂ τ} b op1 op2 :
      (* b : (τ₁,τ₂) -> τout
         op₁ : τin -> τ₁
         op₂ : τin -> τ₂
         ==========================
         b (op₁,op₂) : τin -> τout *)
      binary_op_type b τ₁ τ₂ τ ->
      lambda_nra_type op1 Γ τ₁ ->
      lambda_nra_type op2 Γ τ₂ ->
      lambda_nra_type (LNRABinop b op1 op2) Γ τ
  | TLUnop {Γ τ₀ τ } u op :
      unary_op_type u τ₀ τ ->
      lambda_nra_type op Γ τ₀ ->
      lambda_nra_type (LNRAUnop u op) Γ τ
  | TLMap {Γ τ₀ τ} lop1 op2 :
      lnra_lambda_type lop1 Γ (τ₀ ~~> τ) ->
      lambda_nra_type op2 Γ (Coll τ₀) ->
      lambda_nra_type (LNRAMap lop1 op2) Γ (Coll τ)
  | TLMapProduct {Γ τ₁ τ₂ τ} lop1 op2 pf1 pf2 pf3 :
      lnra_lambda_type lop1 Γ ((Rec Closed τ₁ pf1)~~>(Coll (Rec Closed τ₂ pf2))) ->
      lambda_nra_type op2 Γ (Coll (Rec Closed τ₁ pf1)) ->
      rec_concat_sort τ₁ τ₂ = τ ->
      lambda_nra_type (LNRAMapProduct lop1 op2) Γ (Coll (Rec Closed τ pf3))
  | ATProduct {Γ τ₁ τ₂ τ} op1 op2 pf1 pf2 pf3 :
      lambda_nra_type op1 Γ (Coll (Rec Closed τ₁ pf1)) ->
      lambda_nra_type op2 Γ (Coll (Rec Closed τ₂ pf2)) ->
      rec_concat_sort τ₁ τ₂ = τ ->
      lambda_nra_type (LNRAProduct op1 op2) Γ(Coll (Rec Closed τ pf3))
  | ATFilter {Γ τ} lop1 op2 :
      lnra_lambda_type lop1 Γ (τ~~>Bool) ->
      lambda_nra_type op2 Γ (Coll τ) ->
      lambda_nra_type (LNRAFilter lop1 op2) Γ (Coll τ)
    with
    lnra_lambda_type :  lnra_lambda -> tbindings -> rtype -> Prop :=
    | TLLambda {Γ τin τout} x e :
        lambda_nra_type e (rec_sort (Γ++[(x,τin)])) τout ->
        lnra_lambda_type (LNRALambda x e) Γ (τin ~~> τout)
    .

    Lemma TLLambda_inv {Γ τin τout} x e :
      lnra_lambda_type (LNRALambda x e) Γ (τin ~~> τout) ->
      lambda_nra_type e (rec_sort (Γ++[(x,τin)])) τout.
    Proof.
      inversion 1.
      rtype_equalizer; congruence.
    Qed.
    
  End typ.

    

  (** Type lemmas for individual algebraic expressions *)
  Context {m:basic_model}.

  (** Main lemma for the type correctness of NNNRC *)
    Theorem typed_lambda_nra_yields_typed_data
          {τ}
          (cenv:bindings)
          (τc:tbindings)
          (env:bindings)
          (Γ:tbindings)
          (e:lambda_nra) :
    bindings_type cenv τc ->
    bindings_type env Γ ->
    lambda_nra_type τc e Γ τ ->
    (exists x,
        (lambda_nra_eval brand_relation_brands cenv env e) = Some x
        /\ (data_type x τ)).
    Proof.
      intros cbt.
      revert env Γ τ.
      induction e; intros env Γ τ bt et
      ; invcs et
      ; autorewrite with lambda_nra
      ; simpl.
      - unfold bindings_type in *.
      clear cbt.
      unfold tdot, edot in *.
      dependent induction bt; intros; try discriminate.
      destruct x; destruct y; destruct H; simpl in *; subst.
      match_case_in H0; [intros ? eqq | intros eqq]; rewrite eqq in H0.
      + invcs H0; destruct (IHbt eqq) as [dd [edd tdd]].
         rewrite edd.
         eauto.
      + match_destr_in H0.
        unfold equiv in *; invcs H0.
        apply sorted_forall_same_domain in bt.
        apply assoc_lookupr_none_nin in eqq.
        rewrite <- bt in eqq.
        exists d; split; trivial.
        match_case; intros.
        apply assoc_lookupr_in in H.
        apply in_dom in H.
        congruence.
    - unfold bindings_type in *.
      clear bt.
      unfold tdot, edot in *.
      induction cbt; intros; try discriminate.
      destruct x; destruct y; destruct H; simpl in *; subst.
      match_case_in H0; [intros ? eqq | intros eqq]; rewrite eqq in H0.
      + invcs H0; destruct (IHcbt eqq) as [dd [edd tdd]].
         rewrite edd.
         eauto.
      + match_destr_in H0.
        unfold equiv in *; invcs H0.
        apply sorted_forall_same_domain in cbt.
        apply assoc_lookupr_none_nin in eqq.
        rewrite <- cbt in eqq.
        exists d; split; trivial.
        match_case; intros.
        apply assoc_lookupr_in in H.
        apply in_dom in H.
        congruence.
    - eauto. 
    - destruct (IHe1 _ _ _ bt H5) as [dd1 [edd1 tdd1]]; 
      destruct (IHe2 _ _ _ bt H6) as [dd2 [edd2 tdd2]].
      rewrite edd1; rewrite edd2.
      simpl; apply (@typed_binary_op_yields_typed_data _ _ _ _ _ _ τ₁ τ₂ τ); assumption.
    - destruct (IHe _ _ _ bt H4) as [dd [edd tdd]].
      rewrite edd.
      simpl; apply (@typed_unary_op_yields_typed_data _ _ _ _ _ _ _ τ₀ τ); assumption.
    - destruct (IHe2 _ _ _ bt H4) as [dd2 [edd2 tdd2]].
      rewrite edd2; simpl.
      dtype_inverter.
      apply TLLambda_inv in H1.
      invcs tdd2; rtype_equalizer; subst.
      clear edd2.
      induction dd2; simpl.
      + eexists; split; [reflexivity|]. repeat constructor.
      + invcs H2; destruct (IHdd2 H5) as [dd1 [edd1 tdd1]].
        apply some_lift in edd1.
        destruct edd1 as [dd11 ? tdd11]; subst.
        rewrite e.
        rewrite lnra_lambda_eval_lambda_eq.
        assert (bt1:bindings_type (rec_sort (env ++ [(s, a)])) (rec_sort (Γ ++ [(s, τ₀)])) ).
        {
          apply bindings_type_sort.
          unfold bindings_type.
          apply Forall2_app; trivial.
          constructor; simpl; intuition. 
        }
        destruct (IHe1 _ _ _ bt1 H1) as [dd3 [edd3 tdd3]].
        rewrite edd3.
        simpl.
        eexists; split; [reflexivity | ].
        invcs tdd1; rtype_equalizer; subst.
        constructor; constructor; trivial.
    - destruct (IHe2 _ _ _ bt H2) as [dd2 [edd2 tdd2]].
      rewrite edd2; simpl.
      dtype_inverter.
      apply Col_inv in tdd2.
      apply TLLambda_inv in H1.
      clear edd2.
      induction dd2; simpl.
      + eexists; split; [reflexivity|]. repeat constructor.
      + invcs tdd2.
        destruct (IHdd2 H4) as [dd1 [edd1 tdd1]].
        apply some_lift in edd1.
        destruct edd1 as [dd11 ? tdd11]; subst.
        assert (bt1:bindings_type (rec_sort (env ++ [(s, a)])) (rec_sort (Γ ++ [(s, Rec Closed τ₁ pf1)])) ).
        {
          apply bindings_type_sort.
          unfold bindings_type.
          apply Forall2_app; trivial.
          constructor; simpl; intuition. 
        }
        destruct (IHe1 _ _ _ bt1 H1) as [dd3 [edd3 tdd3]].
        rewrite (omap_product_ext _  (fun d => lambda_nra_eval brand_relation_brands cenv (rec_sort (env ++ [(s, d)])) e1));
          [ | intros; apply lnra_lambda_eval_lambda_eq ].
        dtype_inverter.
        apply Col_inv in tdd1.
        apply Col_inv in tdd3.
        assert (part1pf:exists part1, oncoll_map_concat (fun d => lambda_nra_eval brand_relation_brands cenv 
                                                                             (rec_sort (env ++ [(s, d)])) e1) (drec a) = Some part1 /\ Forall (fun d : data => d ▹ Rec Closed (rec_concat_sort τ₁ τ₂) pf3) part1
).
        {
          unfold oncoll_map_concat.
          rewrite edd3.
          unfold omap_concat.
          clear edd3.
          revert dd3 tdd3 H3; clear; intros.
          induction dd3.
          - eexists; split; [reflexivity | ]; constructor.
          - invcs tdd3.
            dtype_inverter.
            destruct (IHdd3 H2) as [part1 [part1eq part1t]].
            unfold orecconcat in part1eq.
            rewrite part1eq.
            simpl.
            eexists; split; [reflexivity | ].
            constructor; trivial.
            apply dtrec_closed_inv in H1.
            apply dtrec_closed_inv in H3.
            apply dtrec_full.
            apply rec_concat_with_drec_concat_well_typed; auto.
        }
        destruct part1pf as [part1 [part1eq part1t]].
        erewrite omap_product_cons; eauto.
        simpl; eexists; split; [reflexivity | ].
        constructor.
        apply Forall_app; trivial.
    - destruct (IHe1 _ _ _ bt H1) as [dd1 [edd1 tdd1]]; 
      destruct (IHe2 _ _ _ bt H2) as [dd2 [edd2 tdd2]].
      rewrite edd1; rewrite edd2.
      clear edd1 edd2.
      dtype_inverter.
      apply Col_inv in tdd1.
      apply Col_inv in tdd2.
      clear IHe1 IHe2 cbt bt.
      induction dd1; simpl.
      + eexists; split; [reflexivity | ]; repeat constructor.
      + invcs tdd1.
        destruct (IHdd1 H4) as [dd3 [dde3 ddt3]]; clear IHdd1.
        apply some_lift in dde3.
        destruct dde3 as [dd33 dde33 ?]; subst.
        assert (part1pf:exists part1, oncoll_map_concat (fun _ : data => Some (dcoll dd2)) a = Some part1 /\ Forall (fun d : data => d ▹ Rec Closed (rec_concat_sort τ₁ τ₂) pf3) part1).
        {
          clear  dd33 dde33 ddt3.
          unfold oncoll_map_concat.
          dtype_inverter.
          apply dtrec_closed_inv in H3.
          unfold omap_concat.
          unfold orecconcat.
          induction dd2; simpl.
          - eexists; split; [reflexivity | ]; constructor.
          - invcs tdd2.
            destruct (IHdd2 H6) as [part1 [part1e part1t]].
            rewrite part1e; clear part1e.
            dtype_inverter.
            eexists; split; [reflexivity | ].
            constructor; trivial.
            apply dtrec_full.
            apply dtrec_closed_inv in H5.
            apply rec_sort_Forall2.
            + repeat rewrite domain_app; f_equal;
              eapply sorted_forall_same_domain; eauto.
            + apply Forall2_app; trivial.
        } 
        dtype_inverter.
        apply Col_inv in ddt3.
        destruct part1pf as [part1 [part1eq part1t]].
        erewrite omap_product_cons; eauto.
        simpl; eexists; split; [reflexivity | ].
        constructor.
        apply Forall_app; trivial.
    - destruct (IHe2 _ _ _ bt H4) as [dd2 [edd2 tdd2]].
      rewrite edd2; simpl; clear edd2 H4.
      dtype_inverter.
      apply TLLambda_inv in H1.
      apply Col_inv in tdd2.
      induction dd2; simpl.
      + eexists; split; [reflexivity|]. repeat constructor.
      + invcs tdd2.
        destruct (IHdd2 H3) as [dd1 [edd1 tdd1]].
        apply some_lift in edd1.
        destruct edd1 as [dd11 dd11e dd11t]; subst.
        rewrite dd11e.
        rewrite lnra_lambda_eval_lambda_eq.
        assert (bt1:bindings_type (rec_sort (env ++ [(s, a)])) (rec_sort (Γ ++ [(s, τ0)])) ).
        {
          apply bindings_type_sort.
          unfold bindings_type.
          apply Forall2_app; trivial.
          constructor; simpl; intuition. 
        }
        destruct (IHe1 _ _ _ bt1 H1) as [dd3 [edd3 tdd3]].
        rewrite edd3.
        dtype_inverter.
        apply Col_inv in tdd1.
        destruct x; simpl; (eexists; split; [reflexivity | ]).
        * constructor; constructor; trivial.
        * constructor; trivial.
    Qed.

    (* we are only sensitive to the environment up to lookup *)
  Global Instance nnrc_type_lookup_equiv_prop {m:basic_model} :
    Proper (assoc_lookupr_equiv ==> eq ==> assoc_lookupr_equiv ==> eq ==> iff) lambda_nra_type.
  Proof.
    cut (Proper (assoc_lookupr_equiv ==> eq ==> assoc_lookupr_equiv ==> eq ==> impl) lambda_nra_type);
    unfold Proper, respectful, iff, impl; intros; subst;
      [unfold assoc_lookupr_equiv in *; intuition; eauto | ].
    rename y0 into e.
    rename x into cenv1.
    rename y into cenv2.
    rename x1 into env1.
    rename y1 into env2.
    rename y2 into τ.
    rename H into ceqs.
    rename H1 into eqs.
    rename H3 into et.
    revert env1 env2 τ eqs et.
    induction e; simpl; inversion 2; subst; econstructor; eauto 3
    ; try solve [
            constructor
            ; apply TLLambda_inv in H1
            ; eapply IHe1; [ | eassumption]
            ; rewrite eqs; reflexivity].
    - unfold tdot, edot in *; unfold assoc_lookupr_equiv in *; simpl in *.
      rewrite <- eqs; trivial.
    - unfold tdot, edot in *; unfold assoc_lookupr_equiv in *; simpl in *.
      rewrite <- ceqs; trivial.
  Qed.
  
End TLambdaNRA.

