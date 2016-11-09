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

(* This includes some rewrites/simplification rules for the Nested relational calculus *)

Section TRew.
  Require Import String.
  Require Import List ListSet.
  Require Import Arith.
  Require Import EquivDec.
      
  Require Import Utils BasicSystem.
    
  Require Import NNRC NNRCEq NNRCShadow.
  Require Import NRewUtil NRew TNRC TShadow TNRCEq.

  Local Open Scope nrc_scope.
  (* e ⇒ unshadow(e) *)

  Context {m:basic_model}.
  
  Lemma tunshadow_preserves_arrow sep renamer avoid (e:nrc) :
    tnrc_rewrites_to e (unshadow sep renamer avoid e).
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    rewrite unshadow_preserves; reflexivity.
    intros.
    rewrite <- unshadow_type; assumption.
  Qed.

  (* { a: e }.a ≡ e *)

  Lemma tdot_of_rec a (e:nrc) :
    tnrc_rewrites_to (NRCUnop (ADot a) (NRCUnop (ARec a) e)) e.
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    - rewrite dot_of_rec; reflexivity.
    - intros.
      nrc_inverter.
      unfold tdot, edot in *; simpl in * .
      nrc_inverter.
      trivial.
  Qed.

  Lemma tnrc_dot_of_concat_rec_eq_arrow s (e1 e2:nrc) :
    tnrc_rewrites_to (NRCUnop (ADot s) (NRCBinop AConcat e1 (NRCUnop (ARec s) e2))) e2.
  Proof.
    red; intros ? ? typ1.
    nrc_inverter.
    unfold tdot,edot,rec_concat_sort in H0.
    rewrite assoc_lookupr_drec_sort in H0.
    rewrite (assoc_lookupr_app τ₁ ((s, s0) :: nil)) in H0.
    simpl in H0.
    nrc_inverter.
    split; trivial; intros.
    nrc_input_well_typed.
    dtype_inverter.
    unfold edot.
    rewrite assoc_lookupr_drec_sort.
    rewrite (assoc_lookupr_app _ ((s, _) :: nil)).
    simpl.
    nrc_inverter.
    trivial.
  Qed.

  Lemma tnrc_dot_of_concat_rec_neq_arrow s s2 (e1 e2:nrc) :
    s <> s2 ->
    tnrc_rewrites_to (NRCUnop (ADot s) (NRCBinop AConcat e1 (NRCUnop (ARec s2) e2))) (NRCUnop (ADot s) e1).
  Proof.
    red; intros neq ? ? typ1.
    nrc_inverter.
    rewrite tdot_rec_concat_sort_neq in H0 by auto.
    unfold tdot, edot in H0.
    rewrite assoc_lookupr_drec_sort in H0.
    split.
    - econstructor; eauto 2.
      econstructor; eauto 2.
    - intros.
      nrc_input_well_typed.
      dtype_inverter.
      unfold edot.
      rewrite assoc_lookupr_drec_sort.
      rewrite (assoc_lookupr_app _ ((s0, _) :: nil)).
      simpl.
      destruct (string_eqdec s s0); [congruence | ].
      trivial.
  Qed.

  Lemma tnrc_merge_concat_to_concat_arrow s1 s2 p1 p2:
    s1 <> s2 ->
    tnrc_rewrites_to (‵[| (s1, p1)|] ⊗ ‵[| (s2, p2)|]) (‵{|‵[| (s1, p1)|] ⊕ ‵[| (s2, p2)|]|}).
  Proof.
    intros.
    apply nrc_rewrites_typed_with_untyped.
    - apply nrc_merge_concat_to_concat; trivial.
    - intros ? ? typ.
      nrc_inverter.
      econstructor.
      + econstructor.
      + econstructor; econstructor; try econstructor; eauto 2.
        unfold merge_bindings in H2.
        match_destr_in H2.
        injection H2; trivial.
     Grab Existential Variables.
     solve[eauto].   
     solve[eauto].
  Qed.

  Lemma tfor_nil_arrow x e2 :
    tnrc_rewrites_to (NRCFor x ‵{||} e2) ‵{||}.
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    - apply for_nil.
    - intros.
      nrc_inverter.
      econstructor.
      simpl.
      repeat econstructor.
  Qed.

  Lemma tfor_singleton_to_let_arrow x e1 e2:
    tnrc_rewrites_to (NRCFor x (NRCUnop AColl e1) e2)
            (NRCUnop AColl (NRCLet x e1 e2)).
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    - apply for_singleton_to_let.
    - intros.
      nrc_inverter.
      econstructor.
      + econstructor.
      + econstructor; eauto.
  Qed.

  Lemma tflatten_nil_nrc_arrow  :
    tnrc_rewrites_to (♯flatten(‵{||})) ‵{||}.
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    - apply flatten_nil_nrc.
    - intros ? ? typ.
      nrc_inverter.
      repeat (econstructor; simpl).
  Qed.

  Lemma tflatten_singleton_nrc_arrow e :
    tnrc_rewrites_to (♯flatten(‵{| e |})) e.
  Proof.
    red; intros; simpl.
    nrc_inverter.
    split; trivial.
    intros.
    nrc_input_well_typed.
    dtype_inverter.
    rewrite app_nil_r.
    trivial.
  Qed.

  (* {| e3 | $t2 ∈ ♯flatten({| e2 ? ‵{|$t1|} : ‵{||} | $t1 ∈ e1 |}) |}
       ≡ ♯flatten({| e2 ? ‵{| LET $t2 := $t1 IN e3 ]|} : ‵{||} | $t1 ∈ e1 |}) *)

  Lemma tmap_sigma_fusion_arrow (e1 e2 e3:nrc) (v1 v2:var) :
    ~ In v1 (nrc_free_vars e3) ->
    tnrc_rewrites_to
      (NRCFor v2 
              (NRCUnop AFlatten
                       (NRCFor v1 e1
                               (NRCIf e2 (NRCUnop AColl (NRCVar v1)) (NRCConst (dcoll nil)))))
              e3)
      (NRCUnop AFlatten
               (NRCFor v1 e1
                       (NRCIf e2
                              (NRCUnop AColl (NRCLet v2 (NRCVar v1) e3))
                              (NRCConst (dcoll nil))))).
  Proof.
    intros.
    apply nrc_rewrites_typed_with_untyped.
    - rewrite (map_sigma_fusion e1 e2 e3 v1 v2 H); reflexivity.
    - intros.
      nrc_inverter.
      repeat (econstructor; eauto 2).
      + simpl. 
        match_destr.
        congruence.
      + generalize (nrc_type_remove_free_env ((v2, τ₁)::nil) v1 τ₁ τenv e3 τ₂ H); intros nt.
        simpl in nt.
        rewrite nt.
        trivial.
  Qed.

  (* {| e3 | $t2 ∈ ♯flatten({| e2 ? ‵{|$t1|} : ‵{||} | $t1 ∈ e1 |}) |}
       ≡ ♯flatten({| e2 ? ‵{| LET $t2 := $t1 IN e3 ]|} : ‵{||} | $t1 ∈ e1 |}) *)

  Lemma tmap_sigma_fusion_samevar_arrow (e1 e2 e3:nrc) (v1:var) :
    tnrc_rewrites_to
      (NRCFor v1 
              (NRCUnop AFlatten
                       (NRCFor v1 e1
                               (NRCIf e2 (NRCUnop AColl (NRCVar v1)) (NRCConst (dcoll nil)))))
              e3)
      (NRCUnop AFlatten
               (NRCFor v1 e1
                       (NRCIf e2
                              (NRCUnop AColl e3)
                              (NRCConst (dcoll nil))))).
  Proof.
    intros.
    apply nrc_rewrites_typed_with_untyped.
    - rewrite (map_sigma_fusion_samevar e1 e2 e3 v1); reflexivity.
    - intros.
      nrc_inverter.
      repeat (econstructor; eauto 2).
  Qed.

  Lemma tlet_inline_disjoint_arrow x e1 e2 :
    disjoint (nrc_bound_vars e2) (nrc_free_vars e1) ->
    tnrc_rewrites_to
      (NRCLet x e1 e2)
      (nrc_subst e2 x e1).
  Proof.
    red; simpl; intros.
    nrc_inverter.
    split.
    - eapply nrc_type_cons_subst_disjoint; eauto.
    - intros.
      nrc_input_well_typed.
      erewrite <- nrc_eval_cons_subst_disjoint; eauto.
  Qed.

  Lemma tlet_inline_arrow sep renamer x e1 e2 :
    tnrc_rewrites_to
      (NRCLet x e1 e2)
      (nrc_subst (unshadow sep renamer (nrc_free_vars e1) e2) x e1).
  Proof.
    transitivity (NRCLet x e1 (unshadow sep renamer (nrc_free_vars e1) e2)).
    - apply nrclet_tproper; trivial.
      + reflexivity.
      + apply tunshadow_preserves_arrow.
    - apply tlet_inline_disjoint_arrow.
      unfold disjoint.
      intros.
      apply (unshadow_avoid _ _ _ _ _ H0 H).
  Qed.

  Lemma tfor_over_if_arrow x e1 e2  e3 ebody :
    tnrc_rewrites_to (NRCFor x (NRCIf e1 e2 e3) ebody)
                     (NRCIf e1 (NRCFor x e2 ebody)
                            (NRCFor x e3 ebody)).
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    - apply for_over_if.
    - intros ? ? typ.
      nrc_inverter.
      repeat (econstructor; eauto 2).
  Qed.
  
  Lemma tfor_over_either_disjoint_arrow x e1 xl el xr er ebody:
    disjoint (xl::xr::nil) (nrc_free_vars ebody) ->
    tnrc_rewrites_to (NRCFor x (NRCEither e1 xl el xr er) ebody)
            (NRCEither e1
                       xl (NRCFor x el ebody)
                       xr (NRCFor x er ebody)).
  Proof.
    intros disj.
    apply nrc_rewrites_typed_with_untyped.
    - apply for_over_either_disjoint; trivial.
    - intros ? ? typ.
      apply disjoint_cons_inv1 in disj.
      destruct disj as [disj nin1].
      apply disjoint_cons_inv1 in disj.
      destruct disj as [_ nin2].
      nrc_inverter.
      econstructor; eauto 2.
      + econstructor; eauto 2.
        generalize (@nrc_type_remove_free_env m ((x,τ₁)::nil) xl τl τenv ebody)
        ; simpl; intros re1; rewrite re1; trivial.
      + econstructor; eauto 2.
        generalize (@nrc_type_remove_free_env m ((x,τ₁)::nil) xr τr τenv ebody)
        ; simpl; intros re1; rewrite re1; trivial.
  Qed.

  Lemma tnrceither_rename_l_arrow e1 xl el xr er xl' :
    ~ In xl' (nrc_free_vars el) ->
    ~ In xl' (nrc_bound_vars el) ->
    tnrc_rewrites_to (NRCEither e1 xl el xr er)
            (NRCEither e1 xl' (nrc_subst el xl (NRCVar xl')) xr er).
  Proof.
    intros nfree nbound.
    apply nrc_rewrites_typed_with_untyped.
    - apply nrceither_rename_l; trivial.
    - intros.
      nrc_inverter.
      econstructor; eauto 2.
      apply nrc_type_cons_subst; trivial.
  Qed.

  Lemma tnrceither_rename_r_arrow e1 xl el xr er xr' :
    ~ In xr' (nrc_free_vars er) ->
    ~ In xr' (nrc_bound_vars er) ->
    tnrc_rewrites_to (NRCEither e1 xl el xr er)
            (NRCEither e1 xl el xr' (nrc_subst er xr (NRCVar xr'))).
  Proof.
    intros nfree nbound.
    apply nrc_rewrites_typed_with_untyped.
    - apply nrceither_rename_r; trivial.
    - intros.
      nrc_inverter.
      econstructor; eauto 2.
      apply nrc_type_cons_subst; trivial.
  Qed.

  Lemma tfor_over_either_arrow sep x e1 xl el xr er ebody:
    tnrc_rewrites_to (NRCFor x (NRCEither e1 xl el xr er) ebody)
            (    let xl' := really_fresh_in sep xl (nrc_free_vars el ++ nrc_bound_vars el) ebody in
                 let xr' := really_fresh_in sep xr (nrc_free_vars er ++ nrc_bound_vars er) ebody in
              (NRCEither e1
                       xl' (NRCFor x (nrc_subst el xl (NRCVar xl')) ebody)
                       xr' (NRCFor x (nrc_subst er xr (NRCVar xr')) ebody))).
  Proof.
    simpl.
    transitivity (NRCFor x (NRCEither e1
                                       (really_fresh_in sep xl (nrc_free_vars el ++ nrc_bound_vars el) ebody)
                                       (nrc_subst el xl (NRCVar (really_fresh_in sep xl (nrc_free_vars el ++ nrc_bound_vars el) ebody)))
                                       (really_fresh_in sep xr (nrc_free_vars er ++ nrc_bound_vars er) ebody)
                                       (nrc_subst er xr (NRCVar (really_fresh_in sep xr (nrc_free_vars er ++ nrc_bound_vars er) ebody)))) ebody).
    - rewrite <- tnrceither_rename_l_arrow; simpl.
      rewrite <- tnrceither_rename_r_arrow; simpl.
      reflexivity.
      + intro inn.
        assert (inn2:In (really_fresh_in sep xr (nrc_free_vars er ++ nrc_bound_vars er) ebody)
                    (nrc_free_vars er ++ nrc_bound_vars er))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
      + intro inn.
        assert (inn2:In (really_fresh_in sep xr (nrc_free_vars er ++ nrc_bound_vars er) ebody)
                    (nrc_free_vars er ++ nrc_bound_vars er))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
      + intro inn.
        assert (inn2:In (really_fresh_in sep xl (nrc_free_vars el ++ nrc_bound_vars el) ebody)
                    (nrc_free_vars el ++ nrc_bound_vars el))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
      + intro inn.
        assert (inn2:In (really_fresh_in sep xl (nrc_free_vars el ++ nrc_bound_vars el) ebody)
                    (nrc_free_vars el ++ nrc_bound_vars el))
               by (rewrite in_app_iff; intuition).
        apply really_fresh_from_avoid in inn2; trivial.
    - apply tfor_over_either_disjoint_arrow.
      red; simpl; intuition; subst;
        apply really_fresh_from_free in H0; trivial.
  Qed.  

  Lemma tnrcunop_over_either_arrow op e1 xl el xr er:
    tnrc_rewrites_to
      (NRCUnop op (NRCEither e1 xl el xr er))
      (NRCEither e1 xl (NRCUnop op el) xr (NRCUnop op er)).
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    - apply nrcunop_over_either.
    - intros.
      nrc_inverter.
      repeat (econstructor; eauto 2).
    Qed.

  Lemma tnrcunop_over_if_arrow op e1 e2 e3:
    tnrc_rewrites_to
      (NRCUnop op (NRCIf e1 e2 e3))
      (NRCIf e1 (NRCUnop op e2) (NRCUnop op e3)).
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    - apply nrcunop_over_if.
    - intros.
      nrc_inverter.
      repeat (econstructor; eauto 2).
    Qed.

      (* ♯flatten({ e1 ? { $t1 } : {} | $t1 ∈ { e2 } }) ≡ LET $t1 := e2 IN e1 ? { $t1 } : {} *)

  Lemma tsigma_to_if_arrow (e1 e2:nrc) (v:var) :
    tnrc_rewrites_to
      (NRCUnop AFlatten
               (NRCFor v (NRCUnop AColl e2)
                       (NRCIf e1
                              (NRCUnop AColl (NRCVar v))
                              (NRCConst (dcoll nil)))))
      (NRCLet v e2 (NRCIf e1 (NRCUnop AColl (NRCVar v)) (NRCConst (dcoll nil)))).
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    - rewrite sigma_to_if; reflexivity.
    - intros.
      nrc_inverter.
      repeat (econstructor; eauto 2).
      simpl.
      nrc_inverter.
      trivial.
  Qed.

  Ltac casermap H := match type of H with
      | context [rmap ?x ?l] =>
        let fr := fresh "eqq" in
        case_eq (rmap x l); [intros ? fr | intros fr];
          rewrite fr in H
             end; simpl in H.

  Lemma tcount_over_flat_for_either_if_nil_arrow v e1 xl e11 e12 xr ehead :
    tnrc_rewrites_to
      (♯count(♯flatten(NRCFor v
                              ehead (NRCEither e1 xl
                                               (NRCIf e11(‵{| e12|}) ‵{||}) xr ‵{||}))))
      (♯count(♯flatten(NRCFor v
                              ehead (NRCEither e1 xl
                                               (NRCIf e11(‵{| ‵(dunit) |}) ‵{||}) xr ‵{||})))).
  Proof.
    red; intros.
    invcs H.
    invcs H5.
    invcs H2.
    invcs H3.
    rtype_equalizer.
    subst.
    invcs H6.
    apply Coll_right_inv in H4.
    subst.
    invcs H5.
    invcs H9.
    split.
    - econstructor; [econstructor| ].
      econstructor; [econstructor | ].
      econstructor; eauto 2.
      econstructor.
      + eauto.
      + econstructor.
        * eauto.
        * repeat (econstructor; simpl). 
        * repeat (econstructor; simpl). 
      + repeat (econstructor; simpl). 
    - intros; simpl.
      destruct (typed_nrc_yields_typed_data _ _ _ H H2) as [?[eqq1 typ1]].
      rewrite eqq1; simpl.
      destruct x; simpl; trivial.
      clear eqq1 ehead H2.
      induction l; simpl; trivial.
      inversion typ1; clear typ1; rtype_equalizer. 
      subst.
      inversion H2; clear H2; subst.
      assert (typ1':dcoll l ▹ Coll τ₁)
        by (econstructor; trivial).
      clear H5.
      specialize (IHl typ1').
      casermap IHl; [ casermap IHl | ].
      + simpl.
        assert (bt2:bindings_type ((v, a) :: env) ((v, τ₁) :: τenv))
               by (econstructor; eauto).
        destruct (typed_nrc_yields_typed_data _ _ _ bt2 H8) as [?[eqq2 typ2]].
        rewrite eqq2.
        invcs H6.
        invcs H5.
        rtype_equalizer.
        subst.
        invcs typ2; rtype_equalizer.
        * subst.
          assert (tb12:bindings_type ((xl,d)::(v,a)::env) ((xl,τl)::(v,τ₁)::τenv))
            by (econstructor; eauto).
          destruct (typed_nrc_yields_typed_data _ _ _ tb12 H4) as [?[eqq12 typ12]].
          rewrite eqq12; simpl.
          dtype_inverter.
          destruct (typed_nrc_yields_typed_data _ _ _ tb12 H11) as [?[eqq3 typ3]].
          rewrite eqq3.
          simpl.
          { case_eq (rflatten l0);
            [intros ? reqq0 | intros reqq0];
            rewrite reqq0 in IHl;
            (case_eq (rflatten l1);
             [intros ? reqq1 | intros reqq1];
             rewrite reqq1 in IHl); simpl in IHl; inversion IHl.
            - apply of_nat_inv in H1.
              destruct x0; simpl;
              rewrite (rflatten_cons _ _ _ reqq0);
                rewrite (rflatten_cons _ _ _ reqq1); simpl;
              congruence.
            - destruct x0; simpl;
              rewrite (rflatten_cons_none _ _ reqq0);
                rewrite (rflatten_cons_none _ _ reqq1); simpl; trivial.
          }
        * subst.
          { case_eq (rflatten l0);
            [intros ? reqq0 | intros reqq0];
            rewrite reqq0 in IHl;
            (case_eq (rflatten l1);
             [intros ? reqq1 | intros reqq1];
             rewrite reqq1 in IHl); simpl in IHl; inversion IHl;
            simpl.
            - apply of_nat_inv in H1.
              rewrite (rflatten_cons _ _ _ reqq0);
                rewrite (rflatten_cons _ _ _ reqq1); simpl;
                  congruence.
            - rewrite (rflatten_cons_none _ _ reqq0);
                rewrite (rflatten_cons_none _ _ reqq1); simpl; trivial.
          }
      + cut False; [intuition | ].
        clear eqq IHl.
        induction l; simpl in eqq0; try discriminate.
        inversion typ1'; clear typ1'; rtype_equalizer. 
        subst.
        inversion H2; clear H2; subst.
        assert (typ1':dcoll l ▹ Coll τ₁)
          by (econstructor; trivial).
        clear H9.
        apply (IHl typ1'); clear IHl.
        assert (tb:bindings_type ((v,a0)::env) ((v,τ₁)::τenv))
        by (econstructor; eauto).
        destruct (typed_nrc_yields_typed_data _ _ _ tb H8) as [?[eqq1 typ1]].
        rewrite eqq1 in eqq0; simpl in eqq0.
        destruct x; inversion typ1; rtype_equalizer.
        * subst.
          assert (tb2:bindings_type ((xl,x)::(v,a0)::env) ((xl,τl)::(v,τ₁)::τenv))
                 by (econstructor; eauto).
          destruct (typed_nrc_yields_typed_data _ _ _ tb2 H4) as [?[eqq2 typ2]].
          rewrite eqq2 in eqq0; simpl in eqq0.
          dtype_inverter.
          destruct x1; simpl in eqq0;
            apply none_lift in eqq0; trivial.
        * subst.
          apply none_lift in eqq0; trivial.
      + cut False; [intuition | ].
        clear IHl.
        induction l; simpl in eqq; try discriminate.
        inversion typ1'; clear typ1'; rtype_equalizer. 
        subst.
        inversion H2; clear H2; subst.
        assert (typ1':dcoll l ▹ Coll τ₁)
          by (econstructor; trivial).
        clear H9.
        apply (IHl typ1'); clear IHl.
        assert (tb:bindings_type ((v,a0)::env) ((v,τ₁)::τenv))
        by (econstructor; eauto).
        destruct (typed_nrc_yields_typed_data _ _ _ tb H8) as [?[eqq1 typ1]].
        rewrite eqq1 in eqq; simpl in eqq.
        destruct x; inversion typ1; rtype_equalizer.
        * subst.
          assert (tb2:bindings_type ((xl,x)::(v,a0)::env) ((xl,τl)::(v,τ₁)::τenv))
                 by (econstructor; eauto).
          destruct (typed_nrc_yields_typed_data _ _ _ tb2 H4) as [?[eqq2 typ2]].
          rewrite eqq2 in eqq; simpl in eqq.
          dtype_inverter.
          invcs H6.
          invcs H11.
          rtype_equalizer.
          subst.
          destruct (typed_nrc_yields_typed_data _ _ _ tb2 H13) as [?[eqq3 typ3]].
          rewrite eqq3 in eqq.
          destruct x1; simpl in eqq;
            apply none_lift in eqq; trivial.
        * subst.
          apply none_lift in eqq; trivial.
  Qed.
    
  Lemma tcount_over_flat_for_either_either_nil_arrow v e1 xl e11 xll e12 xrr xr ehead :
      tnrc_rewrites_to
        (♯count(♯flatten(NRCFor v
                                ehead (NRCEither e1 xl
                                           (NRCEither e11 xll (‵{| e12|}) xrr ‵{||}) xr ‵{||}))))
        (♯count(♯flatten(NRCFor v
                                ehead (NRCEither e1 xl
                                           (NRCEither e11 xll (‵{| ‵(dunit) |}) xrr ‵{||}) xr ‵{||})))).
  Proof.
    red; intros.
    invcs H.
    invcs H5.
    invcs H2.
    invcs H3.
    rtype_equalizer.
    subst.
    invcs H6.
    apply Coll_right_inv in H4.
    subst.
    invcs H5.
    invcs H9.
    split.
    - econstructor; [econstructor| ].
      econstructor; [econstructor | ].
      econstructor; eauto 2.
      econstructor.
      + eauto.
      + econstructor.
        * eauto.
        * repeat (econstructor; simpl). 
        * repeat (econstructor; simpl). 
      + repeat (econstructor; simpl). 
    - intros; simpl.
      destruct (typed_nrc_yields_typed_data _ _ _ H H2) as [?[eqq1 typ1]].
      rewrite eqq1; simpl.
      destruct x; simpl; trivial.
      clear eqq1 ehead H2.
      induction l; simpl; trivial.
      inversion typ1; clear typ1; rtype_equalizer. 
      subst.
      inversion H2; clear H2; subst.
      assert (typ1':dcoll l ▹ Coll τ₁)
        by (econstructor; trivial).
      clear H4.
      specialize (IHl typ1').
      casermap IHl; [ casermap IHl | ].
      + simpl.
        assert (bt2:bindings_type ((v, a) :: env) ((v, τ₁) :: τenv))
               by (econstructor; eauto).
        destruct (typed_nrc_yields_typed_data _ _ _ bt2 H8) as [?[eqq2 typ2]].
        rewrite eqq2.
        invcs H11.
        invcs H4.
        rtype_equalizer.
        subst.
        invcs typ2; rtype_equalizer.
        * subst.
          assert (tb12:bindings_type ((xl,d)::(v,a)::env) ((xl,τl)::(v,τ₁)::τenv))
            by (econstructor; eauto).
          destruct (typed_nrc_yields_typed_data _ _ _ tb12 H7) as [?[eqq12 typ12]].
          rewrite eqq12; simpl.
          { invcs typ12; rtype_equalizer.
            * subst.
              assert (tb122:bindings_type ((xll,d0)::(xl,d)::(v,a)::env) ((xll,τl0)::(xl,τl)::(v,τ₁)::τenv))
            by (econstructor; eauto).
          destruct (typed_nrc_yields_typed_data _ _ _ tb122 H6) as [?[eqq3 typ3]].
          rewrite eqq3.
          simpl.
          { case_eq (rflatten l0);
            [intros ? reqq0 | intros reqq0];
            rewrite reqq0 in IHl;
            (case_eq (rflatten l1);
             [intros ? reqq1 | intros reqq1];
             rewrite reqq1 in IHl); simpl in IHl; inversion IHl.
            - apply of_nat_inv in H1.
              rewrite (rflatten_cons _ _ _ reqq0);
                rewrite (rflatten_cons _ _ _ reqq1); simpl;
              congruence.
            - rewrite (rflatten_cons_none _ _ reqq0);
                rewrite (rflatten_cons_none _ _ reqq1); simpl; trivial.
          }
        * subst.
          { case_eq (rflatten l0);
            [intros ? reqq0 | intros reqq0];
            rewrite reqq0 in IHl;
            (case_eq (rflatten l1);
             [intros ? reqq1 | intros reqq1];
             rewrite reqq1 in IHl); simpl in IHl; inversion IHl;
            simpl.
            - apply of_nat_inv in H1.
              rewrite (rflatten_cons _ _ _ reqq0);
                rewrite (rflatten_cons _ _ _ reqq1); simpl;
                  congruence.
            - rewrite (rflatten_cons_none _ _ reqq0);
                rewrite (rflatten_cons_none _ _ reqq1); simpl; trivial.
          }
          }
        * subst.
          { case_eq (rflatten l0);
            [intros ? reqq0 | intros reqq0];
            rewrite reqq0 in IHl;
            (case_eq (rflatten l1);
             [intros ? reqq1 | intros reqq1];
             rewrite reqq1 in IHl); simpl in IHl; inversion IHl; simpl.
            - apply of_nat_inv in H1.
              rewrite (rflatten_cons _ _ _ reqq0);
                rewrite (rflatten_cons _ _ _ reqq1); simpl;
              congruence.
            - rewrite (rflatten_cons_none _ _ reqq0);
                rewrite (rflatten_cons_none _ _ reqq1); simpl; trivial.
          }
      + cut False; [intuition | ].
        clear eqq IHl.
        induction l; simpl in eqq0; try discriminate.
        inversion typ1'; clear typ1'; rtype_equalizer. 
        subst.
        inversion H2; clear H2; subst.
        assert (typ1':dcoll l ▹ Coll τ₁)
          by (econstructor; trivial).
        clear H5.
        apply (IHl typ1'); clear IHl.
        assert (tb:bindings_type ((v,a0)::env) ((v,τ₁)::τenv))
        by (econstructor; eauto).
        destruct (typed_nrc_yields_typed_data _ _ _ tb H8) as [?[eqq1 typ1]].
        rewrite eqq1 in eqq0; simpl in eqq0.
        destruct x; invcs typ1; rtype_equalizer.
        * subst.
          assert (tb2:bindings_type ((xl,x)::(v,a0)::env) ((xl,τl)::(v,τ₁)::τenv))
                 by (econstructor; eauto).
          destruct (typed_nrc_yields_typed_data _ _ _ tb2 H7) as [?[eqq2 typ2]].
          rewrite eqq2 in eqq0; simpl in eqq0.
          { invcs typ2; rtype_equalizer.
            * subst; simpl in eqq0.
              unfold lift in eqq0.
              match_destr_in eqq0.
            * subst; simpl in eqq0.
              unfold lift in eqq0.
              match_destr_in eqq0.
          }
        * subst.
          unfold lift in eqq0.
          match_destr_in eqq0.
      + cut False; [intuition | ].
        clear IHl.
        induction l; simpl in eqq; try discriminate.
        inversion typ1'; clear typ1'; rtype_equalizer. 
        subst.
        inversion H2; clear H2; subst.
        assert (typ1':dcoll l ▹ Coll τ₁)
          by (econstructor; trivial).
        clear H5.
        apply (IHl typ1'); clear IHl.
        assert (tb:bindings_type ((v,a0)::env) ((v,τ₁)::τenv))
        by (econstructor; eauto).
        destruct (typed_nrc_yields_typed_data _ _ _ tb H8) as [?[eqq1 typ1]].
        rewrite eqq1 in eqq; simpl in eqq.
        destruct x; inversion typ1; rtype_equalizer.
        * subst.
          assert (tb2:bindings_type ((xl,x)::(v,a0)::env) ((xl,τl)::(v,τ₁)::τenv))
                 by (econstructor; eauto).
          destruct (typed_nrc_yields_typed_data _ _ _ tb2 H7) as [?[eqq2 typ2]].
          rewrite eqq2 in eqq; simpl in eqq.
          { invcs typ2; rtype_equalizer.
            * subst.
              invcs H11.
              invcs H9.
              rtype_equalizer.
              subst.
              assert (tb12:bindings_type ((xll,d)::(xl,x)::(v,a0)::env) ((xll,τl0)::(xl,τl)::(v,τ₁)::τenv))
                 by (econstructor; eauto).
              destruct (typed_nrc_yields_typed_data _ _ _ tb12 H14) as [?[eqq12 typ12]].
              rewrite eqq12 in eqq.
              simpl in eqq.
              unfold lift in eqq.
              match_destr_in eqq.
            * subst; simpl in eqq.
              unfold lift in eqq.
              match_destr_in eqq.
          }
        * subst.
          unfold lift in eqq.
          match_destr_in eqq.
  Qed.

  (****************
   * ARecProject *
   ****************)
  
  Lemma tnrcproject_nil p :
    π[nil](p) ⇒ᶜ  ‵[||].
  Proof.
    red; simpl; intros.
    nrc_inverter.
    split.
    - econstructor. apply dtrec_full.
      simpl. rewrite rproject_nil_r; trivial.
    - intros.
      nrc_input_well_typed.
      dtype_inverter.
      rewrite rproject_nil_r.
      trivial.
  Qed.
  
  Lemma tnrcproject_over_concat_rec_r_in sl s p₁ p₂ :
    In s sl ->
    π[sl](p₁ ⊕ ‵[| (s, p₂) |]) ⇒ᶜ π[remove string_dec s sl](p₁) ⊕ ‵[| (s, p₂) |] .
  Proof.
    red; simpl; intros.
    nrc_inverter.
    split.
    - econstructor.
      3: econstructor; [| eauto]; eauto 2; econstructor.
      2: econstructor; [|eauto]; econstructor.
      + econstructor.
        unfold rec_concat_sort.
        rewrite rproject_rec_sort_commute, rproject_app.
        rewrite <- (rec_sort_rproject_remove_in s) by (simpl; intuition).
        simpl.
        destruct (in_dec string_dec s sl); [ | intuition ].
        trivial.
    + apply (sublist_remove equiv_dec s) in H1.
      rewrite remove_domain_filter in H1.
      unfold rec_concat_sort in H1.
      rewrite rec_sort_filter_fst_commute in H1 by (simpl; intuition).
      rewrite filter_app in H1; simpl in H1.
      unfold nequiv_decb, equiv_decb in H1.
      destruct (equiv_dec s s); [| congruence].
      simpl in H1.
      rewrite app_nil_r in H1.
      rewrite sort_sorted_is_id in H1.
      * rewrite H1.
        apply sublist_domain.
        apply filter_sublist.
      * apply sorted_over_filter; trivial.
    - intros.
      nrc_input_well_typed.
      destruct dout; simpl; trivial.
      rewrite rproject_rec_sort_commute, rproject_app.
      rewrite <- (rec_sort_rproject_remove_in s) by (simpl; intuition).
      simpl.
      destruct (in_dec string_dec s sl); simpl; intuition.
      Grab Existential Variables.
      { eapply is_list_sorted_sublist.
         - eapply pf0.
         - apply sublist_domain.
           apply sublist_rproject.
      }
      { simpl; trivial. }
  Qed.

   Lemma tnrcproject_over_const sl l :
    π[sl](NRCConst (drec l)) ⇒ᶜ NRCConst (drec (rproject l sl)).
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    - apply nrcproject_over_const.
    - intros.
      nrc_inverter.
      inversion H1; subst.
      rtype_equalizer. subst.
      econstructor.
      simpl.
      apply dtrec_full.
      rewrite <- rproject_map_fst_same; simpl; trivial.
      rewrite <- rproject_rec_sort_commute.
      eapply rproject_well_typed; try eassumption.
  Qed.
  
  Lemma tnrcproject_over_rec_in sl s p :
    In s sl ->
    π[sl](‵[| (s, p) |]) ⇒ᶜ ‵[| (s, p) |].
  Proof.
    intros.
    apply nrc_rewrites_typed_with_untyped.
    - apply nrcproject_over_rec_in; trivial.
    - intros.
      nrc_inverter.
      econstructor; eauto.
      destruct (@in_dec string string_dec
              s sl); [| intuition].
      econstructor.
  Qed.

  Lemma tnrcproject_over_rec_nin sl s p :
    ~ In s sl ->
    π[sl](‵[| (s, p) |]) ⇒ᶜ ‵[||].
  Proof.
    red; simpl; intros.
    nrc_inverter.
    split.
    - econstructor; eauto 2.
      econstructor; eauto 2.
      + reflexivity.
      + destruct (@in_dec string string_dec
                        s sl); [| intuition]; [intuition | ].
        simpl.
        econstructor; eauto.
    - intros.
      nrc_input_well_typed.
      destruct (@in_dec string string_dec
                        s sl); intuition.
  Qed.      
      
  Lemma tnrcproject_over_concat_rec_r_nin sl s p₁ p₂ :
    ~ In s sl ->
    π[sl](p₁ ⊕ ‵[| (s, p₂) |]) ⇒ᶜ π[sl](p₁).
  Proof.
    red; simpl; intros.
    nrc_inverter.
    split.
    - econstructor; [ | eauto].
      revert pf2.
      unfold rec_concat_sort.
      rewrite rproject_rec_sort_commute, rproject_app.
      simpl.
      destruct (in_dec string_dec s sl); [intuition | ].
      rewrite app_nil_r.
      rewrite sort_sorted_is_id.
      + intros. econstructor.
        apply (sublist_nin_remove equiv_dec _ _ _ n) in H1.
        rewrite remove_domain_filter in H1.
        unfold rec_concat_sort in H1.
        rewrite rec_sort_filter_fst_commute in H1 by (simpl; intuition).
        rewrite filter_app in H1; simpl in H1.
        unfold nequiv_decb, equiv_decb in H1.
        destruct (equiv_dec s s); [| congruence].
        simpl in H1.
        rewrite app_nil_r in H1.
        rewrite sort_sorted_is_id in H1.
        * rewrite H1.
          apply sublist_domain.
          apply filter_sublist.
        * apply sorted_over_filter; trivial.
      + apply sorted_over_filter; trivial.
    - intros.
      nrc_input_well_typed.
      destruct dout; simpl; trivial.
      rewrite rproject_rec_sort_commute, rproject_app.
      simpl.
      destruct (in_dec string_dec s sl); simpl; [intuition | ].
      rewrite app_nil_r.
      rewrite sort_sorted_is_id; trivial.
      apply sorted_over_filter; trivial.
      apply data_type_normalized in τout.
      inversion τout; trivial.
  Qed.

  Lemma tnrcproject_over_concat_rec_l_nin sl s p₁ p₂ :
    ~ In s sl ->
    π[sl](‵[| (s, p₁) |] ⊕ p₂) ⇒ᶜ π[sl](p₂).
  Proof.
    red; intros.
    nrc_inverter.
    split.
    - econstructor; [ | eauto].
      revert pf2.
      unfold rec_concat_sort.
      rewrite rproject_rec_sort_commute, rproject_app.
      simpl.
      destruct (in_dec string_dec s sl); [intuition | ].
      simpl.
      rewrite sort_sorted_is_id.
      + intros. econstructor.
        apply (sublist_nin_remove equiv_dec _ _ _ n) in H1.
        rewrite remove_domain_filter in H1.
        unfold rec_concat_sort in H1.
        rewrite rec_sort_filter_fst_commute in H1 by (simpl; intuition).
        rewrite filter_app in H1; simpl in H1.
        unfold nequiv_decb, equiv_decb in H1.
        destruct (equiv_dec s s); [| congruence].
        simpl in H1.
        rewrite sort_sorted_is_id in H1.
        * rewrite H1.
          apply sublist_domain.
          apply filter_sublist.
        * apply sorted_over_filter; trivial.
      + apply sorted_over_filter; trivial.
    - intros.
      nrc_input_well_typed.
      destruct dout0; trivial.
      simpl.
      replace (insertion_sort_insert rec_field_lt_dec (s, dout) (rec_sort l)) with
      (rec_sort ((s,dout)::l)) by reflexivity.
      rewrite rproject_rec_sort_commute.
      simpl.
      destruct (in_dec string_dec s sl); simpl; [intuition | ].
      rewrite sort_sorted_is_id; trivial.
      apply sorted_over_filter; trivial.
      apply data_type_normalized in τout0.
      inversion τout0; trivial.
  Qed.

    Lemma tnrcproject_over_concat_recs_in_in sl s₁ p₁ s₂ p₂ :
      In s₁ sl -> In s₂ sl ->
      π[sl](‵[| (s₁, p₁) |] ⊕ ‵[| (s₂, p₂) |]) ⇒ᶜ ‵[| (s₁, p₁) |] ⊕ ‵[| (s₂, p₂) |].
    Proof.
      intros.
      apply nrc_rewrites_typed_with_untyped.
      - rewrite nrcproject_over_concat.
        repeat rewrite nrcproject_over_rec_in by trivial.
        reflexivity.
      - intros.
        nrc_inverter.
        econstructor; eauto 2.
        2: repeat (econstructor; eauto 2).
        2: repeat (econstructor; eauto 2).
        econstructor; eauto.
        unfold rec_concat_sort.
        rewrite rproject_rec_sort_commute, rproject_app.
        simpl.
        destruct (in_dec string_dec s sl); [| intuition ].
        destruct (in_dec string_dec s1 sl); [| intuition ].
        reflexivity.
      Grab Existential Variables.
      solve[eauto].
      solve[eauto].
    Qed.
  
  Lemma tnrcproject_over_nrcproject sl1 sl2 p :
    π[sl1](π[sl2](p)) ⇒ᶜ π[set_inter string_dec sl2 sl1](p).
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    - apply nrcproject_over_nrcproject.
    - intros.
      nrc_inverter.
      generalize pf3.
      rewrite (rproject_rproject τ sl1 sl2).
      econstructor; eauto.
      econstructor.
      apply sublist_set_inter.
      trivial.
  Qed.

  Lemma tnrcproject_over_either sl p xl p1 xr p2 :
    π[sl](NRCEither p xl p1 xr p2) ⇒ᶜ NRCEither p xl (π[sl](p1)) xr (π[sl](p2)).
  Proof.
    apply nrc_rewrites_typed_with_untyped.
    - apply nrcproject_over_either.
    - intros.
      nrc_inverter.
      repeat (econstructor; eauto 2).
  Qed.

End TRew.

Hint Rewrite @tsigma_to_if_arrow : nrc_rew.
Hint Rewrite @tfor_singleton_to_let_arrow : nrc_rew.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
