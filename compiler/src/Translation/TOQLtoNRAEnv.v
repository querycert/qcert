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
Require Import Arith.
Require Import Omega.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonSystem.
Require Import OQLSystem.
Require Import NRAEnvSystem.
Require Import OQLtoNRAEnv.

Section TOQLtoNRAEnv.
  Context {m:basic_model}.

    Lemma oql_to_nraenv_expr_type_preserve_f τconstant τdefls pfd τenv pfe e τout:
      oql_expr_type (rec_concat_sort τconstant τdefls) τenv e τout ->
      nraenv_type τconstant (oql_to_nraenv_expr (domain τdefls) e) (Rec Closed τdefls pfd) (Rec Closed τenv pfe) τout.
    Proof.
      unfold nraenv_type; simpl.
      Hint Constructors nraenv_core_type.
      revert τconstant τdefls pfd τenv pfe τout.
      induction e; simpl; intros τconstant τdefls pfd τenv pfe τout ot; invcs ot; eauto 4.
      - unfold lookup_table.
          unfold tdot, edot, rec_concat_sort in *.
          rewrite assoc_lookupr_drec_sort in H1.
          rewrite (assoc_lookupr_app τconstant τdefls _ ODT_eqdec) in H1.
        match_destr; simpl; intros.
        + econstructor; [ | eauto].
          apply in_dom_lookupr with (dec:=ODT_eqdec) in i.
          destruct i as [? ?].
          match_case_in H1; [intros ? eqq | intros eqq]; rewrite eqq in H1.
          * invcs H1.
            eauto.
          * congruence.
        + constructor.
          apply assoc_lookupr_nin_none with (dec:=ODT_eqdec) in n.
          rewrite n in H1; trivial.
    Qed.

    Lemma oql_to_nraenv_query_program_type_preserve_f τconstant τdefls pfd τenv pfe oq τout:
      oql_query_program_type τconstant τdefls τenv oq τout ->
      nraenv_type τconstant (oql_to_nraenv_query_program (domain τdefls) oq) (Rec Closed τdefls pfd) (Rec Closed τenv pfe) τout.
    Proof.
      unfold nraenv_type; simpl.
      Hint Constructors nraenv_core_type.
      revert τdefls pfd τenv pfe τout.
      induction oq; simpl; intros τdefls pfd τenv pfe τout ot; invcs ot.
      - econstructor.
        + econstructor; eauto.
          econstructor; eauto.
          apply oql_to_nraenv_expr_type_preserve_f; eauto.
        + specialize (IHoq (rec_concat_sort τdefls ((s, τ₁) :: nil))).
          assert (eqls:equivlist (s :: domain τdefls) (domain (rec_concat_sort τdefls ((s, τ₁) :: nil))))
            by (rewrite rec_concat_sort_domain_app_commutatuve_equiv; simpl; reflexivity).
          rewrite eqls.
          apply IHoq; trivial.
      - econstructor; eauto.
        rewrite <- domain_rremove; trivial.
        auto.
      - apply oql_to_nraenv_expr_type_preserve_f; trivial.
        Grab Existential Variables.
        solve[apply is_sorted_rremove; trivial].
        solve[eauto].
        solve[simpl; trivial].
    Qed.

    Theorem oql_to_nraenv_type_preserve_f τconstant oq τout :
      oql_type τconstant oq τout ->
      forall τenv τdata,
      nraenv_type τconstant (oql_to_nraenv oq) τenv τdata τout.
    Proof.
      intros ot τenv τdata.
      unfold oql_to_nraenv, nraenv_type; simpl.
      generalize (oql_to_nraenv_query_program_type_preserve_f τconstant nil sorted_rec_nil nil sorted_rec_nil oq τout ot); intros et.
      simpl in et.
      unfold nraenv_type in et.
      econstructor; econstructor; try eassumption; repeat econstructor;
        try apply sorted_rec_nil.
    Qed.

    (* TODO (backwards preservation)
    Lemma oql_to_nraenv_expr_type_preserve_b τconstant τdefls pfd τenv pfe e τout:
      nraenv_type τconstant (oql_to_nraenv_expr (domain τdefls) e) (Rec Closed τdefls pfd) (Rec Closed τenv pfe) τout ->
      oql_expr_type (rec_concat_sort τconstant τdefls) τenv e τout.
    Proof.
      Hint Constructors oql_expr_type.
      unfold nraenv_type; simpl.
      revert τconstant τdefls pfd τenv pfe τout.
      induction e; simpl; intros τconstant τdefls pfd τenv pfe τout ot; try nraenv_core_inverter; eauto 4.
      - unfold lookup_table in *.
        constructor.
        unfold tdot, edot, rec_concat_sort.
        rewrite assoc_lookupr_drec_sort.
        rewrite (assoc_lookupr_app τconstant τdefls _ ODT_eqdec).
        match_destr_in ot.
        + invcs ot.
          invcs H1.
          invcs H5.
          rtype_equalizer.
          subst.
          apply in_dom_lookupr with (dec:=ODT_eqdec) in i.
          destruct i as [? ?].
          rewrite H.
          unfold tdot, edot in H0.
          unfold equiv, complement in H0.
          unfold not in H.
          congruence.
        + apply assoc_lookupr_nin_none with (dec:=ODT_eqdec) in n.
          rewrite n.
          invcs ot.
          apply H0.
      -
    Qed.
*)
        
End TOQLtoNRAEnv.

