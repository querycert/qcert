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
Require Import Arith.
Require Import Lia.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import DataSystem.
Require Import OQLSystem.
Require Import NRAEnvSystem.
Require Import OQLtoNRAEnv.

Section TOQLtoNRAEnv.
  Context {m:basic_model}.

  Lemma oql_to_nraenv_from_in_expr_type_preserve_f τconstant τenv τenv1 tenv' τdefls e0 v e pfe pfe0 pfd pf':
    (forall (τconstant τdefls : list (string * rtype))
         (pfd : is_list_sorted StringOrder.lt_dec (domain τdefls) = true) 
         (τenv : tbindings) (pfe : is_list_sorted StringOrder.lt_dec (domain τenv) = true)
         (τout : rtype),
       oql_expr_type (rec_concat_sort τconstant τdefls) τenv e τout ->
       nraenv_to_nraenv_core (oql_to_nraenv_expr (domain τdefls) e) ▷ 
       Rec Closed τenv pfe >=> τout ⊣ τconstant; Rec Closed τdefls pfd) ->
    (nraenv_to_nraenv_core e0 ▷ Rec Closed τenv pfe >=> Coll (Rec Closed τenv1 pfe0)
                           ⊣ τconstant; Rec Closed τdefls pfd) ->
    (oql_from_in_expr_type (rec_concat_sort τconstant τdefls) v e τenv1 tenv') ->
    (nraenv_to_nraenv_core
       (NRAEnvMapProduct
          (NRAEnvMap (NRAEnvUnop (OpRec v) NRAEnvID) (oql_to_nraenv_expr (domain τdefls) e)) e0)
       ▷ Rec Closed τenv pfe >=> Coll (Rec Closed tenv' pf') ⊣ τconstant; Rec Closed τdefls pfd).
  Proof.
    intros.
    inversion H1; subst; simpl.
    repeat econstructor.
    + apply H. apply H2.
    + apply H0.
      Unshelve.
      constructor.
  Qed.

  Lemma oql_to_nraenv_from_expr_type_preserve_f τconstant τenv τenv1 e0 el from_tenv τdefls pfd pfe pfe0 pfet :
    nraenv_to_nraenv_core e0 ▷ Rec Closed τenv pfe >=> Coll (Rec Closed τenv1 pfe0)
  ⊣ τconstant; Rec Closed τdefls pfd ->
    oql_from_expr_type (rec_concat_sort τconstant τdefls) τenv1 el from_tenv ->
    Forall
      (fun ab : oql_in_expr =>
         forall (τconstant τdefls : list (string * rtype))
                (pfd : is_list_sorted StringOrder.lt_dec (domain τdefls) = true) 
                (τenv : tbindings) (pfe : is_list_sorted StringOrder.lt_dec (domain τenv) = true)
                (τout : rtype),
           oql_expr_type (rec_concat_sort τconstant τdefls) τenv (oin_expr ab) τout ->
           nraenv_to_nraenv_core (oql_to_nraenv_expr (domain τdefls) (oin_expr ab))
                                 ▷ Rec Closed τenv pfe >=> τout ⊣ τconstant; Rec Closed τdefls pfd) el ->
    nraenv_to_nraenv_core
      (fold_left
         (fun (opacc : nraenv) (from_in_expr : oql_in_expr) =>
            match from_in_expr with
            | OIn in_v from_expr =>
              NRAEnvMapProduct
                (NRAEnvMap (NRAEnvUnop (OpRec in_v) NRAEnvID)
                           (oql_to_nraenv_expr (domain τdefls) from_expr)) opacc
            | OInCast in_v brand_name from_expr =>
              NRAEnvMapProduct
                (NRAEnvMap (NRAEnvUnop (OpRec in_v) NRAEnvID)
                           (NRAEnvUnop OpFlatten
                                       (NRAEnvMap
                                          (NRAEnvEither (NRAEnvUnop OpBag NRAEnvID) (NRAEnvConst (dcoll nil)))
                                          (NRAEnvMap (NRAEnvUnop (OpCast (brand_name :: nil)) NRAEnvID)
                                                     (oql_to_nraenv_expr (domain τdefls) from_expr))))) opacc
            end) el e0) ▷ Rec Closed τenv pfe >=>
      Coll (Rec Closed from_tenv pfet) ⊣ τconstant; Rec Closed τdefls pfd.
  Proof.
    intros He0.
    intros.
    revert τenv τenv1 from_tenv e0 pfe pfe0 pfet H He0.
    induction el; simpl in *; intros.
    - invcs H.
      assert (Rec Closed from_tenv pfe0 = Rec Closed from_tenv pfet) by
          apply Rec_pr_irrel.
      rewrite <- H.
      apply He0.
    - inversion H0; subst; intros; clear H0.
      inversion H; subst; intros; clear H.
      assert (is_list_sorted StringOrder.lt_dec (domain tenv') = true) by
          (apply (oql_from_in_type_sorted (rec_concat_sort τconstant τdefls) τenv1 v e tenv');
           try assumption).
      apply (IHel H4 τenv tenv' from_tenv
                  (NRAEnvMapProduct
                     (NRAEnvMap (NRAEnvUnop (OpRec v) NRAEnvID)
                                (oql_to_nraenv_expr (domain τdefls) e)) e0) pfe H pfet H7)
      ; clear IHel H4.
      simpl in H3.
      apply (oql_to_nraenv_from_in_expr_type_preserve_f τconstant τenv τenv1 tenv'
                  τdefls e0 v e pfe pfe0 pfd H); assumption.
  Qed.

  Lemma oql_to_nraenv_expr_type_preserve_f τconstant τdefls pfd τenv pfe e τout:
    oql_expr_type (rec_concat_sort τconstant τdefls) τenv e τout ->
    nraenv_type τconstant (oql_to_nraenv_expr (domain τdefls) e) (Rec Closed τdefls pfd) (Rec Closed τenv pfe) τout.
  Proof.
    unfold nraenv_type; simpl.
    Local Hint Constructors nraenv_core_type : qcert.
    revert τconstant τdefls pfd τenv pfe τout.
    induction e; simpl; intros τconstant τdefls pfd τenv pfe τout ot; invcs ot;
      eauto 4 with qcert.
    - unfold lookup_table.
      unfold tdot, edot, rec_concat_sort in *.
      rewrite assoc_lookupr_drec_sort in H1.
      rewrite (assoc_lookupr_app τconstant τdefls _ ODT_eqdec) in H1.
      match_destr; simpl; intros.
      + econstructor; [ | qeauto].
        apply in_dom_lookupr with (dec:=ODT_eqdec) in i.
        destruct i as [? ?].
        match_case_in H1; [intros ? eqq | intros eqq]; rewrite eqq in H1.
        * invcs H1.
          qeauto.
        * congruence.
      + constructor.
        apply assoc_lookupr_nin_none with (dec:=ODT_eqdec) in n.
        rewrite n in H1; trivial.
    - destruct e1.
      + simpl in *.
        invcs H5; econstructor; qeauto.
        invcs H2; apply IHe; apply H0.
        apply (oql_to_nraenv_from_expr_type_preserve_f
                 τconstant τenv τenv
                 (NRAEnvUnop OpBag NRAEnvID) el from_tenv τdefls pfd pfe pfe);
          try assumption; qeauto.
        Unshelve.
        apply (oql_from_type_sorted (rec_concat_sort τconstant τdefls) τenv el from_tenv);
          assumption.
      + simpl in *.
        invcs H5; econstructor; [econstructor| ].
        invcs H2; econstructor; [apply IHe; apply H0| ]; try assumption.
        apply (oql_to_nraenv_from_expr_type_preserve_f
                 τconstant τenv τenv
                 (NRAEnvUnop OpBag NRAEnvID) el from_tenv τdefls pfd pfe pfe);
          try assumption; qeauto.
        Unshelve.
        apply (oql_from_type_sorted (rec_concat_sort τconstant τdefls) τenv el from_tenv);
          assumption.
  Qed.

  Lemma oql_to_nraenv_query_program_type_preserve_f τconstant τdefls pfd τenv pfe oq τout:
    oql_query_program_type τconstant τdefls τenv oq τout ->
    nraenv_type τconstant (oql_to_nraenv_query_program (domain τdefls) oq) (Rec Closed τdefls pfd) (Rec Closed τenv pfe) τout.
  Proof.
    unfold nraenv_type; simpl.
    Local Hint Constructors nraenv_core_type : qcert.
    revert τdefls pfd τenv pfe τout.
    induction oq; simpl; intros τdefls pfd τenv pfe τout ot; invcs ot.
    - econstructor.
      + econstructor; qeauto.
        econstructor; qeauto.
        apply oql_to_nraenv_expr_type_preserve_f; eauto.
      + specialize (IHoq (rec_concat_sort τdefls ((s, τ₁) :: nil))).
        assert (eqls:equivlist (s :: domain τdefls) (domain (rec_concat_sort τdefls ((s, τ₁) :: nil))))
          by (rewrite rec_concat_sort_domain_app_commutatuve_equiv; simpl; reflexivity).
        rewrite eqls.
        apply IHoq; trivial.
    - econstructor; qeauto.
      rewrite <- domain_rremove; trivial.
      auto.
    - apply oql_to_nraenv_expr_type_preserve_f; trivial.
      Unshelve.
      solve[simpl; trivial].
      solve[qeauto].
      solve[apply is_sorted_rremove; trivial].
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
   nraenv_type τconstant (oql_to_nraenv_expr (domain τdefls) e) (Rec Closed τdefls pfd) (Rec Closed  τenv pfe) τout ->
   oql_expr_type (rec_concat_sort τconstant τdefls) τenv e τout.
   Proof.
   Local Hint Constructors oql_expr_type.
   unfold nraenv_type; simpl.
   revert τconstant τdefls pfd τenv pfe τout.
   induction e; simpl; intros τconstant τdefls pfd τenv pfe τout ot; try nraenv_core_inverter; eaut o 4.
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
