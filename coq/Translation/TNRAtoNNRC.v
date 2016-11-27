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

Section TNRAtoNNRC.

  Require Import String.
  Require Import List.
  Require Import EquivDec.
  Require Import Compare_dec.
  Require Import Program.
  
  Require Import Utils BasicSystem.
  Require Import NRASystem.
  Require Import NNRCSystem.

  Require Import NRAtoNNRC.

  (** Type preservation for the translation from NRA to NNRC *)

  Context {m:basic_model}.
  Theorem tnra_sem_correct {τin τout} (op:alg) (tenv:tbindings) (v:var) :
    (op ▷ τin >=> τout) ->
    lookup equiv_dec tenv v = Some τin ->
    nrc_type tenv (nra_to_nnrc op v) τout.
  Proof.
    Opaque fresh_var.
    intros.
    revert v tenv H0. 
    dependent induction H; simpl; intros.
    (* ATID *)
    - apply TNRCVar.
      assumption.
    (* ATConst *)
    - apply TNRCConst.
      assumption.
    (* ATBinop *)
    - specialize (IHalg_type1 v tenv H2); specialize (IHalg_type2 v tenv H2).
      apply (@TNRCBinop m τ₁ τ₂); assumption.
    (* ATUnop *)
    - specialize (IHalg_type v tenv H1).
      apply (@TNRCUnop m τ); assumption.
    (* ATMap *)
    - specialize (IHalg_type2 v tenv H1).
      apply (@TNRCFor m τ₁); try assumption.
      specialize (IHalg_type1 (fresh_var "tmap$" [v]) ((fresh_var "tmap$" [v],τ₁)::tenv)).
      simpl in *.
      revert IHalg_type1.
      dest_eqdec; try congruence.
      intros.
      apply IHalg_type1; trivial.
    (* ATMapConcat *)
    - specialize (IHalg_type2 v tenv H2).
      apply (@TNRCUnop m (RType.Coll (RType.Coll (RType.Rec Closed τ₃ pf3)))).
      apply ATFlatten.
      apply (@TNRCFor m (RType.Rec Closed τ₁ pf1)); try assumption.
      apply (@TNRCFor m (RType.Rec Closed τ₂ pf2)).
      specialize (IHalg_type1 (fresh_var "tmc$" [v]) (((fresh_var "tmc$" [v]), RType.Rec Closed τ₁ pf1) :: tenv)).
      assert (lookup equiv_dec (((fresh_var "tmc$" [v]), RType.Rec Closed τ₁ pf1) :: tenv) (fresh_var "tmc$" [v]) =
              Some (RType.Rec Closed τ₁ pf1)).
      simpl; match_destr; try congruence.
      specialize (IHalg_type1 H3); clear H3.
      assumption.
      apply (@TNRCBinop m (RType.Rec Closed τ₁ pf1) (RType.Rec Closed τ₂ pf2)).
      apply ATConcat; assumption.
      + apply TNRCVar; simpl.
        dest_eqdec; try congruence.
        elim (fresh_var2_distinct _ _ _ e).
        dest_eqdec; try congruence.
      + apply TNRCVar; simpl.
        dest_eqdec; try congruence.
    (* ATProduct *)
    - specialize (IHalg_type1 v tenv H2).
      apply (@TNRCUnop m (RType.Coll (RType.Coll (RType.Rec Closed τ₃ pf3)))).
      apply ATFlatten.
      apply (@TNRCFor m (RType.Rec Closed τ₁ pf1)); try assumption.
      apply (@TNRCFor m (RType.Rec Closed τ₂ pf2)).
      assert (lookup equiv_dec ((fresh_var "tprod$" [v], RType.Rec Closed τ₁ pf1) :: tenv) v =
              Some τin).
      simpl. match_destr; try congruence.
      elim (fresh_var_fresh1 _ _ _ e).
      specialize (IHalg_type2 v ((_, RType.Rec Closed τ₁ pf1) :: tenv) H3).
      assumption.
      apply (@TNRCBinop m (RType.Rec Closed τ₁ pf1) (RType.Rec Closed τ₂ pf2)).
      apply ATConcat; assumption.
      + apply TNRCVar; simpl.
        dest_eqdec; try congruence.
        elim (fresh_var_fresh1 _ _ _ e).
        dest_eqdec; try congruence.
      + apply TNRCVar; simpl.
        dest_eqdec; try congruence.
    (* ATSelect *)
    - apply (@TNRCUnop m (RType.Coll (RType.Coll τ))); [apply ATFlatten|idtac].
      apply (@TNRCFor m τ); [apply (IHalg_type2 v tenv H1)|idtac].
      apply TNRCIf.
      apply (IHalg_type1 _ ((_, τ) :: tenv)).
      simpl; match_destr; try congruence.
      apply (@TNRCUnop m τ); [apply ATColl|apply TNRCVar].
      simpl; match_destr; try congruence.
      apply TNRCConst; simpl.
      apply TData.dtcoll; apply Forall_nil.
    (* ATDefault *)
    - econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      Focus 2. econstructor; eauto.
      simpl.
      dest_eqdec; try reflexivity.
      congruence.
      repeat econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      apply Forall_nil.
      apply IHalg_type2.
      simpl. match_destr; try congruence.
      elim (fresh_var_fresh1 _ _ _ e).
      econstructor; eauto.
      simpl; match_destr; try congruence.
    (* ATEither *)
    - repeat (econstructor; eauto);
      [apply IHalg_type1 | apply IHalg_type2]; simpl;
      match_destr; congruence.
    (* ATEitherConcat *)
    - repeat (econstructor; eauto).
      + apply IHalg_type1; simpl. match_destr.
        elim (fresh_var_fresh1 _ _ _ e).
      + simpl; match_destr; try congruence. 
      + simpl; match_destr.
        * elim (fresh_var_fresh1 _ _ _ (symmetry e)).
        * match_destr; try congruence.
      + simpl. match_destr; try congruence.
      + simpl; match_destr.
        * elim (fresh_var_fresh1 _ _ _ (symmetry e)).
        * match_destr; try congruence.
    (* ATApp *)
    - repeat (econstructor; eauto).
      apply IHalg_type2.
      simpl; match_destr; try congruence.
  Qed.

  (** Reverse direction, main theorem *)

  Theorem tnra_sem_correct_back {τin τout} (op:alg) (tenv:tbindings) (v:var) :
    nrc_type tenv (nra_to_nnrc op v) τout ->
    lookup equiv_dec tenv v = Some τin ->
    (op ▷ τin >=> τout).
  Proof.
    Hint Constructors alg_type.
    intros.
    revert v tenv τin τout H H0.
    induction op; simpl; intros; inversion H; subst.
    (* AID *)
    - rewrite H0 in H3; inversion H3; subst. eauto.
    (* AConst *)
    - eauto.
    (* ABinop *)
    - eauto. 
    (* AUnop *)
    - eauto.
    (* AMap *)
    - specialize (IHop2 _ _ _ _ H6 H0).
      econstructor; eauto.
      eapply (IHop1 _ _ _ _ H7).
      simpl; match_destr; try congruence.
    (* AMapConcat *)
    - inversion H6; subst.
      specialize (IHop2 _ _ _ _ H8 H0).
      inversion H9; subst.
      inversion H11; subst.
      inversion H13; subst.
      inversion H14; subst.
      simpl in H3,H5.
      generalize (fresh_var2_distinct "tmc$" "tmc$" [v]); simpl.
      match_destr_in H3; [intuition | ].
      match_destr_in H3; try congruence.
      match_destr_in H5; try congruence.
      inversion H3; inversion H5.
      subst.
      inversion H7; subst.
      clear H3 H13 H14 H5.
      inversion H4; subst.
      destruct τ; simpl in *.
      subst.
      destruct (to_Rec Closed (rec_concat_sort τ₁ τ₂1) e1) as [? rr].
      rewrite rr.
      econstructor; eauto.
      eapply IHop1; eauto.
      simpl; match_destr; congruence.
    (* AProduct *)
    - inversion H4; subst.
      inversion H6; subst.
      specialize (IHop1 _ _ _ _ H5 H0).
      destruct τ₂; simpl in *.
      subst.
      inversion H9; subst.
      rtype_equalizer.
      subst.
      inversion H11; subst.
      inversion H13; inversion H14; subst.
      generalize (fresh_var2_distinct "tprod$" "tprod$" [v]).
      simpl in H3, H16.
      match_destr_in H3; [ intuition | ].
      match_destr_in H3; try congruence.
      match_destr_in H16; try congruence.
      inversion H3; inversion H16; subst.
      inversion H10; subst.
      econstructor; eauto.
      eapply IHop2; eauto.
      simpl; match_destr.
      elim (fresh_var_fresh1 _ _ _ e2).
  (* ASelect *)
    - inversion H4; subst.
      inversion H6; subst.
      inversion H9; subst.
      inversion H13; subst.
      inversion H12; subst.
      inversion H15; subst.
      simpl in H7.
      match_destr_in H7; try congruence.
      inversion H7; subst; clear H7.
      inversion H11; subst.
      inversion H8.
      assert (τ₁0 = τ) by (apply rtype_fequal; assumption).
      subst.
      clear H2 H8.
      inversion H3; subst.
      rtype_equalizer. subst.
      econstructor.
      + eapply IHop1; eauto.
        simpl; match_destr; congruence.
      + eapply IHop2; eauto.
    (* ADefault *)
  - inversion H7; subst; clear H7.
    inversion H10; subst. inversion H5; subst.
    inversion H8; inversion H12; inversion H13;
      subst; clear H5 H10 H8 H12 H13.
    simpl in H3, H11.
    match_destr_in H3; try congruence.
    invcs H3; invcs H11.
    invcs H18.
    econstructor; eauto 2.
    eapply IHop2; eauto.
    simpl; match_destr; try congruence.
    elim (fresh_var_fresh1 _ _ _ e0).
  (* AEither *)
  - inversion H8; subst.
    specialize (IHop1 _ _ τl _ H9).
    specialize (IHop2 _ _ τr _ H10).
    simpl in IHop1, IHop2.
    match_destr_in IHop1; try congruence.
    rewrite H0 in H3. inversion H3; subst.
    eauto.
  (* AEitherConcat *)
  - clear H. inversion H7; subst; clear H7.
    specialize (IHop2 _ _ _ _ H6 H0).
    inversion H10; clear H10; subst.
    inversion H3; clear H3; subst.
    inversion H11; clear H11; subst.
    inversion H3; clear H3; subst.
    rtype_equalizer. subst.
    inversion H5; clear H5; subst.
    inversion H4; clear H4; subst.
    inversion H7; clear H7; subst.
    inversion H4; clear H4; subst.
    inversion H8; clear H8; subst.
    inversion H12; clear H12; subst.
    inversion H10; clear H10; subst.
    inversion H11; clear H11; subst.
    simpl in H3,H5.
    match_destr_in H3.
    elim (fresh_var_fresh1 _ _ _ (symmetry e)).
    match_destr_in H5; try congruence.
    simpl in * .
    match_destr_in H2; try congruence.
    inversion H2; inversion H3;
    inversion H4; inversion H5; subst.
    clear H2 H3 H4 H5.
    specialize (IHop1 _ _ τin _ H9).
    simpl in IHop1.
    match_destr_in IHop1.
    elim (fresh_var_fresh1 _ _ _ e1).
    specialize (IHop1 H0).
    apply Rec_inv in H10. subst.
    econstructor; eauto.
    (* AApp *)
  - inversion H; subst; clear H.
    econstructor.
    eapply IHop2; eauto.
    eapply IHop1; simpl. eauto.
    simpl; match_destr; try congruence.
  Qed.

  (** Theorem 7.4: NRA<->NNRC.
       Final iff Theorem of type preservation for the translation from NRA to NNRC *)

  Theorem tnra_sem_correct_iff {τin τout} (op:alg) (tenv:tbindings) (v:var) :
    lookup equiv_dec tenv v = Some τin ->
    (nrc_type tenv (nra_to_nnrc op v) τout <->
    (op ▷ τin >=> τout)).
  Proof.
    Hint Resolve tnra_sem_correct tnra_sem_correct_back.
    intuition; eauto.
  Qed.

End TNRAtoNNRC.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
