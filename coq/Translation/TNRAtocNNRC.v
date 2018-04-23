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
Require Import EquivDec.
Require Import Compare_dec.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import NRASystem.
Require Import cNNRCSystem.
Require Import NRAtocNNRC.

Section TNRAtocNNRC.
  (** Type preservation for the translation from NRA to NNRC *)

  Ltac elim_fresh e
    := solve[(congruence
            || apply fresh_var_fresh1 in e
            || apply fresh_var_fresh2 in e
            || apply fresh_var_fresh3 in e
            || apply fresh_var_fresh4 in e); intuition].
  
  Context {m:basic_model}.
  Context (τconstants:tbindings).

  Local Open Scope nra_scope.

  Theorem tnra_sem_correct {τin τout} (op:nra) (tenv:tbindings) (vid:var) :
    lookup equiv_dec tenv vid = Some τin ->
    (op ▷ τin >=> τout ⊣ τconstants) ->
    nnrc_core_type τconstants tenv (nra_to_nnrc_core op vid) τout.
  Proof.
    Hint Constructors nra_type.
    Opaque fresh_var.
    intros.
    revert vid tenv H.
    dependent induction H0; simpl; intros.
    (* type_NRAGetConstant *)
    - econstructor; eauto 2.
    (* type_NRAID *)
    - apply type_cNNRCVar; trivial.
    (* type_NRAConst *)
    - apply type_cNNRCConst; trivial.
    (* type_NRABinop *)
    - econstructor; eauto.
    (* type_NRAUnop *)
    - econstructor; eauto.
    (* type_NRAMap *)
    - econstructor; [eauto| ].
      apply (IHnra_type1 
               (fresh_var "tmap$" [vid])
               ((fresh_var "tmap$" [vid],τ₁)::tenv)); simpl; trivial.
      + dest_eqdec; congruence.
    (* type_NRAMapProduct *)
    - specialize (IHnra_type2 vid tenv).
      apply (@type_cNNRCUnop m _ (RType.Coll (RType.Coll (RType.Rec Closed τ₃ pf3)))).
      apply type_OpFlatten.
      apply (@type_cNNRCFor m _ (RType.Rec Closed τ₁ pf1)); [eauto | ].
      apply (@type_cNNRCFor m _ (RType.Rec Closed τ₂ pf2)).
      + apply IHnra_type1; simpl; trivial;
        match_destr; try elim_fresh e.
      + econstructor; econstructor; eauto 2; simpl; match_destr; try elim_fresh e.
        match_destr; elim_fresh e.
    (* type_NRAProduct *)
    - apply (@type_cNNRCUnop m _ (RType.Coll (RType.Coll (RType.Rec Closed τ₃ pf3)))).
      apply type_OpFlatten.
      apply (@type_cNNRCFor m _ (RType.Rec Closed τ₁ pf1)); try assumption.
      apply (IHnra_type1 vid tenv); assumption.
      clear IHnra_type1 op1 H0_.
      apply (@type_cNNRCFor m _ (RType.Rec Closed τ₂ pf2)).
      + apply IHnra_type2; simpl; trivial; match_destr; try elim_fresh e.
      + econstructor; econstructor; eauto 2; simpl.
        * match_destr.
          elim_fresh e.
          match_destr; congruence.
        * match_destr; try congruence.
    (* type_NRASelect *)
    - apply (@type_cNNRCUnop m _ (RType.Coll (RType.Coll τ))); [apply type_OpFlatten|idtac].
      apply (@type_cNNRCFor m _ τ); [apply (IHnra_type2 vid tenv )|idtac]; trivial.
      apply type_cNNRCIf.
      + apply IHnra_type1; simpl; trivial; match_destr; elim_fresh e.
      + econstructor; eauto.
        repeat econstructor. simpl.
        repeat econstructor.
        simpl.
        match_destr; intuition.
      + econstructor. simpl. repeat econstructor.
    (* type_NRADefault *)
    - econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      + simpl. repeat econstructor. simpl. match_destr; congruence.
      + econstructor. econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
        eapply Forall_nil.
      + apply IHnra_type2; simpl; trivial; match_destr; elim_fresh e.
      + econstructor; eauto.
        simpl; match_destr; elim_fresh e.
    (* type_NRAEither *)
    - econstructor.
      + econstructor; eauto.
      + eapply IHnra_type1; simpl; trivial; match_destr; try elim_fresh e.
      + eapply IHnra_type2; simpl; trivial; match_destr; try elim_fresh e.
    (* type_NRAEitherConcat *)
    - econstructor; [eauto | ].
      econstructor.
      + eapply IHnra_type1; simpl; trivial; match_destr; try elim_fresh e.
      + econstructor; [eauto | ].
        econstructor; eauto.
        econstructor; eauto.
        repeat econstructor; eauto. simpl.
        repeat econstructor; eauto. simpl.
        match_destr; try congruence.
        econstructor. simpl.
        dest_eqdec.
        * symmetry in e; elim_fresh e.
        * match_destr; try congruence.
      + econstructor; [econstructor | ].
        econstructor; eauto.
        * econstructor; simpl.
          eauto.
        * econstructor; simpl. match_destr; try congruence.
        * econstructor; simpl.
          { match_destr.
            - symmetry in e; elim_fresh e.
            - match_destr; try congruence.
          }
    (* type_NRAApp *)
    - repeat (econstructor; eauto 2).
      apply IHnra_type2; simpl; trivial.
      + simpl; match_destr; intuition.
  Qed.

  (** Reverse direction, main theorem *)

  Theorem tnra_sem_correct_back {τin τout} (op:nra) (tenv:tbindings) (vid:var) :
    lookup equiv_dec tenv vid = Some τin ->
    nnrc_core_type τconstants tenv (nra_to_nnrc_core op vid) τout ->
    (op ▷ τin >=> τout ⊣ τconstants).
  Proof.
    Hint Constructors nra_type.
    intros.
    revert τin τout vid tenv H H0.
    nra_cases (induction op) Case; simpl; intros; inversion H0; subst.
    - Case "NRAGetConstant"%string.
      econstructor. eauto.
    - Case "NRAID"%string.
      rewrite H in H3; inversion H3; subst. eauto.
    - Case "NRAConst"%string.
      eauto.
    - Case "NRABinop"%string.
      eauto. 
    - Case "NRAUnop"%string.
      eauto.
    - Case "NRAMap"%string.
      econstructor; eauto 2.
      eapply (IHop1 _ _ (fresh_var "tmap$" [vid])
                    ((fresh_var "tmap$" [vid],
                      τ₁) :: tenv)); simpl; trivial.
      + match_destr; congruence.
    - Case "NRAMapProduct"%string.
      inversion H6; subst.
      inversion H9; subst.
      inversion H11; subst.
      inversion H13; subst.
      inversion H14; subst.
      simpl in H3,H5.
      dest_eqdec; [ | congruence].
      dest_eqdec; [elim_fresh e0 | ].
      dest_eqdec; [ | congruence ].
      inversion H3; inversion H5.
      subst.
      inversion H7; subst.
      clear H3 H13 H14 H5.
      inversion H4; subst.
      destruct τ; simpl in *.
      subst.
      destruct (to_Rec Closed (rec_concat_sort τ₁ τ₂1) e1) as [? rr].
      rewrite rr.
      econstructor; eauto 2.
      clear H0 H4 H11 H6 H9.
      eapply (IHop1 _ _ (fresh_var "tmc$" [vid]) (( fresh_var "tmc$" [vid], Rec Closed τ₁ pf1)
           :: tenv)); eauto.
      + simpl; match_destr.
        congruence.
    - Case "NRAProduct"%string.
      inversion H4; subst.
      inversion H6; subst.
      destruct τ₂; simpl in *.
      subst.
      inversion H9; subst.
      rtype_equalizer.
      subst.
      inversion H11; subst.
      inversion H13; inversion H14; subst.
      simpl in H3,H16.
      dest_eqdec; try congruence.
      dest_eqdec; try elim_fresh e1.
      dest_eqdec; try elim_fresh e2.
      inversion H3; inversion H16; subst.
      inversion H10; subst.
      econstructor; eauto 2.
      clear H13 H14 H0 H6 H9 H11 H10.
      eapply (IHop2 _ _ vid ((fresh_var "tprod$" [vid], Rec Closed τ₁ pf1) :: tenv)); eauto.
      + simpl.
        match_destr.
        elim_fresh e2.
    - Case "NRASelect"%string.
      inversion H4; clear H4; subst.
      inversion H6; clear H6; subst.
      inversion H8; clear H8; subst.
      inversion H11; clear H11; subst.
      inversion H10; clear H10; subst.
      inversion H11; clear H11; subst.
      simpl in H5.
      dest_eqdec; try elim_fresh e.
      inversion H5; clear H5; subst.
      inversion H8; clear H8; subst.
      inversion H7; clear H7; subst.
      rtype_equalizer.
      subst.
      econstructor; eauto 2.
      eapply (IHop1 _ _ (fresh_var "tsel$" (vid::nil)) ((fresh_var "tsel$" (vid::nil), τ) :: tenv)); eauto; simpl;
        match_destr; try elim_fresh e0.
    - Case "NRADefault"%string.
      inversion H7; subst; clear H7.
      inversion H10; subst. inversion H5; subst.
      inversion H8; inversion H12; inversion H13;
      subst; clear H5 H10 H8 H12 H13.
      invcs H18.
      simpl in H3, H11.
      dest_eqdec; try congruence.
      inversion H3; subst; inversion H11; subst; clear H3 H11.
      constructor; eauto 2.
      eapply (IHop2 _ _ vid ((fresh_var "tdef$" [vid], Coll τ) :: tenv)); eauto; simpl; match_destr; elim_fresh e0.
    - Case "NRAEither"%string.
      inversion H8; subst.
      rewrite H in H3; inversion H3; clear H3; subst.
      econstructor.
      + eapply IHop1; try eapply H9; trivial;
          simpl; match_destr; try elim_fresh e.
      + eapply IHop2; try eapply H10; trivial;
        simpl; match_destr; try elim_fresh e.
    - Case "NRAEitherConcat"%string.
      inversion H7; clear H7; subst.
      clear H0.
      inversion H11; clear H11; subst.
      inversion H3; clear H3; subst.
      inversion H12; clear H12; subst.
      inversion H3; clear H3; subst.
      rtype_equalizer. subst.
      inversion H5; clear H5; subst.
      inversion H9; clear H9; subst.
      inversion H7; clear H7; subst.
      inversion H12; clear H12; subst.
      inversion H13; clear H13; subst.
      inversion H8; clear H8; subst.
      inversion H4; clear H4; subst.
      simpl in H2, H3.
      dest_eqdec; try congruence.
      inversion H2; clear H2; subst.
      inversion H3; clear H3; subst.
      inversion H11; clear H11; subst.
      simpl in H2, H5.
      dest_eqdec; try (symmetry in e0; elim_fresh e0).
      dest_eqdec; try congruence.
      inversion H5; clear H5; subst.
      inversion H2; clear H2; subst.
      rtype_equalizer. subst.
      econstructor; try reflexivity; eauto 2.
      eapply IHop1; try eapply H10; trivial;
        simpl; match_destr; try elim_fresh e1.
    - Case "NRAApp"%string.
      inversion H; subst; clear H.
      econstructor; eauto 2.
      eapply (IHop1 _ _ (fresh_var "tapp$" [vid]) ((fresh_var "tapp$" [vid], τ₁) :: tenv)); simpl; trivial;
        try (match_destr; try elim_fresh e).
  Qed.

  (** Theorem 7.4: NRA<->NNRC.
       Final iff Theorem of type preservation for the translation from NRA to NNRC *)

  Theorem tnraenv_sem_correct_iff {τin τout} (op:nra) (tenv:tbindings) (vid:var) :
    lookup equiv_dec tenv vid = Some τin ->
    nnrc_core_type τconstants tenv (nra_to_nnrc_core op vid) τout ->
    (op ▷ τin >=> τout ⊣ τconstants).
  Proof.
    Hint Resolve tnra_sem_correct tnra_sem_correct_back.
    intuition; eauto.
  Qed.

End TNRAtocNNRC.

