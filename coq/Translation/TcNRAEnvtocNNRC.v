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
Require Import cNRAEnvSystem.
Require Import cNNRCSystem.
Require Import cNRAEnvtocNNRC.

Section TcNRAEnvtocNNRC.
  (** Type preservation for the translation from NRA to NNRC *)

  Ltac elim_fresh e
    := solve[(congruence
            || apply fresh_var_fresh1 in e
            || apply fresh_var_fresh2 in e
            || apply fresh_var_fresh3 in e
            || apply fresh_var_fresh4 in e); intuition].
  
  Context {m:basic_model}.
  Context (τconstants:tbindings).
  
  Theorem tnraenv_sem_correct {τin τenv τout} (op:nraenv_core) (tenv:tbindings) (vid venv:var) :
    lookup equiv_dec tenv vid = Some τin ->
    lookup equiv_dec tenv venv = Some τenv ->
    (op ▷ τin >=> τout ⊣ τconstants;τenv) ->
    nnrc_core_type τconstants tenv (nraenv_core_to_nnrc_core op vid venv) τout.
  Proof.
    Opaque fresh_var.
    Opaque append.
    intros.
    revert vid venv tenv H H0.
    dependent induction H1; simpl; intros.
    (* cNRAEnvGetConstant *)
    - econstructor; eauto 2.
    (* cNRAEnvID *)
    - apply type_cNNRCVar; trivial.
    (* cNRAEnvConst *)
    - apply type_cNNRCConst; trivial.
    (* cNRAEnvBinop *)
    - econstructor; eauto.
    (* cNRAEnvUnop *)
    - econstructor; eauto. 
    (* cNRAEnvMap *)
    - econstructor; [eauto | ].
      apply (IHnraenv_core_type1 
                    (fresh_var "tmap$" [vid; venv]) venv
                    ((fresh_var "tmap$" [vid; venv],τ₁)::tenv)); simpl; trivial.
      + dest_eqdec; congruence.
      + dest_eqdec; trivial.
        elim_fresh e.
    (* cNRAEnvMapProduct *)
    - specialize (IHnraenv_core_type2 vid venv tenv).
      apply (@type_cNNRCUnop m _ (RType.Coll (RType.Coll (RType.Rec Closed τ₃ pf3)))).
      apply type_OpFlatten.
      apply (@type_cNNRCFor m _ (RType.Rec Closed τ₁ pf1)); [eauto | ].
      apply (@type_cNNRCFor m _ (RType.Rec Closed τ₂ pf2)).
      + apply IHnraenv_core_type1; simpl; trivial;
        match_destr; try elim_fresh e.
      + econstructor; econstructor; eauto 2; simpl; match_destr; try elim_fresh e.
        match_destr; elim_fresh e.
    (* cNRAEnvProduct *)
    - apply (@type_cNNRCUnop m _ (RType.Coll (RType.Coll (RType.Rec Closed τ₃ pf3)))).
      apply type_OpFlatten.
      apply (@type_cNNRCFor m _ (RType.Rec Closed τ₁ pf1)); try assumption.
      apply (IHnraenv_core_type1 vid venv tenv); assumption.
      clear IHnraenv_core_type1 op1 H1_.
      apply (@type_cNNRCFor m _ (RType.Rec Closed τ₂ pf2)).
      + apply IHnraenv_core_type2; simpl; trivial; match_destr; try elim_fresh e.
      + econstructor; econstructor; eauto 2; simpl.
        * match_destr.
          elim_fresh e.
          match_destr; congruence.
        * match_destr; try congruence.
    (* cNRAEnvSelect *)
    - apply (@type_cNNRCUnop m _ (RType.Coll (RType.Coll τ))); [apply type_OpFlatten|idtac].
      apply (@type_cNNRCFor m _ τ); [apply (IHnraenv_core_type2 vid venv tenv )|idtac]; trivial.
      apply type_cNNRCIf.
      + apply IHnraenv_core_type1; simpl; trivial; match_destr; elim_fresh e.
      + econstructor; eauto.
        econstructor. simpl.
        match_destr; intuition.
      + econstructor. simpl. repeat econstructor.
    (* cNRAEnvDefault *)
    - econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      + simpl. match_destr; congruence.
      + econstructor. econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
        eapply Forall_nil.
      + apply IHnraenv_core_type2; simpl; trivial; match_destr; elim_fresh e.
      + econstructor; eauto.
        simpl; match_destr; elim_fresh e.
    (* cNRAEnvEither *)
    - econstructor.
      + econstructor; eauto.
      + eapply IHnraenv_core_type1; simpl; trivial; match_destr; try elim_fresh e.
      + eapply IHnraenv_core_type2; simpl; trivial; match_destr; try elim_fresh e.
    (* cNRAEnvEitherConcat *)
    - econstructor; [eauto | ].
      econstructor.
      + eapply IHnraenv_core_type1; simpl; trivial; match_destr; try elim_fresh e.
      + econstructor; [eauto | ].
        econstructor; eauto.
        econstructor; eauto.
        simpl.
        match_destr; try congruence.
        econstructor. simpl.
        dest_eqdec.
        * symmetry in e; elim_fresh e.
        * match_destr; try congruence.
      + econstructor; [econstructor | ].
        econstructor. econstructor. eauto.
        * econstructor; simpl.
          match_destr; try congruence.
        * econstructor; simpl.
          { match_destr.
            - symmetry in e; elim_fresh e.
            - match_destr; try congruence.
          }
    (* cNRAEnvApp *)
    - repeat (econstructor; eauto 2).
      apply IHnraenv_core_type2; simpl; trivial.
      + simpl; match_destr; intuition.
      + simpl; match_destr.
        elim_fresh e.
    (* cNRAEnvEnv *)
    - apply type_cNNRCVar; assumption.
    (* cNRAEnvAppEnv *)
    - repeat (econstructor; eauto 2).
      apply IHnraenv_core_type2; simpl; trivial; match_destr; elim_fresh e.
    (* cNRAEnvMapEnv *)
    - repeat econstructor; eauto 2.
      apply IHnraenv_core_type; simpl; trivial; match_destr; elim_fresh e.
  Qed.

  (** Reverse direction, main theorem *)

  Theorem tnraenv_sem_correct_back {τin τenv τout} (op:nraenv_core) (tenv:tbindings) (vid venv:var) :
    lookup equiv_dec tenv vid = Some τin ->
    lookup equiv_dec tenv venv = Some τenv ->
    nnrc_core_type τconstants tenv (nraenv_core_to_nnrc_core op vid venv) τout ->
    (op ▷ τin >=> τout ⊣ τconstants;τenv).
  Proof.
    Hint Constructors nraenv_core_type.
    intros.
    revert τin τenv τout vid venv tenv H H0 H1.
    nraenv_core_cases (induction op) Case; simpl; intros; inversion H1; subst.
    - Case "cNRAEnvGetConstant"%string.
      econstructor.
      eauto.
    - Case "cNRAEnvID"%string.
      rewrite H in H4; inversion H4; subst. eauto.
    - Case "cNRAEnvConst"%string.
      eauto.
    - Case "cNRAEnvBinop"%string.
      eauto. 
    - Case "cNRAEnvUnop"%string.
      eauto.
    - Case "cNRAEnvMap"%string.
      econstructor; eauto 2.
      eapply (IHop1 _ _ _ (fresh_var "tmap$" [vid; venv])
                    venv
                    ((fresh_var "tmap$" [vid; venv],
                      τ₁) :: tenv)); simpl; trivial.
      + match_destr; congruence.
      + match_destr. elim_fresh e.
    - Case "cNRAEnvMapProduct"%string.
      inversion H7; subst.
      inversion H10; subst.
      inversion H12; subst.
      inversion H14; subst.
      inversion H15; subst.
      simpl in H4,H6.
      dest_eqdec; [ | congruence].
      dest_eqdec; [elim_fresh e0 | ].
      dest_eqdec; [ | congruence ].
      inversion H4; inversion H6.
      subst.
      inversion H8; subst.
      clear H4 H14 H15 H6.
      inversion H5; subst.
      destruct τ; simpl in *.
      subst.
      destruct (to_Rec Closed (rec_concat_sort τ₁ τ₂1) e1) as [? rr].
      rewrite rr.
      econstructor; eauto 2.
      clear H1 H5 H12 H7 H10.
      eapply (IHop1 _ _ _ (fresh_var "tmc$" [vid; venv]) venv (( fresh_var "tmc$" [vid; venv], Rec Closed τ₁ pf1)
           :: tenv)); eauto.
      + simpl; match_destr.
        congruence.
      + simpl; match_destr.
        elim_fresh e2.
    - Case "cNRAEnvProduct"%string.
      inversion H5; subst.
      inversion H7; subst.
      destruct τ₂; simpl in *.
      subst.
      inversion H10; subst.
      rtype_equalizer.
      subst.
      inversion H12; subst.
      inversion H14; inversion H15; subst.
      simpl in H4,H17.
      dest_eqdec; try congruence.
      dest_eqdec; try elim_fresh e1.
      dest_eqdec; try elim_fresh e2.
      inversion H4; inversion H17; subst.
      inversion H11; subst.
      econstructor; eauto 2.
      clear H14 H15 H1 H7 H10 H12 H11.
      eapply (IHop2 _ _ _ vid venv ((fresh_var "tprod$" [vid; venv], Rec Closed τ₁ pf1) :: tenv)); eauto.
      + simpl.
        match_destr.
        elim_fresh e2.
      + simpl; match_destr; try elim_fresh e2.
    - Case "cNRAEnvSelect"%string.
      inversion H5; clear H5; subst.
      inversion H7; clear H7; subst.
      inversion H9; clear H9; subst.
      inversion H12; clear H12; subst.
      inversion H11; clear H11; subst.
      inversion H12; clear H12; subst.
      simpl in H6.
      dest_eqdec; try elim_fresh e.
      inversion H6; clear H6; subst.
      inversion H9; clear H9; subst.
      inversion H8; clear H8; subst.
      rtype_equalizer.
      subst.
      econstructor; eauto 2.
      eapply (IHop1 _ _ _ (fresh_var "tsel$" (vid::venv::nil)) venv ((fresh_var "tsel$" (vid::venv::nil), τ) :: tenv)); eauto; simpl;
        match_destr; try elim_fresh e0.
    - Case "cNRAEnvDefault"%string.
      inversion H8; subst; clear H8.
      inversion H11; subst. inversion H6; subst.
      inversion H9; inversion H13; inversion H14;
      subst; clear H6 H11 H9 H13 H14.
      invcs H19.
      simpl in H4, H12.
      dest_eqdec; try congruence.
      inversion H4; subst; inversion H12; subst; clear H4 H12.
      constructor; eauto 2.
      eapply (IHop2 _ _ _ vid venv ((fresh_var "tdef$" [vid; venv], Coll τ) :: tenv)); eauto; simpl; match_destr; elim_fresh e0.
    - Case "cNRAEnvEither"%string.
      inversion H9; subst.
      rewrite H in H4; inversion H4; clear H4; subst.
      econstructor.
      + eapply IHop1; try eapply H10; trivial;
          simpl; match_destr; try elim_fresh e.
      + eapply IHop2; try eapply H11; trivial;
        simpl; match_destr; try elim_fresh e.
    - Case "cNRAEnvEitherConcat"%string.
      inversion H8; clear H8; subst.
      clear H1.
      inversion H12; clear H12; subst.
      inversion H4; clear H4; subst.
      inversion H13; clear H13; subst.
      inversion H4; clear H4; subst.
      rtype_equalizer. subst.
      inversion H6; clear H6; subst.
      inversion H10; clear H10; subst.
      inversion H8; clear H8; subst.
      inversion H13; clear H13; subst.
      inversion H14; clear H14; subst.
      inversion H9; clear H9; subst.
      inversion H5; clear H5; subst.
      simpl in H3, H4.
      dest_eqdec; try congruence.
      inversion H3; clear H3; subst.
      inversion H4; clear H4; subst.
      inversion H12; clear H12; subst.
      simpl in H3, H6.
      dest_eqdec; try (symmetry in e0; elim_fresh e0).
      dest_eqdec; try congruence.
      inversion H6; clear H6; subst.
      inversion H3; clear H3; subst.
      rtype_equalizer. subst.
      econstructor; try reflexivity; eauto 2.
      eapply IHop1; try eapply H11; trivial;
        simpl; match_destr; try elim_fresh e1.
    - Case "cNRAEnvApp"%string.
      inversion H; subst; clear H.
      econstructor; eauto 2.
      eapply (IHop1 _ _ _ (fresh_var "tapp$" [vid; venv]) venv ((fresh_var "tapp$" [vid; venv], τ₁) :: tenv)); simpl; trivial;
        try (match_destr; try elim_fresh e).
    - Case "cNRAEnvEnv"%string.
      rewrite H0 in H4; inversion H4; subst; eauto.
    - Case "cNRAEnvAppEnv"%string.
      inversion H; subst; clear H.
      econstructor; eauto 2.
      eapply (IHop1 _ _ _ vid (fresh_var "tappe$" [vid; venv]) ((fresh_var "tappe$" [vid; venv], τ₁) :: tenv)); trivial; simpl;
        try (match_destr; elim_fresh e).
    - Case "cNRAEnvMapEnv"%string.
      inversion H7; clear H7; subst.
      rewrite H0 in H4.
      inversion H4; clear H4; subst.
      econstructor; eauto 2.
      apply (IHop _ _ _ vid (fresh_var "tmape$" [vid; venv])
                  ((fresh_var "tmape$" [vid; venv], τ₁) :: tenv));
        trivial; simpl;
        try (match_destr; elim_fresh e).
  Qed.

  (** Theorem 7.4: NRA<->NNRC.
       Final iff Theorem of type preservation for the translation from NRA to NNRC *)

  Theorem tnraenv_sem_correct_iff {τin τenv τout} (op:nraenv_core) (tenv:tbindings) (vid venv:var) :
    lookup equiv_dec tenv vid = Some τin ->
    lookup equiv_dec tenv venv = Some τenv ->
    nnrc_core_type τconstants tenv (nraenv_core_to_nnrc_core op vid venv) τout ->
    (op ▷ τin >=> τout ⊣ τconstants;τenv).
  Proof.
    Hint Resolve tnraenv_sem_correct tnraenv_sem_correct_back.
    intuition; eauto.
  Qed.

End TcNRAEnvtocNNRC.

