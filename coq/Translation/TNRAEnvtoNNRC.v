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

Section TNRAEnvtoNNRC.

  Require Import String.
  Require Import List.
  Require Import EquivDec.
  Require Import Compare_dec.
  Require Import Program.
  
  Require Import Utils BasicSystem.
  Require Import NRAEnvSystem.
  Require Import NNRCSystem.

  Require Import NRAEnvtoNNRC.

  (** Type preservation for the translation from NRA to NNRC *)

  Ltac elim_fresh e
    := solve[(congruence
            || apply fresh_var_fresh1 in e
            || apply fresh_var_fresh2 in e
            || apply fresh_var_fresh3 in e
            || apply fresh_var_fresh4 in e); intuition].
  
  Context {m:basic_model}.
  Theorem tnraenv_sem_correct {τcenv} {τin τenv τout} (op:algenv) (tenv:tbindings) (vid venv:var) :
    prefix CONST_PREFIX vid = false ->
    prefix CONST_PREFIX venv = false ->
    (forall x,
        assoc_lookupr equiv_dec (mkConstants τcenv) x
        = lookup equiv_dec (filterConstants tenv) x) ->
    lookup equiv_dec tenv vid = Some τin ->
    lookup equiv_dec tenv venv = Some τenv ->
    (op ▷ τin >=> τout ⊣ τcenv;τenv) ->
    nnrc_type tenv (algenv_to_nnrc op vid venv) τout.
  Proof.
    Opaque fresh_var.
    Opaque append.
    intros pre1 pre2 fpre; intros.
    revert vid venv tenv pre1 pre2 fpre H H0.
    dependent induction H1; simpl; intros.
    (* ATID *)
    - apply TNNRCVar; trivial.
    (* ATConst *)
    - apply TNNRCConst; trivial.
    (* ATBinop *)
    - econstructor; eauto.
    (* ATUnop *)
    - econstructor; eauto. 
    (* ATMap *)
    - econstructor; [eauto | ].
      apply (IHalgenv_type1 
                    (fresh_var "tmap$" [vid; venv]) venv
                    ((fresh_var "tmap$" [vid; venv],τ₁)::tenv)); simpl; trivial.
      + dest_eqdec; congruence.
      + dest_eqdec; trivial.
        elim_fresh e.
    (* ATMapConcat *)
    - specialize (IHalgenv_type2 vid venv tenv).
      apply (@TNNRCUnop m (RType.Coll (RType.Coll (RType.Rec Closed τ₃ pf3)))).
      apply ATFlatten.
      apply (@TNNRCFor m (RType.Rec Closed τ₁ pf1)); [eauto | ].
      apply (@TNNRCFor m (RType.Rec Closed τ₂ pf2)).
      + apply IHalgenv_type1; simpl; trivial;
        match_destr; try elim_fresh e.
      + econstructor; econstructor; eauto 2; simpl; match_destr; try elim_fresh e.
        match_destr; elim_fresh e.
    (* ATProduct *)
    - apply (@TNNRCUnop m (RType.Coll (RType.Coll (RType.Rec Closed τ₃ pf3)))).
      apply ATFlatten.
      apply (@TNNRCFor m (RType.Rec Closed τ₁ pf1)); try assumption.
      apply (IHalgenv_type1 vid venv tenv); assumption.
      clear IHalgenv_type1 op1 H1_.
      apply (@TNNRCFor m (RType.Rec Closed τ₂ pf2)).
      + apply IHalgenv_type2; simpl; trivial; match_destr; try elim_fresh e.
      + econstructor; econstructor; eauto 2; simpl.
        * match_destr.
          elim_fresh e.
          match_destr; congruence.
        * match_destr; try congruence.
    (* ATSelect *)
    - apply (@TNNRCUnop m (RType.Coll (RType.Coll τ))); [apply ATFlatten|idtac].
      apply (@TNNRCFor m τ); [apply (IHalgenv_type2 vid venv tenv )|idtac]; trivial.
      apply TNNRCIf.
      + apply IHalgenv_type1; simpl; trivial; match_destr; elim_fresh e.
      + econstructor; eauto.
        econstructor. simpl.
        match_destr; intuition.
      + econstructor. simpl. repeat econstructor.
    (* ATDefault *)
    - econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      + simpl. match_destr; congruence.
      + econstructor. econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
        eapply Forall_nil.
      + apply IHalgenv_type2; simpl; trivial; match_destr; elim_fresh e.
      + econstructor; eauto.
        simpl; match_destr; elim_fresh e.
    (* ATEither *)
    - econstructor.
      + econstructor; eauto.
      + eapply IHalgenv_type1; simpl; trivial; match_destr; try elim_fresh e.
      + eapply IHalgenv_type2; simpl; trivial; match_destr; try elim_fresh e.
    (* ATEitherConcat *)
    -  econstructor; [eauto | ].
       econstructor.
       + eapply IHalgenv_type1; simpl; trivial; match_destr; try elim_fresh e.
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
         econstructor; eauto.
         * econstructor; simpl.
           match_destr; try congruence.
         * econstructor; simpl.
           { match_destr.
             - symmetry in e; elim_fresh e.
             - match_destr; try congruence.
           }
    (* ATApp *)
    - repeat (econstructor; eauto 2).
      apply IHalgenv_type2; simpl; trivial.
      + simpl; match_destr; intuition.
      + simpl; match_destr.
        elim_fresh e.
    (* ATGetConstant *)
    - econstructor; eauto 2.
      rewrite <- (filterConstants_lookup_pre tenv s).
      rewrite <- fpre.
      unfold equiv_dec.
      rewrite mkConstants_assoc_lookupr.
      trivial.
    (* ATEnv *)
    - apply TNNRCVar; assumption.
    (* ATAppEnv *)
    - repeat (econstructor; eauto 2).
      apply IHalgenv_type2; simpl; trivial; match_destr; elim_fresh e.
    (* ATMapEnv *)
    - repeat econstructor; eauto 2.
      apply IHalgenv_type; simpl; trivial; match_destr; elim_fresh e.
  Qed.

  (** Reverse direction, main theorem *)

  Theorem tnraenv_sem_correct_back {τcenv} {τin τenv τout} (op:algenv) (tenv:tbindings) (vid venv:var) :
    prefix CONST_PREFIX vid = false ->
    prefix CONST_PREFIX venv = false ->
    (forall x,
        assoc_lookupr equiv_dec (mkConstants τcenv) x
        = lookup equiv_dec (filterConstants tenv) x) ->
    lookup equiv_dec tenv vid = Some τin ->
    lookup equiv_dec tenv venv = Some τenv ->
    nnrc_type tenv (algenv_to_nnrc op vid venv) τout ->
    (op ▷ τin >=> τout ⊣ τcenv;τenv).
  Proof.
    Hint Constructors algenv_type.
    intros pre1 pre2 fpre; intros.
    revert τin τenv τout vid venv tenv pre1 pre2 fpre H H0 H1.
    algenv_cases (induction op) Case; simpl; intros; inversion H1; subst.
    - Case "ANID"%string.
      rewrite H in H4; inversion H4; subst. eauto.
    - Case "ANConst"%string.
      eauto.
    - Case "ANBinop"%string.
      eauto. 
    - Case "ANUnop"%string.
      eauto.
    - Case "ANMap"%string.
      econstructor; eauto 2.
      eapply (IHop1 _ _ _ (fresh_var "tmap$" [vid; venv])
                    venv
                    ((fresh_var "tmap$" [vid; venv],
                      τ₁) :: tenv)); simpl; trivial.
      + match_destr; congruence.
      + match_destr. elim_fresh e.
    - Case "ANMapConcat"%string.
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
    - Case "ANProduct"%string.
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
    - Case "ANSelect"%string.
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
    - Case "ANDefault"%string.
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
    - Case "ANEither"%string.
      inversion H9; subst.
      rewrite H in H4; inversion H4; clear H4; subst.
      econstructor.
      + eapply IHop1; try eapply H10; trivial;
          simpl; match_destr; try elim_fresh e.
      + eapply IHop2; try eapply H11; trivial;
        simpl; match_destr; try elim_fresh e.
    - Case "ANEitherConcat"%string.
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
    - Case "ANApp"%string.
      inversion H; subst; clear H.
      econstructor; eauto 2.
      eapply (IHop1 _ _ _ (fresh_var "tapp$" [vid; venv]) venv ((fresh_var "tapp$" [vid; venv], τ₁) :: tenv)); simpl; trivial;
        try (match_destr; try elim_fresh e).
    - Case "ANGetConstant"%string.
      econstructor.
      rewrite <- filterConstants_lookup_pre in H4.
      rewrite <- fpre in H4.
      rewrite mkConstants_assoc_lookupr in H4.
      apply H4.
    - Case "ANEnv"%string.
      rewrite H0 in H4; inversion H4; subst; eauto.
    - Case "ANAppEnv"%string.
      inversion H; subst; clear H.
      econstructor; eauto 2.
      eapply (IHop1 _ _ _ vid (fresh_var "tappe$" [vid; venv]) ((fresh_var "tappe$" [vid; venv], τ₁) :: tenv)); trivial; simpl;
        try (match_destr; elim_fresh e).
    - Case "ANMapEnv"%string.
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

  Theorem tnraenv_sem_correct_iff {τcenv} {τin τenv τout} (op:algenv) (tenv:tbindings) (vid venv:var) :
    prefix CONST_PREFIX vid = false ->
    prefix CONST_PREFIX venv = false ->
    (forall x,
        assoc_lookupr equiv_dec (mkConstants τcenv) x
        = lookup equiv_dec (filterConstants tenv) x) ->
    lookup equiv_dec tenv vid = Some τin ->
    lookup equiv_dec tenv venv = Some τenv ->
    nnrc_type tenv (algenv_to_nnrc op vid venv) τout ->
    (op ▷ τin >=> τout ⊣ τcenv;τenv).
  Proof.
    Hint Resolve tnraenv_sem_correct tnraenv_sem_correct_back.
    intuition; eauto.
  Qed.

End TNRAEnvtoNNRC.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
