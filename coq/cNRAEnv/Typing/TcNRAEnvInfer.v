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

(** Type inference for NRA when given the type of the input *)

Require Import String.
Require Import List.
Require Import Compare_dec.
Require Import Eqdep_dec.
Require Import Bool.
Require Import EquivDec.
Require Import Utils.
Require Import CommonSystem.
Require Import cNRAEnv.
Require Import TcNRAEnv.
Require Import Program.
Require Import TNRAInfer. (* Only for a few auxiliary Lemmas that should probably be moved *)

Section TcNRAEnvInfer.
  (* Type inference for algebraic expressions *)

  Context {m:basic_model}.
  Context (τconstants:list (string*rtype)).

  Fixpoint infer_nraenv_core_type (e:nraenv_core) (τenv τin:rtype) : option rtype :=
    match e with
    | cNRAEnvGetConstant s =>
      tdot τconstants s
    | cNRAEnvID => Some τin
    | cNRAEnvConst d => infer_data_type (normalize_data brand_relation_brands d)
    | cNRAEnvBinop b op1 op2 =>
      let binf (τ₁ τ₂:rtype) := infer_binary_op_type b τ₁ τ₂ in
      olift2 binf (infer_nraenv_core_type op1 τenv τin) (infer_nraenv_core_type op2 τenv τin)
    | cNRAEnvUnop u op1 =>
      let unf (τ₁:rtype) := infer_unary_op_type u τ₁ in
      olift unf (infer_nraenv_core_type op1 τenv τin)
    | cNRAEnvMap op1 op2 =>
      let mapf (τ₁:rtype) :=
          olift (fun x => lift (fun y => Coll y) (infer_nraenv_core_type op1 τenv x)) (tuncoll τ₁)
      in
      olift mapf (infer_nraenv_core_type op2 τenv τin)
    | cNRAEnvMapProduct op1 op2 =>
      let mapconcatf (τ₁:list (string*rtype)) :=
          match RecMaybe Closed τ₁ with
          | None => None
          | Some τr₁ =>
            match olift (tmapConcatOutput τ₁) (infer_nraenv_core_type op1 τenv τr₁) with
            | None => None
            | Some τ₂ => Some (Coll τ₂)
            end
          end
      in
      olift mapconcatf (olift tmapConcatInput (infer_nraenv_core_type op2 τenv τin))
    | cNRAEnvProduct op1 op2 =>
      let mapconcatf (τ₁:list (string*rtype)) :=
          match RecMaybe Closed τ₁ with
          | None => None
          | Some τr₁ =>
            match olift (tmapConcatOutput τ₁) (infer_nraenv_core_type op2 τenv τin) with
            | None => None
            | Some τ₂ => Some (Coll τ₂)
            end
          end
      in
      olift mapconcatf (olift tmapConcatInput (infer_nraenv_core_type op1 τenv τin))
    | cNRAEnvSelect op1 op2 =>
      let selectf (τ₁:rtype) :=
          match tuncoll τ₁ with
          | Some τ₁' =>
            match infer_nraenv_core_type op1 τenv τ₁' with
            | Some τ₂ =>
              match `τ₂ with
              | Bool₀ => Some (Coll τ₁')
              | _ => None
              end
            | None => None
            end
          | None => None
          end
      in
      olift selectf (infer_nraenv_core_type op2 τenv τin)
    | cNRAEnvDefault op1 op2 =>
      match ((infer_nraenv_core_type op1 τenv τin), (infer_nraenv_core_type op2 τenv τin)) with
      | (Some τ₁', Some τ₂') =>
        match (tuncoll τ₁', tuncoll τ₂') with
        | (Some τ₁₀, Some τ₂₀) =>
          if (`τ₁₀ == `τ₂₀) then Some τ₁' else None
        | _ => None
        end
      | (_, _) => None
      end
    | cNRAEnvEither op1 op2 =>
      match tuneither τin with
      | Some (τl, τr) =>
        match ((infer_nraenv_core_type op1 τenv τl), (infer_nraenv_core_type op2 τenv τr)) with
        | (Some τ₁', Some τ₂') =>
          if (rtype_eq_dec τ₁' τ₂') (* Probably should be generalized using join... *)
          then Some τ₁'
          else None
        | (_, _) => None
        end
      | _ => None
      end
    | cNRAEnvEitherConcat op1 op2 =>
      match (infer_nraenv_core_type op1 τenv τin, infer_nraenv_core_type op2 τenv τin) with
      | (Some τeither, Some τrecplus) =>          
        match tuneither τeither with
        | Some (τl, τr) =>
          match (trecConcat τl τrecplus, trecConcat τr τrecplus) with
          | (Some τrecl, Some τrecr) =>
            Some (Either τrecl τrecr)
          | (_, _) => None
          end
        | None => None
        end
      | (_, _) => None
      end
    | cNRAEnvApp op1 op2 =>
      let appf (τ₁:rtype) := infer_nraenv_core_type op1 τenv τ₁ in
      olift appf (infer_nraenv_core_type op2 τenv τin)
    | cNRAEnvEnv =>
      Some τenv
    | cNRAEnvAppEnv op1 op2 =>
      let appf (τ₁:rtype) := infer_nraenv_core_type op1 τ₁ τin in
      olift appf (infer_nraenv_core_type op2 τenv τin)
    | cNRAEnvMapEnv op1 =>
      let mapf (τenv':rtype) :=
          lift Coll (infer_nraenv_core_type op1 τenv' τin)
      in
      olift mapf (tuncoll τenv)
    end.

  Lemma infer_nraenv_core_type_correct (τenv τin τout:rtype) (e:nraenv_core) :
    infer_nraenv_core_type e τenv τin = Some τout ->
    nraenv_core_type τconstants e τenv τin τout.
  Proof.
    intros.
    revert τenv τin τout H.
    nraenv_core_cases (induction e) Case; intros; simpl in H.
    - Case "cNRAEnvGetConstant"%string.
      apply type_cNRAEnvGetConstant; assumption.
    - Case "cNRAEnvID"%string.
      inversion H; clear H.
      apply type_cNRAEnvID.
    - Case "cNRAEnvConst"%string.
      apply type_cNRAEnvConst.
      apply infer_data_type_correct. assumption.
    - Case "cNRAEnvBinop"%string.
      specialize (IHe1 τenv τin); specialize (IHe2 τenv τin).
      destruct (infer_nraenv_core_type e1 τenv τin);
        destruct (infer_nraenv_core_type e2 τenv τin); simpl in *;
      try discriminate.
      specialize (IHe1 r eq_refl); specialize (IHe2 r0 eq_refl).
      apply (@type_cNRAEnvBinop m τconstants τenv τin r r0 τout); try assumption.
      apply infer_binary_op_type_correct; assumption.
    - Case "cNRAEnvUnop"%string.
      specialize (IHe τenv τin).
      destruct (infer_nraenv_core_type e τenv τin); simpl in *;
      try discriminate.
      specialize (IHe r eq_refl).
      apply (@type_cNRAEnvUnop m τconstants τenv τin r τout); try assumption.
      apply infer_unary_op_type_correct; assumption.
    - Case "cNRAEnvMap"%string.
      case_eq (infer_nraenv_core_type e2 τenv τin); intros; simpl in *.
      + specialize (IHe2 τenv τin r H0). rewrite H0 in H. simpl in *.
        unfold lift in H.
        case_eq (tuncoll r); intros. rewrite H1 in *.
        inversion H. subst. clear H H0.
        case_eq (infer_nraenv_core_type e1 τenv r0); intros.
        specialize (IHe1 τenv r0 r1 H).
        rewrite H in H3.
        inversion H3.
        apply (@type_cNRAEnvMap m τconstants τenv τin r0 r1); try assumption.
        apply tuncoll_correct in H1.
        rewrite <- H1; assumption.
        rewrite H in H3; congruence.
        rewrite H1 in H; simpl in H; congruence.
      + rewrite H0 in H. simpl in H; congruence.
    - Case "cNRAEnvMapProduct"%string.
      case_eq (infer_nraenv_core_type e2 τenv τin); intros.
      + specialize (IHe2 τenv τin r H0). rewrite H0 in H; simpl in *.
        unfold tmapConcatInput in H.
        destruct r; try congruence.
        destruct x; simpl in H; try congruence.
        destruct x; simpl in H; try congruence.
        clear H0.
        destruct k; simpl in H; [congruence| ].
        destruct (from_Rec₀ srl e) as [l1' [pf1' [eq11 eq12]]].
        assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ (Rec₀ Closed srl)) e =
                Coll (Rec Closed l1' pf1')) by (rewrite eq12; apply rtype_fequal; reflexivity).
        rewrite H0 in IHe2; clear H0.
        simpl in H; clear eq12 eq11 e.
        assert (RecMaybe Closed l1' = Some (Rec Closed l1' pf1')) by apply RecMaybe_pf_some.
        rewrite H0 in H; clear H0.
        case_eq (infer_nraenv_core_type e1 τenv (Rec Closed l1' pf1')); intros.
        * rewrite H0 in H; simpl in H.
          destruct r; try congruence.
          destruct x; simpl in H; try congruence.
          destruct x; simpl in H; try congruence.
          destruct k; simpl in H; try congruence.
          destruct (from_Rec₀ srl0 e) as [l2' [pf2' [eq21 eq22]]].
          assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ (Rec₀ Closed srl0)) e =
                  Coll (Rec Closed l2' pf2')) by (rewrite eq22; apply rtype_fequal; reflexivity).
          rewrite H1 in *.
          specialize (IHe1 τenv (Rec Closed l1' pf1') (Coll (Rec Closed l2' pf2')) H0).
          assert (is_list_sorted ODT_lt_dec
                                 (domain (rec_concat_sort l1' l2')) = true)
            by (apply (rec_concat_sort_sorted l1' l2'); reflexivity).
          assert (RecMaybe Closed (rec_concat_sort l1' l2') = Some (Rec Closed (rec_concat_sort l1' l2') H2))
            by apply RecMaybe_pf_some.
          simpl in H.
          clear e eq22 H1 eq21 srl0 H0.
          generalize (@type_cNRAEnvMapProduct m τconstants τenv τin l1' l2' (rec_concat_sort l1' l2')
                                   e1 e2 pf1' pf2' H2 IHe1 IHe2 eq_refl); intros.
          assert (τout = (Coll (Rec Closed (rec_concat_sort l1' l2') H2))).
          assert ((@RecMaybe (@basic_model_foreign_type m)
            (@brand_model_relation (@basic_model_foreign_type m)
               (@basic_model_brand_model m)) Closed
            (@rec_concat_sort string ODT_string
               (@sig (@rtype₀ (@basic_model_foreign_type m))
                  (fun τ₀ : @rtype₀ (@basic_model_foreign_type m) =>
                   @eq bool
                     (@wf_rtype₀ (@basic_model_foreign_type m)
                        (@brand_model_relation
                           (@basic_model_foreign_type m)
                           (@basic_model_brand_model m)) τ₀) true)) l1'
               l2')) = 
           (@RecMaybe (@basic_model_foreign_type m)
            (@brand_model_relation (@basic_model_foreign_type m)
               (@basic_model_brand_model m)) Closed
            (@rec_concat_sort string ODT_string
               (@rtype (@basic_model_foreign_type m)
                  (@brand_model_relation (@basic_model_foreign_type m)
                                         (@basic_model_brand_model m))) l1' l2')))
            by reflexivity.
          rewrite <- H1 in H.
          destruct (RecMaybe Closed (rec_concat_sort l1' l2')).
          inversion H.
          rewrite H5.
          inversion H3.
          rewrite <- H5.
          rewrite H6; reflexivity.
          congruence.
          rewrite H1.
          assumption.
        * rewrite H0 in H; simpl in H; congruence.
      + rewrite H0 in H; simpl in H; congruence.
    - Case "cNRAEnvProduct"%string.
      case_eq (infer_nraenv_core_type e1 τenv τin); intros.
      case_eq (infer_nraenv_core_type e2 τenv τin); intros.
      + specialize (IHe1 τenv τin r H0). rewrite H0 in H; simpl in *.
        unfold tmapConcatInput in H.
        destruct r; try congruence.
        destruct x; simpl in H; try congruence.
        destruct x; simpl in H; try congruence.
        destruct k; simpl in H; try congruence.
        clear H0.
        rewrite H1 in H; simpl in H.
        destruct (from_Rec₀ srl e) as [l1' [pf1' [eq11 eq12]]].
        assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ (Rec₀ Closed srl)) e =
                Coll (Rec Closed l1' pf1')) by (rewrite eq12; apply rtype_fequal; reflexivity).
        rewrite H0 in IHe1; clear H0.
        simpl in H; clear eq12 eq11 e.
        assert (RecMaybe Closed l1' = Some (Rec Closed l1' pf1')) by apply RecMaybe_pf_some.
        rewrite H0 in H; clear H0.
        destruct r0; try congruence.
        destruct x; simpl in H; try congruence.
        destruct x; simpl in H; try congruence.
        destruct k; simpl in H; try congruence.
        destruct (from_Rec₀ srl0 e) as [l2' [pf2' [eq21 eq22]]].
        assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ (Rec₀ Closed srl0)) e =
                Coll (Rec Closed l2' pf2')) by (rewrite eq22; apply rtype_fequal; reflexivity).
        rewrite H0 in *.
        specialize (IHe2 τenv τin (Coll (Rec Closed l2' pf2')) H1).
        assert (is_list_sorted ODT_lt_dec
                               (domain (rec_concat_sort l1' l2')) = true)
          by (apply (rec_concat_sort_sorted l1' l2'); reflexivity).
        assert (RecMaybe Closed (rec_concat_sort l1' l2') = Some (Rec Closed (rec_concat_sort l1' l2') H2))
          by apply RecMaybe_pf_some.
        clear e eq22 H1 eq21 srl0 H0.
        generalize (@type_cNRAEnvProduct m τconstants τenv τin l1' l2' (rec_concat_sort l1' l2')
                               e1 e2 pf1' pf2' H2 IHe1 IHe2 eq_refl); intros.
        assert (τout = (Coll (Rec Closed (rec_concat_sort l1' l2') H2))).
        assert (τout = (Coll (Rec Closed (rec_concat_sort l1' l2') H2))).
          assert ((@RecMaybe (@basic_model_foreign_type m)
            (@brand_model_relation (@basic_model_foreign_type m)
               (@basic_model_brand_model m)) Closed
            (@rec_concat_sort string ODT_string
               (@sig (@rtype₀ (@basic_model_foreign_type m))
                  (fun τ₀ : @rtype₀ (@basic_model_foreign_type m) =>
                   @eq bool
                     (@wf_rtype₀ (@basic_model_foreign_type m)
                        (@brand_model_relation
                           (@basic_model_foreign_type m)
                           (@basic_model_brand_model m)) τ₀) true)) l1'
               l2')) = 
           (@RecMaybe (@basic_model_foreign_type m)
            (@brand_model_relation (@basic_model_foreign_type m)
               (@basic_model_brand_model m)) Closed
            (@rec_concat_sort string ODT_string
               (@rtype (@basic_model_foreign_type m)
                       (@brand_model_relation (@basic_model_foreign_type m)
                                              (@basic_model_brand_model m))) l1' l2')))
          by reflexivity.
          rewrite <- H1 in H.
        destruct (RecMaybe Closed (rec_concat_sort l1' l2')).
        inversion H.
        rewrite H5 in *.
        inversion H3.
        rewrite <- H6.
        auto.
        congruence.
        assumption.
        rewrite H1.
        auto.
      + rewrite H1 in H. simpl in H.
        destruct ((olift tmapConcatInput (infer_nraenv_core_type e1 τenv τin))); simpl in H.
        destruct (RecMaybe Closed l); congruence.
        congruence.
      + rewrite H0 in H; simpl in H; congruence.
    - Case "cNRAEnvSelect"%string.
      simpl.
      case_eq (infer_nraenv_core_type e2 τenv τin); intros; simpl in *.
      + specialize (IHe2 τenv τin r H0). rewrite H0 in H. simpl in *.
        unfold lift in H.
        case_eq (tuncoll r); intros. rewrite H1 in *.
        inversion H. subst. clear H H0.
        case_eq (infer_nraenv_core_type e1 τenv r0); intros.
        specialize (IHe1 τenv r0 r1 H).
        rewrite H in H3.
        destruct r1; try congruence; simpl in *.
        destruct x; try congruence; simpl in *.
        inversion H3; clear H3 H2.
        apply (@type_cNRAEnvSelect m τconstants τenv τin r0); try assumption.
        assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) Bool₀ e = Bool).
        apply rtype_fequal; reflexivity.
        rewrite H0 in IHe1. assumption.
        apply tuncoll_correct in H1.
        rewrite <- H1; assumption.
        rewrite H in H3; congruence.
        rewrite H1 in H; congruence.
      + rewrite H0 in H. simpl in H; congruence.
    - Case "cNRAEnvDefault"%string.
      specialize (IHe1 τenv τin); specialize (IHe2 τenv τin).
      destruct (infer_nraenv_core_type e1 τenv τin); destruct (infer_nraenv_core_type e2 τenv τin); simpl in *;
      try discriminate.
      specialize (IHe1 r eq_refl); specialize (IHe2 r0 eq_refl).
      case_eq r; case_eq r0;intros; subst; simpl in *.
      destruct x; destruct x0; try (subst; discriminate); simpl in *.
      destruct (equiv_dec x0 x); try congruence.
      inversion H; clear H.
      assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ x0) e0 = exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ x) e).
      apply rtype_fequal; simpl. subst. rewrite e3; reflexivity.
      rewrite H in *; clear H1 H e3 x0 e0 τout.
      assert (exists τ, Coll τ = exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ x) e).
      exists (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e).
      apply rtype_fequal; simpl; reflexivity.
      elim H; clear H; intros.
      rewrite <- H in *.
      apply type_cNRAEnvDefault; assumption.
    - Case "cNRAEnvEither"%string.
      unfold tuneither in H.
      destruct τin.
      destruct x; simpl in *; try discriminate.
      match_case_in H; intros; rewrite H0 in H; try discriminate.
      match_case_in H; intros; rewrite H1 in H; try discriminate.
      match_destr_in H.
      red in e0.
      invcs H; subst.
      specialize (IHe1 _ _ _ H0).
      specialize (IHe2 _ _ _ H1).
      erewrite Either_canon
      ; eapply type_cNRAEnvEither
      ; eauto.
    - Case "cNRAEnvEitherConcat"%string.
      case_eq (infer_nraenv_core_type e1 τenv τin); case_eq (infer_nraenv_core_type e2 τenv τin); simpl in *; intros;
      rewrite H0 in *; rewrite H1 in *; try discriminate.
      unfold tuneither in H.
      destruct r0; simpl in H.
      destruct x; simpl in H; try discriminate.
      destruct x1; simpl in H; try discriminate.
      destruct r; simpl in H; try discriminate.
      destruct x; simpl in H; try discriminate.
      match goal with
      | [H:context [from_Rec₀ _ ?x] |- _ ] => revert H; generalize x;
                                                let pff := fresh "pf" in
                                                intros pff H
      end.
      destruct k; simpl in H; try discriminate
      ; destruct k0; simpl in H; try (destruct (from_Rec₀ srl pf); destruct (from_Rec₀ srl0 e0); simpl in H; try discriminate).
      rewrite @RecMaybe_rec_concat_sort in H.
      destruct x2; simpl in H; try discriminate.
      match goal with
      | [H:context [from_Rec₀ _ ?x] |- _ ] => revert H; generalize x;
                                                let pff := fresh "pf" in
                                                intros pff H
      end.
      destruct k; simpl in H; try discriminate
      ; [ destruct (from_Rec₀ srl1 pf0); try discriminate | ].
      case_eq (from_Rec₀ (k:=Closed) srl1 pf0); intros.
      rewrite H2 in H.
      rewrite @RecMaybe_rec_concat_sort in H.
      invcs H.
      specialize (IHe1 _ _ _ H1).
      specialize (IHe2 _ _ _ H0).
      destruct e3 as [? [??]].
      destruct e4 as [? [??]].
      destruct e5 as [? [??]].
      subst.
      destruct (Either_canon_ex _ _ e) as [pfl [pfr eqq]].
      rewrite eqq in IHe1.
      clear eqq.
      destruct (to_Rec _ _ pfl) as [? eqq1].
      destruct (to_Rec _ _ pfr) as [? eqq2].
      rewrite eqq1, eqq2 in IHe1.
      destruct (to_Rec _ _ e0) as [? eqq3].
      rewrite eqq3 in IHe2.
      eapply type_cNRAEnvEitherConcat; eauto.
    - Case "cNRAEnvApp"%string.
      specialize (IHe2 τenv τin).
      destruct (infer_nraenv_core_type e2 τenv τin).
      specialize (IHe2 r eq_refl).
      econstructor; eauto.
      simpl in *; congruence.
    - Case "cNRAEnvEnv"%string.
      inversion H; apply type_cNRAEnvEnv.
    - Case "cNRAEnvAppEnv"%string.
      specialize (IHe2 τenv τin).
      destruct (infer_nraenv_core_type e2 τenv τin).
      simpl in H.
      specialize (IHe2 r eq_refl).
      specialize (IHe1 r τin τout).
      econstructor; eauto.
      econstructor; eauto.
      simpl in *; congruence.
    - Case "cNRAEnvMapEnv"%string.
      case_eq (tuncoll τenv); intros.
      + apply tuncoll_correct in H0.
        subst.
        simpl in H.
        assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) 
                      (` r) (proj2_sig r) = r) by (apply rtype_fequal; reflexivity).
        rewrite H0 in H; clear H0.
        case_eq (infer_nraenv_core_type e r τin); intros; simpl in *.
        * unfold lift in H.
          rewrite H0 in H; simpl in H.
          inversion H. subst; clear H.
          specialize (IHe r τin r0 H0).
          apply (@type_cNRAEnvMapEnv m τconstants r τin r0 e IHe).
        * rewrite H0 in H; simpl in H; congruence.
      + rewrite H0 in H; simpl in H; congruence.
  Qed.

  (* Still should try and prove most specific and completeness theorems ... *)
  
End TcNRAEnvInfer.

