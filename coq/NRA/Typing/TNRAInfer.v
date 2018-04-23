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
Require Import Eqdep_dec.
Require Import Bool.
Require Import EquivDec.
Require Import Utils.
Require Import CommonSystem.
Require Import NRA.
Require Import TNRA.
Require Import Program.

Section TNRAInfer.
  (** Type inference for NRA when given the type of the input *)

  (* Auxiliary lemmas/definitions *)

  Section aux.
    Context {fdata:foreign_data}.
    Context {ftype:foreign_type}.
    Context {fdtyping:foreign_data_typing}.
    Context {m:brand_model}.

    Definition tmapConcatInput (τ₁: rtype) : option (list (string*rtype)).
    Proof.
      destruct τ₁; destruct x.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
      - destruct x.
        + exact None.
        + exact None.
        + exact None.
        + exact None.
        + exact None.
        + exact None.
        + exact None.
        + exact None.
        + destruct k.
          * exact None. (* As with record concat, has to be closed records *)
          * generalize (@from_Rec₀ _ _ Closed srl e); intros.
            destruct H.
            exact (Some x).
        + exact None.
        + exact None.
        + exact None.
        + exact None.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
    Defined.

    Definition tmapConcatOutput (τ₁ : list (string*rtype)) (τ₂: rtype) : option rtype.
    Proof.
      destruct τ₂; destruct x.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
      - destruct x.
        + exact None.
        + exact None.
        + exact None.
        + exact None.
        + exact None.
        + exact None.
        + exact None.
        + exact None.
        + destruct k.
          * exact None. (* As with record concat, has to be closed records *)
          * generalize (@from_Rec₀ _ _ Closed srl e); intros.
            destruct H.
            generalize (rec_concat_sort τ₁ x); intros.
            exact (RecMaybe Closed H).
        + exact None.
        + exact None.
        + exact None.
        + exact None.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
      - exact None.
    Defined.

  End aux.
  
  (* Type inference for algebraic expressions *)

  Context {m:basic_model}.
  Context (τconstants:list (string*rtype)).

  Fixpoint infer_nra_type (e:nra) (τin:rtype) : option rtype :=
    match e with
      | NRAGetConstant s =>
        tdot τconstants s
      | NRAID => Some τin
      | NRAConst d => infer_data_type (normalize_data brand_relation_brands d)
      | NRABinop b op1 op2 =>
        let binf (τ₁ τ₂:rtype) := infer_binary_op_type b τ₁ τ₂ in
        olift2 binf (infer_nra_type op1 τin) (infer_nra_type op2 τin)
      | NRAUnop u op1 =>
        let unf (τ₁:rtype) := infer_unary_op_type u τ₁ in
        olift unf (infer_nra_type op1 τin)
      | NRAMap op1 op2 =>
        let mapf (τ₁:rtype) :=
            olift (fun x => lift (fun y => Coll y) (infer_nra_type op1 x)) (tuncoll τ₁)
        in
        olift mapf (infer_nra_type op2 τin)
      | NRAMapProduct op1 op2 =>
        let mapconcatf (τ₁:list (string*rtype)) :=
            match RecMaybe Closed τ₁ with
              | None => None
              | Some τr₁ =>
                match olift (tmapConcatOutput τ₁) (infer_nra_type op1 τr₁) with
                  | None => None
                  | Some τ₂ => Some (Coll τ₂)
                end
            end
        in
        olift mapconcatf (olift tmapConcatInput (infer_nra_type op2 τin))
      | NRAProduct op1 op2 =>
        let mapconcatf (τ₁:list (string*rtype)) :=
            match RecMaybe Closed τ₁ with
              | None => None
              | Some τr₁ =>
                match olift (tmapConcatOutput τ₁) (infer_nra_type op2 τin) with
                  | None => None
                  | Some τ₂ => Some (Coll τ₂)
                end
            end
        in
        olift mapconcatf (olift tmapConcatInput (infer_nra_type op1 τin))
      | NRASelect op1 op2 =>
        let selectf (τ₁:rtype) :=
            match tuncoll τ₁ with
              | Some τ₁' =>
                match infer_nra_type op1 τ₁' with
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
        olift selectf (infer_nra_type op2 τin)
      | NRADefault op1 op2 =>
        match ((infer_nra_type op1 τin), (infer_nra_type op2 τin)) with
            | (Some τ₁', Some τ₂') =>
              match (tuncoll τ₁', tuncoll τ₂') with
                | (Some τ₁₀, Some τ₂₀) =>
                  if (`τ₁₀ == `τ₂₀) then Some τ₁' else None
                | _ => None
              end
            | (_, _) => None
        end
      | NRAEither op1 op2 =>
        match tuneither τin with
        | Some (τl, τr) =>
          match ((infer_nra_type op1 τl), (infer_nra_type op2 τr)) with
          | (Some τ₁', Some τ₂') =>
            if (rtype_eq_dec τ₁' τ₂') (* Probably should be generalized using join... *)
            then Some τ₁'
            else None
          | (_, _) => None
          end
        | _ => None
        end
      | NRAEitherConcat op1 op2 =>
        match (infer_nra_type op1 τin, infer_nra_type op2 τin) with
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
      | NRAApp op1 op2 =>
        let appf (τ₁:rtype) := infer_nra_type op1 τ₁ in
        olift appf (infer_nra_type op2 τin)
    end.

  Lemma infer_nra_type_correct (τin τout:rtype) (e:nra) :
    infer_nra_type e τin = Some τout ->
    nra_type τconstants e τin τout.
  Proof.
    intros.
    revert τin τout H.
    nra_cases (induction e) Case; intros; simpl in H.
    - Case "NRAGetConstant"%string.
      apply type_NRAGetConstant; assumption.
    - Case "NRAID"%string.
      inversion H; clear H.
      apply type_NRAID.
    - Case "NRAConst"%string.
      apply type_NRAConst.
      apply infer_data_type_correct. assumption.
    - Case "NRABinop"%string.
      specialize (IHe1 τin); specialize (IHe2 τin).
      destruct (infer_nra_type e1 τin); destruct (infer_nra_type e2 τin); simpl in *;
      try discriminate.
      specialize (IHe1 r eq_refl); specialize (IHe2 r0 eq_refl).
      apply (@type_NRABinop m τconstants τin r r0 τout); try assumption.
      apply infer_binary_op_type_correct; assumption.
    - Case "NRAUnop"%string.
      specialize (IHe τin).
      destruct (infer_nra_type e τin); simpl in *;
      try discriminate.
      specialize (IHe r eq_refl).
      apply (@type_NRAUnop m τconstants τin r τout); try assumption.
      apply infer_unary_op_type_correct; assumption.
    - Case "NRAMap"%string.
      case_eq (infer_nra_type e2 τin); intros; simpl in *.
      + specialize (IHe2 τin r H0). rewrite H0 in H. simpl in *.
        unfold lift in H.
        case_eq (tuncoll r); intros. rewrite H1 in *.
        inversion H. subst. clear H H0.
        case_eq (infer_nra_type e1 r0); intros.
        specialize (IHe1 r0 r1 H).
        rewrite H in H3.
        inversion H3.
        apply (@type_NRAMap m τconstants τin r0 r1); try assumption.
        apply tuncoll_correct in H1.
        rewrite <- H1; assumption.
        rewrite H in H3; congruence.
        rewrite H1 in H; simpl in H; congruence.
      + rewrite H0 in H. simpl in H; congruence.
    - Case "NRAMapProduct"%string.
      case_eq (infer_nra_type e2 τin); intros.
      + specialize (IHe2 τin r H0). rewrite H0 in H; simpl in *.
        unfold tmapConcatInput in H.
        destruct r; try congruence.
        destruct x; simpl in H; try congruence.
        destruct x; simpl in H; try congruence.
        clear H0.
        destruct k; simpl in H; [congruence| ].
        destruct (from_Rec₀ srl e) as [l1' [pf1' [eq11 eq12]]].
        simpl in H.
        assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ (Rec₀ Closed srl)) e =
                Coll (Rec Closed l1' pf1')) by (rewrite eq12; apply rtype_fequal; reflexivity).
        rewrite H0 in IHe2; clear H0.
        simpl in H; clear eq12 eq11.
        assert (RecMaybe Closed l1' = Some (Rec Closed l1' pf1')) by apply RecMaybe_pf_some.
        rewrite H0 in H; clear H0.
        case_eq (infer_nra_type e1 (Rec Closed l1' pf1')); intros.
        * rewrite H0 in H; simpl in H.
          destruct r; try congruence.
          destruct x; simpl in H; try congruence.
          destruct x; simpl in H; try congruence.
          destruct k; simpl in H; try congruence.
          destruct (from_Rec₀ srl0 e0) as [l2' [pf2' [eq21 eq22]]].
          assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ (Rec₀ Closed srl0)) e0 =
                  Coll (Rec Closed l2' pf2')) by (rewrite eq22; apply rtype_fequal; reflexivity).
          rewrite H1 in *.
          specialize (IHe1 (Rec Closed l1' pf1') (Coll (Rec Closed l2' pf2')) H0).
          assert (is_list_sorted ODT_lt_dec
                                 (domain (rec_concat_sort l1' l2')) = true)
            by (apply (rec_concat_sort_sorted l1' l2'); reflexivity).
          assert (RecMaybe Closed (rec_concat_sort l1' l2') = Some (Rec Closed (rec_concat_sort l1' l2') H2))
            by apply RecMaybe_pf_some.
          simpl in H.
          clear e eq22 H1 eq21 H0.
          generalize (@type_NRAMapProduct m τconstants τin l1' l2' (rec_concat_sort l1' l2')
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
          rewrite <- H1 in H; clear H1.
          destruct (RecMaybe Closed (rec_concat_sort l1' l2')).
          inversion H.
          rewrite H4.
          inversion H3.
          rewrite <- H5.
          auto.
          congruence.
          rewrite H1.
          assumption.
        * rewrite H0 in H; simpl in H; congruence.
      + rewrite H0 in H; simpl in H; congruence.
    - Case "NRAProduct"%string.
      case_eq (infer_nra_type e1 τin); intros.
      case_eq (infer_nra_type e2 τin); intros.
      + specialize (IHe1 τin r H0). rewrite H0 in H; simpl in *.
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
        specialize (IHe2 τin (Coll (Rec Closed l2' pf2')) H1).
        assert (is_list_sorted ODT_lt_dec
                               (domain (rec_concat_sort l1' l2')) = true)
          by (apply (rec_concat_sort_sorted l1' l2'); reflexivity).
        assert (RecMaybe Closed (rec_concat_sort l1' l2') = Some (Rec Closed (rec_concat_sort l1' l2') H2))
          by apply RecMaybe_pf_some.
        clear e eq22 H1 eq21 srl0 H0.
        generalize (@type_NRAProduct m τconstants τin l1' l2' (rec_concat_sort l1' l2')
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
          rewrite <- H1 in H; clear H1.
        destruct (RecMaybe Closed (rec_concat_sort l1' l2')).
        inversion H.
        rewrite H4.
        inversion H3.
        rewrite <- H5.
        auto.
        congruence.
        rewrite H1.
        assumption.
      + rewrite H1 in H. simpl in H.
        destruct ((olift tmapConcatInput (infer_nra_type e1 τin))); simpl in H.
        destruct (RecMaybe Closed l); congruence.
        congruence.
      + rewrite H0 in H; simpl in H; congruence.
    - Case "NRASelect"%string.
      simpl.
      case_eq (infer_nra_type e2 τin); intros; simpl in *.
      + specialize (IHe2 τin r H0). rewrite H0 in H. simpl in *.
        unfold lift in H.
        case_eq (tuncoll r); intros. rewrite H1 in *.
        inversion H. subst. clear H H0.
        case_eq (infer_nra_type e1 r0); intros.
        specialize (IHe1 r0 r1 H).
        rewrite H in H3.
        destruct r1; try congruence; simpl in *.
        destruct x; try congruence; simpl in *.
        inversion H3; clear H3 H2.
        apply (@type_NRASelect m τconstants τin r0); try assumption.
        assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) Bool₀ e = Bool).
        apply rtype_fequal; reflexivity.
        rewrite H0 in IHe1. assumption.
        apply tuncoll_correct in H1.
        rewrite <- H1; assumption.
        rewrite H in H3; congruence.
        rewrite H1 in H; congruence.
      + rewrite H0 in H. simpl in H; congruence.
    - Case "NRADefault"%string.
      specialize (IHe1 τin); specialize (IHe2 τin).
      destruct (infer_nra_type e1 τin); destruct (infer_nra_type e2 τin); simpl in *;
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
      apply type_NRADefault; assumption.
    - Case "NRAEither"%string.
      unfold tuneither in H.
      destruct τin.
      destruct x; simpl in *; try discriminate.
      match_case_in H; intros; rewrite H0 in H; try discriminate.
      match_case_in H; intros; rewrite H1 in H; try discriminate.
      match_destr_in H.
      red in e0.
      invcs H; subst.
      specialize (IHe1 _ _ H0).
      specialize (IHe2 _ _ H1).
      erewrite Either_canon
      ; eapply type_NRAEither
      ; eauto.
    - Case "NRAEitherConcat"%string.
      case_eq (infer_nra_type e1 τin); case_eq (infer_nra_type e2 τin); simpl in *; intros;
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
      specialize (IHe1 _ _ H1).
      specialize (IHe2 _ _ H0).
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
      eapply type_NRAEitherConcat; eauto.
    - Case "NRAApp"%string.
      specialize (IHe2 τin).
      destruct (infer_nra_type e2 τin).
      specialize (IHe2 r eq_refl).
      econstructor; eauto.
      simpl in *; congruence.
  Qed.

  (* Still should try and prove most specific and completeness theorems ... *)
  
End TNRAInfer.

