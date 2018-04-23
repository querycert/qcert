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
Require Import Program.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonSystem.
Require Import cNNRC.
Require Import TcNNRC.

Section TcNNRCInfer.
  Context {m:basic_model}.
  Context (τconstants:tbindings).

  (** Type inference for NNRC when given the type of the environment *)

  Fixpoint infer_nnrc_core_type (tenv:tbindings) (n:nnrc) {struct n} : option rtype :=
    match n with
    | NNRCGetConstant v =>
      tdot τconstants v
    | NNRCVar v =>
      lookup equiv_dec tenv v
    | NNRCConst d => infer_data_type (normalize_data brand_relation_brands d)
    | NNRCBinop b n1 n2 =>
      let binf (τ₁ τ₂:rtype) := infer_binary_op_type b τ₁ τ₂ in
      olift2 binf (infer_nnrc_core_type tenv n1) (infer_nnrc_core_type tenv n2)
    | NNRCUnop u n1 =>
        let unf (τ₁:rtype) := infer_unary_op_type u τ₁ in
        olift unf (infer_nnrc_core_type tenv n1)
    | NNRCLet v n1 n2 =>
      let τ₁ := infer_nnrc_core_type tenv n1 in
      let let_infer τ := infer_nnrc_core_type ((v,τ)::tenv) n2 in
      olift let_infer τ₁
    | NNRCFor v n1 n2 =>
      let τ₁ := infer_nnrc_core_type tenv n1 in
      let for_infer τ := lift Coll (infer_nnrc_core_type ((v,τ)::tenv) n2) in
      olift for_infer (olift tuncoll τ₁)
    | NNRCIf n0 n1 n2 =>
      match infer_nnrc_core_type tenv n0 with
      | Some τ₀ =>
        match `τ₀ with
        | Bool₀ =>
          let oτ₁ := infer_nnrc_core_type tenv n1 in
          let oτ₂ := infer_nnrc_core_type tenv n2 in
          match (oτ₁, oτ₂) with
            | (Some τ₁, Some τ₂) =>
              if (rtype_eq_dec τ₁ τ₂) (* Probably should be generalized using join... *)
              then Some τ₁
              else None
            | (_, _) => None
          end
        | _ => None
        end
      | None => None
      end
    | NNRCEither n0 v1 n1 v2 n2 =>
      match olift tuneither (infer_nnrc_core_type tenv n0) with
      | Some (τl, τr) =>
          let oτ₁ := infer_nnrc_core_type ((v1,τl)::tenv) n1 in
          let oτ₂ := infer_nnrc_core_type ((v2,τr)::tenv) n2 in
          match (oτ₁, oτ₂) with
            | (Some τ₁, Some τ₂) =>
              if (rtype_eq_dec τ₁ τ₂) (* Probably should be generalized using join... *)
              then Some τ₁
              else None
            | (_, _) => None
          end
      | _ => None
      end
    | NNRCGroupBy g sl n1 =>
      None (* For core, always fails *)
    end.

  Lemma infer_nnrc_core_type_correct {τout} (tenv:tbindings) (n:nnrc) :
    infer_nnrc_core_type tenv n = Some τout ->
    nnrc_core_type τconstants tenv n τout.
  Proof.
    revert tenv τout.
    nnrc_cases (induction n) Case; intros; simpl in *.
    - Case "NNRCGetConstant"%string.
      apply type_cNNRCGetConstant; assumption.
    - Case "NNRCVar"%string.
      apply type_cNNRCVar; assumption.
    - Case "NNRCConst"%string.
      apply type_cNNRCConst.
      apply infer_data_type_correct. assumption.
    - Case "NNRCBinop"%string.
      specialize (IHn1 tenv); specialize (IHn2 tenv).
      destruct (infer_nnrc_core_type tenv n1); destruct (infer_nnrc_core_type tenv n2); simpl in *;
      try discriminate.
      specialize (IHn1 r eq_refl); specialize (IHn2 r0 eq_refl).
      apply (@type_cNNRCBinop m τconstants r r0 τout tenv); try assumption.
      apply infer_binary_op_type_correct; assumption.
    - Case "NNRCUnop"%string.
      specialize (IHn tenv).
      destruct (infer_nnrc_core_type tenv n); simpl in *;
      try discriminate.
      specialize (IHn r eq_refl).
      apply (@type_cNNRCUnop m τconstants r τout tenv); try assumption.
      apply infer_unary_op_type_correct; assumption.
    - Case "NNRCLet"%string.
      specialize (IHn1 tenv).
      destruct (infer_nnrc_core_type tenv n1); simpl in *; try discriminate.
      specialize (IHn2 ((v,r) :: tenv)).
      destruct (infer_nnrc_core_type ((v, r) :: tenv) n2); simpl in *; try discriminate.
      inversion H; subst; clear H.
      specialize (IHn1 r eq_refl).
      specialize (IHn2 τout eq_refl).
      apply (type_cNNRCLet τconstants v tenv n1 n2 IHn1 IHn2).
    - Case "NNRCFor"%string.
      specialize (IHn1 tenv).
      destruct (infer_nnrc_core_type tenv n1); simpl in *; try discriminate.
      case_eq (tuncoll r); intros; rewrite H0 in *; simpl in H.
      + apply tuncoll_correct in H0.
        specialize (IHn2 ((v,r0) :: tenv)).
        destruct (infer_nnrc_core_type ((v, r0) :: tenv) n2); simpl in *; try discriminate.
        inversion H; subst; clear H.
        specialize (IHn1 (Coll r0) eq_refl).
        specialize (IHn2 r1 eq_refl).
        apply (type_cNNRCFor τconstants v tenv n1 n2 IHn1 IHn2).
      + discriminate.
    - Case "NNRCIf"%string.
      specialize (IHn1 tenv).
      specialize (IHn2 tenv).
      specialize (IHn3 tenv).
      destruct (infer_nnrc_core_type tenv n1); simpl in *; try discriminate.
      destruct r; try congruence; simpl in H.
      destruct x; try congruence; simpl in H.
      destruct (infer_nnrc_core_type tenv n2); simpl in *; try discriminate.
      destruct (infer_nnrc_core_type tenv n3); simpl in *; try discriminate.
      destruct (rtype_eq_dec r r0); simpl in *; try congruence.
      rewrite e0 in *; clear e0.
      inversion H; clear H; subst.
      assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) Bool₀ e = Bool) by (apply rtype_fequal; reflexivity).
      rewrite H in IHn1; clear H.
      specialize (IHn1 Bool eq_refl).
      specialize (IHn2 τout eq_refl).
      specialize (IHn3 τout eq_refl).
      apply type_cNNRCIf; assumption.
    - Case "NNRCEither"%string.
      specialize (IHn1 tenv).
      destruct (infer_nnrc_core_type tenv n1); simpl in *; try discriminate.
      unfold tuneither in H.
      destruct r; simpl in H; try discriminate.
      destruct x; simpl in H; try discriminate.
      match_case_in H; intros; rewrite H0 in H; try discriminate.
      match_case_in H; intros; rewrite H1 in H; try discriminate.
      match_destr_in H.
      red in e0.
      invcs H; subst.
      specialize (IHn1 (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) 
                              (Either₀ x1 x2) e) eq_refl).
      specialize (IHn2 _ _ H0).
      specialize (IHn3 _ _ H1).
      eapply type_cNNRCEither; eauto.
      erewrite <- Either_canon; eauto.
    - Case "NNRCGroupBy"%string.
      congruence. (* Type checking always fails for groupby in core NNRC *)
  Qed.

End TcNNRCInfer.

