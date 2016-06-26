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

Section TNRCInfer.

  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import Program.
  Require Import EquivDec Morphisms.

  Require Import Utils BasicSystem.
  Require Import NNRC.

  Require Import TNRC.

  Context {m:basic_model}.

  (** Type inference for NNRC when given the type of the environment *)

  Require Import TDataInfer.
  Require Import TOpsInfer.

  Fixpoint infer_nrc_type (tenv:tbindings) (n:nrc) {struct n} : option rtype :=
    match n with
    | NRCVar v =>
      lookup equiv_dec tenv v
    | NRCConst d => infer_data_type (normalize_data brand_relation_brands d)
    | NRCBinop b n1 n2 =>
      let binf (τ₁ τ₂:rtype) := infer_binop_type b τ₁ τ₂ in
      olift2 binf (infer_nrc_type tenv n1) (infer_nrc_type tenv n2)
    | NRCUnop u n1 =>
        let unf (τ₁:rtype) := infer_unop_type u τ₁ in
        olift unf (infer_nrc_type tenv n1)
    | NRCLet v n1 n2 =>
      let τ₁ := infer_nrc_type tenv n1 in
      let let_infer τ := infer_nrc_type ((v,τ)::tenv) n2 in
      olift let_infer τ₁
    | NRCFor v n1 n2 =>
      let τ₁ := infer_nrc_type tenv n1 in
      let for_infer τ := lift Coll (infer_nrc_type ((v,τ)::tenv) n2) in
      olift for_infer (olift tuncoll τ₁)
    | NRCIf n0 n1 n2 =>
      match infer_nrc_type tenv n0 with
      | Some τ₀ =>
        match `τ₀ with
        | Bool₀ =>
          let oτ₁ := infer_nrc_type tenv n1 in
          let oτ₂ := infer_nrc_type tenv n2 in
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
    | NRCEither n0 v1 n1 v2 n2 =>
      match olift tuneither (infer_nrc_type tenv n0) with
      | Some (τl, τr) =>
          let oτ₁ := infer_nrc_type ((v1,τl)::tenv) n1 in
          let oτ₂ := infer_nrc_type ((v2,τr)::tenv) n2 in
          match (oτ₁, oτ₂) with
            | (Some τ₁, Some τ₂) =>
              if (rtype_eq_dec τ₁ τ₂) (* Probably should be generalized using join... *)
              then Some τ₁
              else None
            | (_, _) => None
          end
      | _ => None
      end
    end.
  
  Lemma infer_nrc_type_correct {τout} (tenv:tbindings) (n:nrc) :
    infer_nrc_type tenv n = Some τout ->
    nrc_type tenv n τout.
  Proof.
    revert tenv τout.
    nrc_cases (induction n) Case; intros; simpl in *.
    - Case "NRCVar"%string.
      apply TNRCVar; assumption.
    - Case "NRCConst"%string.
      apply TNRCConst.
      apply infer_data_type_correct. assumption.
    - Case "NRCBinop"%string.
      specialize (IHn1 tenv); specialize (IHn2 tenv).
      destruct (infer_nrc_type tenv n1); destruct (infer_nrc_type tenv n2); simpl in *;
      try discriminate.
      specialize (IHn1 r eq_refl); specialize (IHn2 r0 eq_refl).
      apply (@TNRCBinop m r r0 τout tenv); try assumption.
      apply infer_binop_type_correct; assumption.
    - Case "NRCUnop"%string.
      specialize (IHn tenv).
      destruct (infer_nrc_type tenv n); simpl in *;
      try discriminate.
      specialize (IHn r eq_refl).
      apply (@TNRCUnop m r τout tenv); try assumption.
      apply infer_unop_type_correct; assumption.
    - Case "NRCLet"%string.
      specialize (IHn1 tenv).
      destruct (infer_nrc_type tenv n1); simpl in *; try discriminate.
      specialize (IHn2 ((v,r) :: tenv)).
      destruct (infer_nrc_type ((v, r) :: tenv) n2); simpl in *; try discriminate.
      inversion H; subst; clear H.
      specialize (IHn1 r eq_refl).
      specialize (IHn2 τout eq_refl).
      apply (TNRCLet v tenv n1 n2 IHn1 IHn2).
    - Case "NRCFor"%string.
      specialize (IHn1 tenv).
      destruct (infer_nrc_type tenv n1); simpl in *; try discriminate.
      case_eq (tuncoll r); intros; rewrite H0 in *; simpl in H.
      + apply tuncoll_correct in H0.
        specialize (IHn2 ((v,r0) :: tenv)).
        destruct (infer_nrc_type ((v, r0) :: tenv) n2); simpl in *; try discriminate.
        inversion H; subst; clear H.
        specialize (IHn1 (Coll r0) eq_refl).
        specialize (IHn2 r1 eq_refl).
        apply (TNRCFor v tenv n1 n2 IHn1 IHn2).
      + discriminate.
    - Case "NRCIf"%string.
      specialize (IHn1 tenv).
      specialize (IHn2 tenv).
      specialize (IHn3 tenv).
      destruct (infer_nrc_type tenv n1); simpl in *; try discriminate.
      destruct r; try congruence; simpl in H.
      destruct x; try congruence; simpl in H.
      destruct (infer_nrc_type tenv n2); simpl in *; try discriminate.
      destruct (infer_nrc_type tenv n3); simpl in *; try discriminate.
      destruct (rtype_eq_dec r r0); simpl in *; try congruence.
      rewrite e0 in *; clear e0.
      inversion H; clear H; subst.
      assert (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) Bool₀ e = Bool) by (apply rtype_fequal; reflexivity).
      rewrite H in IHn1; clear H.
      specialize (IHn1 Bool eq_refl).
      specialize (IHn2 τout eq_refl).
      specialize (IHn3 τout eq_refl).
      apply TNRCIf; assumption.
    - Case "NRCEither"%string.
      specialize (IHn1 tenv).
      destruct (infer_nrc_type tenv n1); simpl in *; try discriminate.
      unfold tuneither in H.
      destruct r; simpl in H; try congruence.
      destruct x; simpl in H; try congruence.
      unfold and_rec, and_rect in H.
      destruct (Either₀_wf_inv e); simpl in *.
      specialize (IHn2 ((v, exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x1 e0)
                          :: tenv)).
      specialize (IHn3 ((v0, exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x2 e1)
                          :: tenv)).
      assert
        (infer_nrc_type
           ((v, exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x1 e0)
              :: tenv) n2 =
         infer_nrc_type
           (@cons
              (prod var
                    (@rtype (@basic_model_foreign_type m)
                            (@brand_model_relation (@basic_model_foreign_type m)
                                                   (@basic_model_brand_model m))))
              (@pair var
                     (@rtype (@basic_model_foreign_type m)
                             (@brand_model_relation (@basic_model_foreign_type m)
                                                    (@basic_model_brand_model m))) v
                     (@exist (@rtype₀ (@basic_model_foreign_type m))
                             (fun τ₀ : @rtype₀ (@basic_model_foreign_type m) =>
                                @eq bool
                                    (@wf_rtype₀ (@basic_model_foreign_type m)
                                                (@brand_model_relation
                                                   (@basic_model_foreign_type m)
                                                   (@basic_model_brand_model m)) τ₀) true) x1
                             e0)) tenv) n2) by reflexivity.
      rewrite <- H0 in H; clear H0.
      destruct (infer_nrc_type ((v, exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x1 e0)
                                  :: tenv) n2); simpl in H; try congruence.
      assert
        (infer_nrc_type
           ((v0, exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x2 e1)
              :: tenv) n3 =
         infer_nrc_type
           (@cons
              (prod var
                    (@rtype (@basic_model_foreign_type m)
                            (@brand_model_relation (@basic_model_foreign_type m)
                                                   (@basic_model_brand_model m))))
              (@pair var
                     (@rtype (@basic_model_foreign_type m)
                             (@brand_model_relation (@basic_model_foreign_type m)
                                                    (@basic_model_brand_model m))) v0
                     (@exist (@rtype₀ (@basic_model_foreign_type m))
                             (fun τ₀ : @rtype₀ (@basic_model_foreign_type m) =>
                                @eq bool
                                    (@wf_rtype₀ (@basic_model_foreign_type m)
                                                (@brand_model_relation
                                                   (@basic_model_foreign_type m)
                                                   (@basic_model_brand_model m)) τ₀) true) x2
                             e1)) tenv) n3) by reflexivity.
      rewrite <- H0 in H; clear H0.
      destruct (infer_nrc_type ((v0, exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x2 e1)
                                  :: tenv) n3); simpl in H; try congruence.
      destruct (rtype_eq_dec r r0); try congruence; simpl.
      rewrite e2 in *; clear e2.
      inversion H; subst; clear H.
      specialize (IHn1 (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) 
                              (Either₀ x1 x2) e) eq_refl).
      specialize (IHn2 τout eq_refl).
      specialize (IHn3 τout eq_refl).
      assert ((exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Either₀ x1 x2) e)
              = Either (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x1 e0)
                       (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x2 e1))
        by (apply rtype_fequal; reflexivity).
      rewrite H in IHn1. 
      apply (TNRCEither tenv n1 v n2 v0 n3 IHn1 IHn2 IHn3).
  Qed.

End TNRCInfer.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
