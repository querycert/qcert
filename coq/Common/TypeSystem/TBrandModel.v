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
Require Import ListSet.
Require Import Sumbool.
Require Import Arith.
Require Import Bool.
Require Import Morphisms.
Require Import Basics.
Require Import EquivDec.
Require Import Eqdep_dec.
Require Import Utils.
Require Import ForeignType.
Require Import RType.
Require Export BrandRelation.
Require Export TBrandContext.
Require Import RSubtype.
Require Import RConsistentSubtype.

Section TBrandModel.

  Definition sub_brand_context {br:brand_relation} {ftype:foreign_type} (m1 m2:brand_context) :=
    subtype (brand_context_Rec m1) (brand_context_Rec m2).

  Section brand_model_types.
    Context {ftype:foreign_type} {br:brand_relation} {m:brand_context}.

    Definition brand_model_domain_t
      := forall a, In a (domain brand_relation_brands) ->
                   In a (domain brand_context_types).

    Definition brand_model_subtype_weak_t :=
      forall a b τa,
        In (a,b) brand_relation_brands ->
        In (a,τa) brand_context_types ->
        exists (τb:rtype),
          In (b,τb) brand_context_types /\
          subtype τa τb.

    Definition brand_model_subtype_t :=
      forall a b τa,
        In (a,b) brand_relation_brands ->
        In (a,τa) brand_context_types ->
        {τb:rtype | 
         In (b,τb) brand_context_types /\ subtype τa τb}.

    Section brand_model_types_dec.

Lemma brand_model_domain_dec :
  {brand_model_domain_t }
  +  {~ brand_model_domain_t}.
Proof.
  apply (incl_list_dec string_dec).
Defined.

Lemma brand_model_subtype_weak_dec :
  {brand_model_subtype_weak_t}
  +  {~ brand_model_subtype_weak_t}.
Proof.
  unfold brand_model_subtype_weak_t.
  case_eq (forallb
             (fun ab =>
                match lookup string_dec brand_context_types (fst ab) with
                  | Some ta => match lookup string_dec brand_context_types (snd ab) with
                                 | Some tb => if subtype_dec ta tb then true else false
                                 | None => false
                               end
                  | None => true
                end)
             brand_relation_brands).
  - left. intros.
    rewrite forallb_forall in H.
    specialize (H _ H0).
    match_case_in H; intros.
    + rewrite H2 in *.
      apply lookup_in in H2; simpl in *.
      generalize (nodup_in_eq brand_context_nodup H1 H2); intros; subst.
      match_case_in H; intros.
      * rewrite H3 in *. match_destr_in H.
        apply lookup_in in H3. simpl in *.
        exists r0; intuition.
      * rewrite H3 in H; discriminate.
    +  rewrite H2 in H; simpl in *.
        apply lookup_none_nin in H2. apply in_dom in H1. intuition.
  - right.
    rewrite forallb_not_existb in H; rewrite negb_false_iff in H.
    rewrite existsb_exists in H.
    destruct H as [[? ?] [inn ne]].
    rewrite negb_true_iff in ne.
    match_case_in ne; intros.
    + rewrite H in ne; simpl in *.
       intro fb. specialize (fb _ _ _ inn (lookup_in _ _ H)).
       destruct fb as [? [inn2 sub]].
       match_case_in ne; intros.
       * rewrite H0 in ne.
         apply lookup_in in H0.
         generalize (nodup_in_eq brand_context_nodup H0 inn2); intros; subst.
         match_destr_in ne.
         intuition.
       * apply lookup_none_nin in H0.  apply in_dom in inn2.
         intuition.
    + rewrite H in *. discriminate. 
Defined.

    End brand_model_types_dec.
    
End brand_model_types.

  Context {ftype:foreign_type}.
  
  Class brand_model :=
    mkBrand_model {
        (* note that brand_context_brand_model can have duplicates in the domain *)
        brand_model_relation :> brand_relation;
        brand_model_context :> brand_context;
        brand_model_domain_b :
         holds (brand_model_domain_dec);
            
        brand_model_subtype_weak_b :
           holds (brand_model_subtype_weak_dec)
      }.

Section brand_model_prop.
  Context {m:brand_model}.
Lemma brand_model_domain :
  brand_model_domain_t.
Proof.
  generalize (brand_model_domain_b).
  unfold holds, is_true; match_destr.
Qed.

Lemma brand_model_subtype_weak :
  brand_model_subtype_weak_t.
Proof.
  generalize (brand_model_subtype_weak_b).
  unfold holds, is_true; match_destr.
Qed.

Lemma brand_model_subtype :
  brand_model_subtype_t.
Proof.
  generalize (brand_model_subtype_weak_b).
  unfold holds, is_true; match_destr.
  unfold brand_model_subtype_t, brand_model_subtype_weak_t in *;
    intros.
  case_eq (lookup string_dec brand_context_types b0); intros.
  - exists r.
    destruct (b _ _ _ H0 H1) as [? [inn sub]].
    apply lookup_in in H2.
    generalize (nodup_in_eq brand_context_nodup H2 inn). intros; subst.
    intuition.
  - apply lookup_none_nin in H2. elim H2.
    destruct (b _ _ _ H0 H1) as [? [??]].
    apply in_dom in H3. trivial.
Qed.

  End brand_model_prop.

  Lemma brand_model_ext a b pf1 pf2 pf1' pf2' :
    mkBrand_model a b pf1 pf2  = mkBrand_model a b pf1' pf2'.
  Proof.
    f_equal; apply UIP_dec; apply bool_dec.
  Defined.

  Definition make_brand_model (b:brand_relation) (m:brand_context)
             (pf:
             (is_true (brand_model_domain_dec)
            && is_true (brand_model_subtype_weak_dec)
             ) = true) : brand_model.
  Proof.
    unfold is_true in *.
    match_case_in pf; intros ? eqq.
    - case_eq (brand_model_subtype_weak_dec); intros ? eqq2.
      + apply (@mkBrand_model b m); unfold holds, is_true;
        try rewrite eqq; try rewrite eqq2; trivial.
      + rewrite eqq, eqq2 in pf. simpl in pf. discriminate.
    - rewrite eqq in pf. simpl in pf. discriminate.
  Defined.

  Definition make_brand_model_fails (b:brand_relation) (m:brand_context) : option brand_model.
  Proof.
    generalize (make_brand_model b m); intros;
    destruct (is_true brand_model_domain_dec);
    destruct (is_true brand_model_subtype_weak_dec).
    - specialize (H eq_refl).
      exact (Some H).
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Program Definition empty_brand_model := make_brand_model (mkBrand_relation nil _ _) (mkBrand_context nil _).
  Next Obligation.
    unfold holds. auto.
  Qed.
  Next Obligation.
    unfold holds. auto.
  Defined.

End TBrandModel.

