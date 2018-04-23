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
Require Import Permutation.
Require Import Sumbool.
Require Import Arith.
Require Import Bool.
Require Import Morphisms.
Require Import Basics.
Require Import Utils.
Require Import ForeignType.
Require Import RType.
Require Import RSubtype.
Require Export TBrandModel.
Require Import RSubtypeProp.
Require Import RTypeLattice.
Require Import RTypeMeetJoin.

Section TBrandModelProp.

  Context {ftype:foreign_type}.
  Context {m:brand_model}.
  
  Lemma sub_brand_in {b0 b τbrand} :
    sub_brand brand_relation_brands b0 b ->
    In (b, τbrand) brand_context_types ->
    exists τ₂, 
      In (b0, τ₂) brand_context_types /\
      subtype τ₂ τbrand.
  Proof.
    unfold sub_brand.
    destruct 1; intros; subst.
    - exists τbrand; intuition.
    - intros.
      generalize (@brand_model_domain _ _ _ (in_dom H)); intros inn.
      apply in_domain_in in inn.
      destruct inn as [? inn].
      destruct (@brand_model_subtype _ _ _ _ _ H inn) as [?[??]].
      generalize (is_list_sorted_NoDup _ _ (brand_context_types_sorted)); intros nd.
      generalize (nodup_in_eq nd H0 H1); intros; subst.
      eauto.
  Qed.

  Definition brands_type_list (b:brands) : (list rtype)
    := flat_map (fun bb =>
                   match lookup string_dec brand_context_types bb with
                     | Some τ => (τ::nil)
                     | None => nil
                   end) b.
  
  Definition brands_type (b:brands) : rtype
    := fold_left meet (brands_type_list b) ⊤ .

  Lemma brands_type_singleton (bb:brand) 
  : brands_type (singleton bb) =
    match lookup string_dec brand_context_types bb with
      | Some τ => τ
      | None => ⊤
    end.
  Proof.
    unfold brands_type, singleton.
    simpl.
    match_destr; simpl.
    autorewrite with rtype_meet.
    trivial.
  Qed.
    
  Lemma brands_type_list_app b1 b2 :
    brands_type_list (b1 ++ b2) =  brands_type_list b1 ++ brands_type_list b2.
  Proof.
    unfold brands_type_list.
    apply flat_map_app.
  Qed.

  Lemma brands_type_alt (b :brands) :
    brands_type b = fold_right meet ⊤ (brands_type_list b).
  Proof.
    apply fold_symmetric.
    - intros. rewrite meet_associative; trivial.
    - intros. rewrite meet_commutative; trivial.
  Qed.

  
  Global Instance brands_type_sub_proper :
    Proper (sub_brands brand_relation_brands ==> subtype) brands_type.
  Proof.
    unfold Proper, respectful.
    intros x y sub.
    repeat rewrite brands_type_alt.
    revert x sub.
    unfold sub_brands.   
    induction y; simpl.
    intros.
    - apply STop.
    - intros x inn.
      rewrite fold_right_app.
      specialize (IHy x). cut_to IHy.
      + match_case; simpl; intros.
        specialize (inn a). cut_to inn; [| intuition].
        destruct inn as [b [inb subb]].
        destruct (sub_brand_in subb (lookup_in _ _ H))
          as [r2 [in2 sub2]].
        assert (eqq:fold_right rtype_meet ⊤ (brands_type_list x)=
                 fold_right rtype_meet ⊤ (r2::(brands_type_list x))).
        apply fold_right_equivlist.
        * intros; rewrite rtype_meet_associative; reflexivity.
        * intros; rewrite rtype_meet_commutative; reflexivity.
        * intros; rewrite rtype_meet_idempotent; reflexivity.
        * {
            assert (eqq2:equivlist (brands_type_list x) (brands_type_list (b::x))).
            - destruct (in_split _ _ inb) as [t1 [t2 teq]].
              rewrite teq.
              simpl.
              repeat rewrite brands_type_list_app.
              simpl.
              match_destr; simpl; try reflexivity.
              
              assert (perm:Permutation (brands_type_list t1 ++ r0 :: brands_type_list t2) (r0::brands_type_list t1 ++ brands_type_list t2))
                by (rewrite Permutation_middle; reflexivity).
              rewrite perm.
              apply equivlist_incls; split; intros ?; simpl; intros inn;
              intuition.
            - simpl in eqq2.
              eapply (in_lookup_nodup string_dec) in in2.
              + rewrite in2 in eqq2.
                simpl in eqq2; trivial.
              + eapply is_list_sorted_NoDup_strlt.
                eapply brand_context_types_sorted.
          } 
        * rewrite eqq.
          simpl.
          apply (meet_leq_proper (olattice:=rtype_olattice)); auto.
      + intuition.
  Qed.

  Lemma brands_type_sub_part bb τ b :
    lookup string_dec brand_context_types bb = Some τ ->
    In bb b ->
    brands_type b <: τ.
  Proof.
    intros look inn.
    replace τ with (brands_type (singleton bb)).
    - apply brands_type_sub_proper.
      unfold sub_brands, sub_brand, singleton; simpl.
      intuition; subst.
      eauto.
    - rewrite brands_type_singleton, look; trivial.
  Qed.

  Lemma brands_type_of_canon b :
    brands_type (canon_brands brand_relation_brands b) = brands_type b.
  Proof.
    destruct (canon_brands_equiv b).
    apply antisymmetry; apply brands_type_sub_proper; trivial.
  Qed.
  
End TBrandModelProp.

