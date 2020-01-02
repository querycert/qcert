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
Require Import BrandRelation.
Require Import ForeignType.
Require Import RType.

Section TBrandContext.

  (** Implicitly, everything derives from Any *)
  Definition Any {ftype:foreign_type} {br:brand_relation} := Brand nil. 

  Section Brand_Context.
    Context {ftype:foreign_type}.
    Context {br:brand_relation}.
    
    (** Represents a mapping from brands to types *)
    Definition brand_context_decls : Set := list (string*rtype).
    Class brand_context :=
      mkBrand_context {
          brand_context_types : brand_context_decls;
          brand_context_types_sorted : is_list_sorted ODT_lt_dec (domain brand_context_types) = true
        }.

    Lemma brand_context_nodup {m:brand_context} : NoDup (domain brand_context_types).
    Proof.
      eapply is_list_sorted_NoDup.
      - eapply StringOrder.lt_strorder.
      - apply brand_context_types_sorted.
    Qed.

    Lemma brand_context_ext m pf1 pf1':
      mkBrand_context m pf1 = mkBrand_context m pf1'.
    Proof.
      f_equal.
      - apply UIP_dec. apply bool_dec.
    Defined.
  
    Lemma brand_context_fequal {m₁ m₂}:
      @brand_context_types m₁ = @brand_context_types m₂ -> m₁ = m₂.
    Proof.
      destruct m₁; destruct m₂; simpl; intros; subst.
      apply brand_context_ext.
    Qed.

    Definition brand_context_Rec (m:brand_context) := Rec Open _ (brand_context_types_sorted).

    Lemma brand_context_Rec_inj (m1 m2:brand_context) :
      brand_context_Rec m1 = brand_context_Rec m2 -> m1 = m2.
    Proof.
      inversion 1; rtype_equalizer; subst.
      apply brand_context_fequal; trivial.
    Qed.

  End Brand_Context.
End TBrandContext.

