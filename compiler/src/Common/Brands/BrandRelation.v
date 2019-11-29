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
Require Import Bool.
Require Import EquivDec.
Require Import Eqdep_dec.
Require Import Basics.
Require Import ListSet.
Require Import Program.Basics.
Require Import RelationClasses.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.

Definition brand := string.
Definition brands := list brand.

Definition any : brands := nil.

Definition brand_relation_t := list (string*string).

Section brand_relation_types.
  Context  (brand_relation_brands:brand_relation_t).

  Definition brand_relation_trans_t
    := forall a b c, In (a,b) brand_relation_brands ->
                     In (b,c) brand_relation_brands ->
                     In (a,c) brand_relation_brands.
    
  Definition brand_relation_assym_t
    := forall a b, In (a,b) brand_relation_brands ->
                   ~ In (b,a) brand_relation_brands.

  Section brand_relation_dec.
   
    Lemma brand_relation_trans_dec :
      {brand_relation_trans_t}
      +  {~ brand_relation_trans_t}.
    Proof.
      unfold brand_relation_trans_t.
      case_eq (forallb (fun ab => forallb (fun bc =>
                                             if string_dec (snd ab) (fst bc)
                                             then set_mem (pair_eqdec) ((fst ab), (snd bc)) brand_relation_brands 
                                             else true
                                          ) brand_relation_brands) brand_relation_brands).
      - left; intros.
        rewrite forallb_forall in H.
        specialize (H _ H0).
        rewrite forallb_forall in H.
        specialize (H _ H1).
        match_destr_in H; simpl in *; [| intuition ].
        apply set_mem_correct1 in H. trivial.
      - right; intro fb.
        rewrite forallb_not_existb, negb_false_iff, existsb_exists in H.
        destruct H as [[? ?] [inn ne]].
        rewrite negb_true_iff, forallb_not_existb, negb_false_iff, existsb_exists in ne.
        destruct ne as [[? ?] [inn2 ne]].
        simpl in *.
        match_destr_in ne; subst.
        rewrite negb_true_iff in ne.
        apply set_mem_complete1 in ne.
        specialize (fb _ _ _ inn inn2). 
        apply (ne fb). 
    Defined.

    Lemma brand_relation_assym_dec :
      {brand_relation_assym_t}
      +  {~ brand_relation_assym_t}.
    Proof.
      unfold brand_relation_assym_t.
      case_eq (forallb (fun ab =>
                          negb (set_mem (pair_eqdec) ((snd ab), (fst ab)) brand_relation_brands)) brand_relation_brands).
      - left; intros.
        rewrite forallb_forall in H.
        specialize (H _ H0).
        apply negb_true_iff in H.
        apply set_mem_complete1 in H. simpl in *.
        trivial.
      - right; intro fb.
        rewrite forallb_not_existb, negb_false_iff, existsb_exists in H.
        destruct H as [[? ?] [inn ne]].
        rewrite negb_involutive in ne.
        apply set_mem_correct1 in ne.
        simpl in *.
        apply (fb _ _ inn ne).
    Defined.

  End brand_relation_dec.
End brand_relation_types.

Class brand_relation :=
  mkBrand_relation {
      brand_relation_brands : list (string*string);
      
      brand_relation_trans_b :
        holds (brand_relation_trans_dec brand_relation_brands);
      brand_relation_assym_b :
        holds (brand_relation_assym_dec brand_relation_brands)
    }.

Section brand_relation_prop.
  Context {br:brand_relation}.
  
  Lemma brand_relation_trans :
    brand_relation_trans_t brand_relation_brands.
  Proof.
    generalize (brand_relation_trans_b).
    unfold holds, is_true; match_destr.
  Qed.
    
  Lemma brand_relation_assym :
    brand_relation_assym_t brand_relation_brands.
  Proof.
    generalize (brand_relation_assym_b).
    unfold holds, is_true; match_destr.
  Qed.
  
  Lemma brand_relation_irrefl a : ~ In (a,a) brand_relation_brands.
  Proof.
    intro inn.
    apply (brand_relation_assym a a); trivial.
  Qed.

  
End brand_relation_prop.

Lemma brand_relation_ext b pf1 pf2 pf1' pf2' :
  mkBrand_relation b pf1 pf2  = mkBrand_relation b pf1' pf2' .
Proof.
  f_equal; apply UIP_dec; try apply bool_dec;
    try (decide equality; apply string_dec).
Defined.

Lemma brand_relation_fequal {br₁ br₂}:
  @brand_relation_brands br₁ = @brand_relation_brands br₂ ->
  br₁ = br₂.
Proof.
  destruct br₁; destruct br₂; simpl; intros; subst.
  apply brand_relation_ext.
Qed.
  
Section sub_brand.
  
  Definition sub_brand (h:brand_relation_t) (a b:brand)
    := a = b \/ In (a,b) h.
  
  Definition sub_brand_dec br a b : {sub_brand br a b} + {~sub_brand br a b}.
  Proof.
    unfold sub_brand.
    destruct (a == b).
    - left; intuition.
    - destruct (in_dec equiv_dec (a,b) br).
      * left; intuition.
      * right; intuition.
  Defined.
    
  Global Instance sub_brand_refl br : Reflexive (sub_brand br).
  Proof.
    repeat red; intuition.
  Qed.

  Global Instance sub_brand_pre `{brand_relation} : PreOrder (sub_brand brand_relation_brands).
  Proof.
    split; unfold sub_brand;
      repeat red; intuition; subst; intuition.
    - generalize (brand_relation_trans _ _ _ H2 H0); eauto.
  Qed.

  Global Instance sub_brand_part `{brand_relation} : PartialOrder eq (sub_brand brand_relation_brands).
  Proof.
    unfold sub_brand, PartialOrder, relation_equivalence, relation_conjunction,
    predicate_equivalence, predicate_intersection, Basics.flip; simpl.
    intros; split; intros; subst; intuition; subst; trivial.
    eelim brand_relation_assym; eauto.
  Qed.
  
  Lemma sub_brand_in_trans `{brand_relation} {x y z}:
    sub_brand brand_relation_brands x y ->
    In (y, z) brand_relation_brands ->
    In (x, z) brand_relation_brands.
  Proof.
    intros [?|?] ?; subst; trivial.
    eapply brand_relation_trans; eauto.
  Qed.
      
  Lemma in_sub_brand_trans `{brand_relation} {x y z}:
    In (x, y) brand_relation_brands ->
    sub_brand brand_relation_brands y z ->
    In (x, z) brand_relation_brands.
  Proof.
    intros ? [?|?]; subst; trivial.
    eapply brand_relation_trans; eauto.
  Qed.

  (* everything in the second brand list is a 
     parent of (or same as) something in the first brand list *)
  Definition sub_brands (h:brand_relation_t) (a b:brands)
    := forall y, In y b -> exists x, In x a /\ sub_brand h x y.
  
  Definition sub_brands_dec br a b :
    {sub_brands br a b} + {~sub_brands br a b}.
  Proof.
    apply forall_in_dec; intros.
    apply exists_in_dec; intros.
    apply sub_brand_dec.
  Defined.
  
  Global Instance sub_brands_pre `{brand_relation} : PreOrder (sub_brands brand_relation_brands).
  Proof.
    unfold sub_brands.
    constructor; red; intros.
    - exists y; intuition.
    - destruct (H1 _ H2) as [y' [yin ysb]].
      destruct (H0 _ yin) as [z' [zin zsb]].
      exists z'; split.
      + intuition.
      + etransitivity; eauto.
  Qed.

  Lemma incl_sub_brands (hs:brand_relation_t) (a b:brands) :
    incl a b -> sub_brands hs b a.
  Proof.
    unfold incl, sub_brands.
    intros.
    exists y; intuition.
  Qed.

  Definition equiv_brands (h:brand_relation_t) (a b:brands)
    := sub_brands h a b /\ sub_brands h b a.

  Global Instance equiv_brands_sub_subr  (hs:brand_relation_t) :
    subrelation (equiv_brands hs) (sub_brands hs).
  Proof.
    unfold equiv_brands.
    repeat red; intuition.
  Qed.
  
  Global Instance equiv_brands_sub_flip_subr  (hs:brand_relation_t) :
    subrelation (equiv_brands hs) (flip (sub_brands hs)).
  Proof.
    unfold equiv_brands.
    repeat red; intuition.
  Qed.
  
  Definition equiv_brands_dec br a b :
    {equiv_brands br a b} + {~equiv_brands br a b}.
  Proof.
    unfold equiv_brands.
    destruct (sub_brands_dec br a b).
    - destruct (sub_brands_dec br b a).
      + left; intuition.
      + right; intuition.
    - right; intuition.
  Defined.

  Global Instance equiv_brands_equiv `{brand_relation} :
    Equivalence (equiv_brands brand_relation_brands).
  Proof.
    unfold equiv_brands.
    constructor; red; intros.
    - intuition.
    - intuition.
    - intuition; etransitivity; eauto.
  Qed.

  Global Instance equiv_brands_eqdec `{brand_relation} :
    EqDec brands (equiv_brands brand_relation_brands).
  Proof.
    red; intros.
    apply equiv_brands_dec.
  Defined.
  
  Global Instance equivlist_equiv_brands (hs:brand_relation_t)
    : subrelation equivlist (equiv_brands hs).
  Proof.
    repeat red.
    unfold equiv_brands; intros.
    split; apply incl_sub_brands;
      red; intros; eapply equivlist_in; eauto.
    symmetry; eauto.
  Qed.

  Global Instance sub_brands_part `{brand_relation} : PartialOrder (equiv_brands brand_relation_brands) (sub_brands brand_relation_brands).
  Proof.
    unfold PartialOrder, relation_equivalence, predicate_equivalence,
    relation_conjunction, predicate_intersection, Basics.flip; simpl.
    unfold equiv_brands. intuition.
  Qed.

  Global Instance sub_brands_app_proper `{brand_relation} :
    Proper (sub_brands brand_relation_brands ==>
                       sub_brands brand_relation_brands ==>
                       sub_brands brand_relation_brands)
           (@app brand).
  Proof.
    unfold Proper, respectful, equiv_brands; intros.
    unfold sub_brands in *; intros a ain.
    rewrite in_app_iff in ain.
    destruct ain.
    - specialize (H0 _ H2). destruct H0 as [b [bin bhas]].
      exists b. rewrite in_app_iff; intuition.
    - specialize (H1 _ H2). destruct H1 as [b [bin bhas]].
      exists b. rewrite in_app_iff; intuition.
  Qed.
  
  Global Instance equiv_brands_app_proper `{brand_relation} :
    Proper (equiv_brands brand_relation_brands ==>
                         equiv_brands brand_relation_brands ==>
                         equiv_brands brand_relation_brands)
           (@app brand).
  Proof.
    unfold Proper, respectful, equiv_brands; intros.
    intuition; apply sub_brands_app_proper; trivial.
  Qed.
  
  Lemma sub_brands_any hs b : sub_brands hs b any.
  Proof.
    unfold sub_brands; intuition.
  Qed.

  Lemma any_sub_brands hs b : sub_brands hs any b -> b = any.
  Proof.
    unfold sub_brands, any.
    destruct b; trivial; intros.
    destruct (H b); simpl; intuition.
  Qed.

End sub_brand.

Section brand_ops.
    
  Definition parents (hs:brand_relation_t) (a:brand)
    := map snd
           (filter (fun x => if a == (fst x) then true else false) hs).

  Lemma  parents_In (hs:brand_relation_t) (s a:brand) :
    In s (parents hs a) <-> In (a,s) hs.
  Proof.
    unfold parents. split.
    - intros inn.
      apply in_map_iff in inn.
      destruct inn as [[? ?] [? inn]]; simpl in *; subst.
      apply filter_In in inn. destruct inn as [??]; unfold brand in *;
                                match goal with [H: context [match ?x with _ => _ end] |- _] => destruct x end; trivial; unfold equiv, complement in *; simpl in *; congruence.
    - intros inn.
      apply in_map_iff. exists (a, s); simpl; intuition.
      apply filter_In; intuition.
      simpl.
      unfold brand in *;
        match goal with [|- context [match ?x with _ => _ end] ] => destruct x end; trivial; unfold equiv, complement in *; simpl in *; congruence.
  Qed.
  
  Definition parents_and_self (hs:brand_relation_t) (a:brand)
    := a::(parents hs a).

  Lemma parents_and_self_In (hs:brand_relation_t) (s:brand) (a:brand) :
    In s (parents_and_self hs a) <-> sub_brand hs a s.
  Proof.
    unfold parents_and_self, sub_brand.
    simpl; split; intuition; right; apply parents_In; eauto.
  Qed.
    
  Definition explode_brands (hs:brand_relation_t) (a:brands)
    := flat_map (parents_and_self hs) a.
  
  Lemma incl_explode_brands (hs:brand_relation_t) (a:brands) :
    incl a (explode_brands hs a).
  Proof.
    unfold incl, explode_brands.
    intros x inn.
    apply in_flat_map; simpl; eauto.
  Qed.
  
  Lemma sub_explode_brands
        (hs:brand_relation_t) (a:brands) :
    sub_brands hs (explode_brands hs a) a.
  Proof.
    apply incl_sub_brands.
    apply incl_explode_brands.
  Qed.
  
  Lemma explode_brands_sub
        (hs:brand_relation_t) (a:brands) :
    sub_brands hs a (explode_brands hs a).
  Proof.
    unfold sub_brands, explode_brands.
    intros x inn.
    apply in_flat_map in inn.
    destruct inn as [y [inn1 inn2]].
    apply parents_and_self_In in inn2.
    eauto.
  Qed.

  Lemma explode_brands_equivbrands
        (hs:brand_relation_t) (a:brands) :
    equiv_brands hs (explode_brands hs a) a.
  Proof.
    unfold equiv_brands; split.
    - apply sub_explode_brands.
    - apply explode_brands_sub.
  Qed.

  Global Instance explode_brands_proper `{brand_relation} :
    Proper (equiv_brands brand_relation_brands ==> equiv_brands brand_relation_brands) (explode_brands brand_relation_brands).
  Proof.
    unfold Proper, respectful; intros.
    repeat rewrite explode_brands_equivbrands; trivial.
  Qed.

  Lemma explode_brands_proper_inv `{brand_relation} (a b:brands) :
    equiv_brands brand_relation_brands
                 (explode_brands brand_relation_brands a)
                 (explode_brands brand_relation_brands b) ->
    equiv_brands brand_relation_brands
                 a
                 b.
  Proof.
    repeat rewrite explode_brands_equivbrands; trivial.
  Qed.

  (* explode_brands includes everything *)
  Lemma explode_brands_incl hs b a:
    sub_brands hs a b ->
    incl b (explode_brands hs a).
  Proof.
    unfold sub_brands, incl. intros.
    unfold explode_brands.
    apply in_flat_map.
    specialize (H _ H0).
    destruct H as [x [inx subx]].
    exists x; split; trivial.
    apply parents_and_self_In; trivial.
  Qed.

  Global Instance explode_brands_properequiv `{brand_relation} :
    Proper (equiv_brands brand_relation_brands ==> equivlist) (explode_brands brand_relation_brands).
  Proof.
    unfold Proper, respectful; intros.
    apply equivlist_incls.
    destruct H0.
    split; apply explode_brands_incl.
    - rewrite H1. apply explode_brands_sub.
    - rewrite H0. apply explode_brands_sub.
  Qed.
    
  Lemma explode_brands_idempotent `{brand_relation} (a:brands) :
    equivlist
      (explode_brands brand_relation_brands
                      (explode_brands brand_relation_brands a))
      (explode_brands brand_relation_brands a).
  Proof.
    apply equivlist_incls; split.
    - apply explode_brands_incl.
      transitivity (explode_brands brand_relation_brands a);
        apply explode_brands_sub.
    - apply incl_explode_brands.
  Qed.

  Lemma explode_brands_app_incl hs a b :
    incl (explode_brands hs a)
         (explode_brands hs (a++b)).
  Proof.
    unfold explode_brands.
    intros x xin.
    apply in_flat_map in xin.
    apply in_flat_map.
    destruct xin as [y [yin yhas]].
    exists y.
    rewrite in_app_iff.
    intuition.
  Qed.
    
  Definition has_subtype_in (hs:brand_relation_t) (c:brands) (a:brand)
    : bool
    := existsb (fun x => (if in_dec equiv_dec (x,a) hs then true else false)) c.
  
  Definition collapse_brands (hs:brand_relation_t) (c:brands)
    := filter (fun x => negb (has_subtype_in hs c x)) c.

  Lemma collapse_brands_sublist (hs:brand_relation_t) (a:brands) :
    sublist (collapse_brands hs a) a.
  Proof.
    unfold incl, collapse_brands.
    apply filter_sublist.
  Qed.
  
  Lemma collapse_brands_incl (hs:brand_relation_t) (a:brands) :
    incl (collapse_brands hs a) a.
  Proof.
    apply sublist_incl_sub.
    apply collapse_brands_sublist.
  Qed.

  Lemma has_subtype_in_app hs a l1 l2 : 
    has_subtype_in hs (l1 ++ l2) a =
    has_subtype_in hs l1 a ||
                   has_subtype_in hs l2 a.
  Proof.
    unfold has_subtype_in.
    apply existsb_app.
  Qed.

  Lemma nosub_collapse_brands hs a : 
    (forall x y : brand, In x a -> In y a -> ~ In (x, y) hs) ->
    collapse_brands hs a = a.
  Proof.
    intros. unfold collapse_brands.
    apply true_filter.
    unfold has_subtype_in; intros.
    rewrite negb_true_iff, existsb_not_forallb, negb_false_iff, forallb_forall.
    intros. match_destr.
    elim (H _ _ H1 H0 i).
  Qed.

  Lemma collapse_brands_nosub hs a : 
    collapse_brands hs a = a ->
    (forall x y : brand, In x a -> In y a -> ~ In (x, y) hs).
  Proof.
    unfold collapse_brands; intros.
    generalize (filter_id_implies_pred _ _ H _ H1); intros fall.
    unfold has_subtype_in in fall.
    rewrite negb_true_iff, existsb_not_forallb, negb_false_iff, forallb_forall in fall.
    specialize (fall _ H0).
    match_destr_in fall.
  Qed.

  Lemma has_subtype_in_single hs a b :
    has_subtype_in hs (a::nil) b = if in_dec equiv_dec (a,b) hs then true else false.
  Proof.
    simpl.
    rewrite orb_comm; simpl; trivial.
  Qed.

  Lemma has_subtype_in_not_self `{brand_relation} a : 
    has_subtype_in brand_relation_brands (a :: nil) a = false.
  Proof.
    rewrite has_subtype_in_single.
    match_destr.
    apply brand_relation_irrefl in i.
    intuition.
  Qed.

  Lemma collapse_brands_singleton {br:brand_relation} (bb:brand)
    : collapse_brands brand_relation_brands (singleton bb) = singleton bb.
  Proof.
    unfold collapse_brands.
    unfold singleton.
    rewrite true_filter; trivial.
    simpl; intuition.
    match_destr.
    subst.
    apply brand_relation_irrefl in i.
    intuition.
  Qed.
  
  Lemma has_subtype_in_cons_self `{brand_relation} a l : 
    has_subtype_in brand_relation_brands (a :: l) a =
    has_subtype_in brand_relation_brands l a.
  Proof.
    replace (a::l) with ((a::nil)++l) by reflexivity.
    rewrite has_subtype_in_app, has_subtype_in_not_self.
    simpl; trivial.
  Qed.
    
  Lemma has_subtype_in_least `{brand_relation} {x:brand} {a:brands} :
    In x a ->
    {y:brand | 
     In y a
     /\ sub_brand brand_relation_brands y x
     /\ has_subtype_in brand_relation_brands a y = false}.
  Proof.
    revert x.
    induction a; simpl; intuition.
    destruct (in_dec string_dec x a0).
    - destruct (IHa _ i) as [y [iny [subyx nsuby]]].
      case_eq (@in_dec (prod string brand)
                       (@equiv_dec (prod string brand)
                                   (@eq (prod string brand))
                                   (@eq_equivalence (prod string brand))
                                   (@pair_eqdec string brand (@eq_equivalence string)
                                                string_eqdec (@eq_equivalence string) string_eqdec))
                       (@pair string brand a y) (@brand_relation_brands H)); intros.
      + exists a.
        split; [intuition | ].
        split.
        * generalize (in_sub_brand_trans i0 subyx); right; trivial.
        * { match_destr.
            - elim (brand_relation_irrefl _ i1).
            - simpl. unfold has_subtype_in.
              rewrite existsb_not_forallb, negb_false_iff, forallb_forall.
              intros. match_destr.
              unfold has_subtype_in in nsuby.
              rewrite existsb_not_forallb, negb_false_iff, forallb_forall in nsuby.
              specialize (nsuby x0 H2).
              match_destr_in nsuby.
              generalize (in_sub_brand_trans i0 subyx).
              elim n0. eapply brand_relation_trans; eauto.
          }
      + exists y. rewrite nsuby, H1. intuition.
    - destruct (string_dec a x).
      + subst.
        case_eq (has_subtype_in brand_relation_brands a0 x); intros.
        * unfold has_subtype_in in H1. apply existsb_ex in H1.
          destruct H1 as [y [iny suby]].
          match_destr_in suby.
          destruct (IHa _ iny) as [z [inz [subz nsubz]]].
          exists z. rewrite nsubz.
          { intuition.
            - rewrite subz; right; trivial.
            - match_destr.
              generalize (sub_brand_in_trans subz i); intros.
              elim (brand_relation_assym _ _ i0); trivial.
          }
        * exists x. rewrite H1.
          intuition. match_destr.
          elim (brand_relation_irrefl _ i).
      + elim n0. destruct H0; intuition.
  Qed.

  Lemma sub_collapse_brands `{brand_relation} (a:brands) :
    sub_brands brand_relation_brands
               (collapse_brands brand_relation_brands a)
               a.
  Proof.
    unfold sub_brands, collapse_brands.
    intros.
    destruct (has_subtype_in_least H0) as [x [innx [subx nsubx]]].
    exists x.
    split; trivial.
    apply filter_In.
    split; trivial.
    rewrite nsubx.
    trivial.
  Qed.
    
  Lemma collapse_brands_sub
        (hs:brand_relation_t) (a:brands) :
    sub_brands hs a (collapse_brands hs a).
  Proof.
    apply incl_sub_brands.
    apply collapse_brands_incl.
  Qed.

  Lemma collapse_brands_equivbrands
        `{brand_relation} (a:brands) :
    equiv_brands brand_relation_brands
                 (collapse_brands brand_relation_brands a)
                 a.
  Proof.
    unfold equiv_brands; split.
    - apply sub_collapse_brands.
    - apply collapse_brands_sub.
  Qed.

  (* collapse_brands collapses *)
  Lemma collapse_collapses `{brand_relation} (a:brands) :
    forall x y,
      In x a ->
      In y (collapse_brands brand_relation_brands a) ->
      ~ In (x,y) brand_relation_brands.
  Proof.
    unfold collapse_brands, has_subtype_in. intros.
    apply filter_In in H1.
    destruct H1 as [iny nhasy].
    rewrite negb_true_iff, existsb_not_forallb, negb_false_iff, forallb_forall in nhasy.
    specialize (nhasy _ H0).
    match_destr_in nhasy.
  Qed.
  
  Global Instance collapse_brands_proper `{brand_relation} :
    Proper (equiv_brands brand_relation_brands ==> equiv_brands brand_relation_brands) (collapse_brands brand_relation_brands).
  Proof.
    unfold Proper, respectful; intros.
    repeat rewrite collapse_brands_equivbrands; trivial.
  Qed.

  Lemma collapse_brands_proper_inv `{brand_relation} (a b:brands) :
    equiv_brands brand_relation_brands
                 (collapse_brands brand_relation_brands a)
                 (collapse_brands brand_relation_brands b) ->
    equiv_brands brand_relation_brands
                 a
                 b.
  Proof.
    repeat rewrite collapse_brands_equivbrands; trivial.
  Qed.

  Lemma existsb_app {A} (f:A->bool) l1 l2 :
    existsb f (l1 ++ l2) = existsb f l1 || existsb f l2.
  Proof.
    induction l1; simpl; trivial.
    rewrite IHl1.
    rewrite orb_assoc; trivial.
  Qed.
    
  Lemma collapse_brands_idempotent `{brand_relation} (a:brands) :
    collapse_brands brand_relation_brands (collapse_brands brand_relation_brands a) = collapse_brands brand_relation_brands a.
  Proof.
    unfold collapse_brands.
    apply true_filter; intros x inn.
    apply filter_In in inn.
    destruct inn as [inn hasin].
    unfold has_subtype_in in *.
    rewrite negb_true_iff, existsb_not_forallb, negb_false_iff, forallb_forall in hasin.
    rewrite negb_true_iff, existsb_not_forallb, negb_false_iff, forallb_forall.
    intros y iny.
    apply filter_In in iny.
    destruct iny as [iny exy].
    rewrite negb_true_iff, existsb_not_forallb, negb_false_iff, forallb_forall in exy.
    specialize (hasin _ iny).
    match_destr.
  Qed.

  Lemma sort_brands_equiv hs a :
    equiv_brands hs (insertion_sort StringOrder.lt_dec a) a.
  Proof.
    apply equivlist_equiv_brands.
    apply insertion_sort_trich_equiv.
    apply StringOrder.trichotemy.
  Qed.    
  
  Definition canon_brands (hs:brand_relation_t) (a:brands)
    := insertion_sort StringOrder.lt_dec (collapse_brands hs a).

  Lemma canon_brands_singleton {br:brand_relation} (bb:brand)
    : canon_brands brand_relation_brands (singleton bb) = singleton bb.
  Proof.
    unfold canon_brands.
    rewrite collapse_brands_singleton.
    reflexivity.
  Qed.
  
  Lemma canon_brands_equiv `{brand_relation} (a:brands)
    : equiv_brands
        brand_relation_brands
        (canon_brands brand_relation_brands a)
        a.
  Proof.
    unfold canon_brands.
    rewrite sort_brands_equiv.
    apply collapse_brands_equivbrands.
  Qed.

  Global Instance has_subtype_in_proper_equivlist :
    Proper (eq ==> equivlist ==> eq ==> eq) has_subtype_in.
  Proof.
    unfold Proper, respectful; intros; subst.
    unfold has_subtype_in.
    match goal with
      [|- ?x = ?y ] => case_eq y
    end; intros eqq1.
    - rewrite existsb_exists in eqq1 |- *.
      destruct eqq1 as [x [? inn]].
      exists x; split; trivial.
      rewrite H0; trivial.      
    - rewrite existsb_not_forallb, negb_false_iff, forallb_forall in eqq1 |- *.
      intros x xinn.
      rewrite H0 in xinn.
      eauto.
  Qed.
  
  Lemma collapse_sort_brands_commute (hs:brand_relation_t) (a:brands)
    : insertion_sort StringOrder.lt_dec (collapse_brands hs a)
      = collapse_brands hs (insertion_sort StringOrder.lt_dec a).
  Proof.
    unfold collapse_brands.
    rewrite sort_filter_commute.
    - f_equal. apply filter_eq; intros.
      rewrite insertion_sort_trich_equiv; trivial.
      apply StringOrder.trichotemy.
    - eapply StringOrder.lt_strorder.
    - apply StringOrder.trichotemy.
  Qed.

  Lemma canon_brands_incl (hs:brand_relation_t) (a:brands) :
    incl (canon_brands hs a) a.
  Proof.
    unfold canon_brands.
    intros ? xin.
    apply in_insertion_sort in xin.
    revert a0 xin.
    apply sublist_incl_sub.
    apply collapse_brands_sublist.
  Qed.

  Definition is_canon_brands (hs:brand_relation_t) (a:brands)
    := is_list_sorted StringOrder.lt_dec a = true
       /\ (forall x y, In x a -> In y a -> ~ In (x,y) hs).

  Lemma canon_brands_is_canon_brands (hs:brand_relation_t) (a:brands) :
    is_canon_brands hs (canon_brands hs a).
  Proof.
    unfold canon_brands, is_canon_brands. split.
    - apply is_list_sorted_Sorted_iff. apply insertion_sort_Sorted.
    - repeat rewrite collapse_sort_brands_commute.
      intros.
      unfold collapse_brands in H, H0.
      apply filter_In in H.
      apply filter_In in H0.
      destruct H as [xin xhas].
      destruct H0 as [yin yhas].
      unfold has_subtype_in in yhas.
      rewrite negb_true_iff, existsb_not_forallb, negb_false_iff, forallb_forall in yhas.
      specialize (yhas _ xin).
      match_destr_in yhas.
  Qed.

  Lemma is_canon_brands_canon_brands hs a :
    is_canon_brands hs a -> canon_brands hs a = a.
  Proof.
    unfold canon_brands, is_canon_brands. intros [issort nin].
    rewrite collapse_sort_brands_commute.
    rewrite insertion_sort_sorted_is_id; trivial.
    apply nosub_collapse_brands; trivial.
  Qed.
  
  Lemma canon_brands_idempotent (hs:brand_relation_t) (a:brands) :
    canon_brands hs (canon_brands hs a)
    = canon_brands hs a.
  Proof.
    apply is_canon_brands_canon_brands.
    apply canon_brands_is_canon_brands.
  Qed.

  Lemma is_canon_brands_dec (hs:brand_relation_t) (a:brands) :
    {is_canon_brands hs a} + {~ is_canon_brands hs a}.
  Proof.
    case_eq (list_eqdec string_dec (canon_brands hs a) a).
    - left. unfold equiv in *.
      rewrite <- e.  apply canon_brands_is_canon_brands.
    - right. unfold equiv, complement in *.
      intro can.
      apply is_canon_brands_canon_brands in can.
      congruence.
  Defined.

  Lemma is_canon_brands_singleton {br:brand_relation} (bb:brand)
    : is_canon_brands brand_relation_brands (singleton bb).
  Proof.
    rewrite <- canon_brands_singleton.
    apply canon_brands_is_canon_brands.
  Qed.

  (* two brands are equivalent if and only if there canonicalizations 
     are equal.  *)
  Lemma canon_equiv `{brand_relation} (a b:brands) :
    equiv_brands brand_relation_brands a b
    <->
    canon_brands brand_relation_brands a = canon_brands brand_relation_brands b.
  Proof.
    split; intros.
    - apply insertion_sort_equivlist; [apply lt_contr1 | ].
      revert a b H0.
      cut (forall a b : brands,
              equiv_brands brand_relation_brands a b ->
              incl (collapse_brands brand_relation_brands a)
                   (collapse_brands brand_relation_brands b)).
      { intros. apply equivlist_incls; intuition. }
      unfold equiv_brands, sub_brands.
      unfold canon_brands.
      intros a b [Hb Ha].
      unfold collapse_brands.
      intros x innx.
      apply filter_In in innx.
      apply filter_In.
      destruct innx as [innx hasx].
      specialize (Ha _ innx).
      destruct Ha as [y [iny suby]].
      unfold has_subtype_in in hasx.
      rewrite negb_true_iff, existsb_not_forallb, negb_false_iff, forallb_forall in hasx.
      destruct suby.
      + subst.
        split; trivial.
        unfold has_subtype_in.
        rewrite negb_true_iff, existsb_not_forallb, negb_false_iff, forallb_forall.
        intros.
        match_destr.
        specialize (Hb _ H0).
        destruct Hb as [z [inz subz]].
        unfold has_subtype_in in hasx.
        specialize (hasx _ inz).
        match_destr_in hasx.
        generalize (sub_brand_in_trans subz i); intuition.
      + specialize (Hb _ iny).
        destruct Hb as [z [inz subz]].
        specialize (hasx _ inz).
        match_destr_in hasx.
        generalize (sub_brand_in_trans subz H0); intuition.
    - unfold equiv_brands.
      revert a b H0.
      cut (forall a b : brands,
              canon_brands brand_relation_brands a =
              canon_brands brand_relation_brands b ->
              sub_brands brand_relation_brands a b).
      { intuition. }
      intros a b eqq.
      unfold sub_brands; intros.
      unfold canon_brands in eqq.
      assert (eqq1: equivlist (insertion_sort StringOrder.lt_dec
                                              (collapse_brands brand_relation_brands a))
                              (insertion_sort StringOrder.lt_dec
                                              (collapse_brands brand_relation_brands b)))
        by (rewrite eqq; reflexivity).
      repeat rewrite -> insertion_sort_trich_equiv in eqq1 by (apply StringOrder.trichotemy).
      apply equivlist_incls in eqq1.
      destruct eqq1 as [eqqab eqqba].
      destruct (has_subtype_in_least H0) as [x [xin [subx hasx]]].
      assert (xin2:In x (collapse_brands brand_relation_brands b)).
      + unfold collapse_brands.
        apply filter_In. split; trivial.
        rewrite hasx; trivial.
      + specialize (eqqba _ xin2).
        unfold collapse_brands in eqqba.
        apply filter_In in eqqba.
        exists x; intuition.
  Qed.

  Global Instance canon_proper `{brand_relation} :
    Proper (equiv_brands brand_relation_brands ==> eq) (canon_brands brand_relation_brands).
  Proof.
    unfold Proper, respectful; intros.
    apply canon_equiv; trivial.
  Qed.
  
  Lemma canon_equiv_is_canon_brands `{brand_relation} (a b:brands) :
    is_canon_brands brand_relation_brands b ->
    (equiv_brands brand_relation_brands a b
     <->
     canon_brands brand_relation_brands a = b).
  Proof.
    intros can.
    rewrite <- (is_canon_brands_canon_brands _ _ can).
    rewrite canon_equiv.
    repeat rewrite (is_canon_brands_canon_brands _ _ can).
    reflexivity.
  Qed.
    
  (* canonicalization gives rise to a different decision procedure
     for brand equivalence: canonicalize and compare *)
  Definition equiv_brands_dec_alt `{brand_relation} a b :
    {equiv_brands brand_relation_brands a b}
    + {~equiv_brands brand_relation_brands a b}.
  Proof.
    destruct (list_eqdec string_dec
                         (canon_brands brand_relation_brands a)
                         (canon_brands brand_relation_brands b)).
    - left. rewrite canon_equiv; trivial.
    - right. rewrite canon_equiv; trivial.
  Defined.
  
  Lemma explode_canon_explode `{brand_relation} a :
    equivlist (explode_brands brand_relation_brands
                              (canon_brands brand_relation_brands a))
              (explode_brands brand_relation_brands a).
  Proof.
    rewrite canon_brands_equiv.
    reflexivity.
  Qed.

  Lemma canon_brands_canon_brands_app1 `{brand_relation} a b :
    canon_brands brand_relation_brands
                 (canon_brands brand_relation_brands a ++ b) =
    canon_brands brand_relation_brands (a ++ b).
  Proof.
    apply canon_equiv.
    rewrite canon_brands_equiv.
    reflexivity.
  Qed.

End brand_ops.

Section brand_join.
  Definition brand_join (hs:brand_relation_t) (a b:brands)
    := canon_brands hs
                    (set_inter string_dec
                               (explode_brands hs a)
                               (explode_brands hs b)).

  Lemma brand_join_is_canon hs a b :
    is_canon_brands hs (brand_join hs a b).
  Proof.
    unfold brand_join.
    apply canon_brands_is_canon_brands.
  Qed.

  Lemma brand_join_canon_l `{brand_relation} a b :
    brand_join brand_relation_brands (canon_brands brand_relation_brands a) b
    = brand_join brand_relation_brands a b.
  Proof.
    unfold brand_join.
    rewrite explode_canon_explode; trivial.
  Qed.

  Lemma brand_join_canon_r `{brand_relation} a b :
    brand_join brand_relation_brands a (canon_brands brand_relation_brands b)
    = brand_join brand_relation_brands a b.
  Proof.
    unfold brand_join.
    rewrite explode_canon_explode; trivial.
  Qed.

  Theorem brand_join_idempotent `{brand_relation} a :
    brand_join brand_relation_brands a a
    = canon_brands brand_relation_brands a.
  Proof.
    unfold brand_join.
    rewrite set_inter_idempotent.
    rewrite explode_brands_equivbrands.
    trivial.
  Qed.

  Lemma brand_join_idempotent_can `{brand_relation} a :
    is_canon_brands brand_relation_brands a ->
    brand_join brand_relation_brands a a = a.
  Proof.
    intros.
    rewrite brand_join_idempotent; trivial.
    apply is_canon_brands_canon_brands; trivial.
  Qed.

  Theorem brand_join_commutative hs a b :
    brand_join hs a b = brand_join hs b a.
  Proof.
    unfold brand_join.
    unfold canon_brands.
    repeat rewrite collapse_sort_brands_commute.
    f_equal.
    apply insertion_sort_equivlist; [apply lt_contr1 | ].
    apply set_inter_equivlist.
  Qed.

  Lemma set_inter_preserves_explode_brands `{brand_relation} a b:
    equivlist
      (explode_brands brand_relation_brands
                      (set_inter string_dec
                                 (explode_brands brand_relation_brands a)
                                 (explode_brands brand_relation_brands b)))
      (set_inter string_dec
                 (explode_brands brand_relation_brands a)
                 (explode_brands brand_relation_brands b)).
  Proof.
    apply equivlist_incls; split.
    - intros x xin.
      unfold explode_brands in *.
      apply in_flat_map in xin.
      destruct xin as [y [iny inpar]].
      apply set_inter_elim in iny.
      destruct iny as [inya inyb].
      apply in_flat_map in inya.
      apply in_flat_map in inyb.
      destruct inya as [a2 [ina2 inpa2]].
      destruct inyb as [b2 [inb2 inpb2]].
      apply set_inter_intro.
      + apply in_flat_map.
        exists a2; split; trivial.
        rewrite parents_and_self_In in *.
        etransitivity; eauto.
      + apply in_flat_map.
        exists b2; split; trivial.
        rewrite parents_and_self_In in *.
        etransitivity; eauto.        
    - apply incl_explode_brands.
  Qed.

  Theorem brand_join_associative`{brand_relation} a b c:
    brand_join brand_relation_brands
               (brand_join brand_relation_brands a b)
               c
    = brand_join brand_relation_brands a
                 (brand_join brand_relation_brands b c).
  Proof.
    unfold brand_join.
    repeat rewrite explode_canon_explode.
    repeat rewrite set_inter_preserves_explode_brands.
    rewrite set_inter_assoc.
    reflexivity.
  Qed.

  Lemma brand_join_consistent1 `{brand_relation} b b2 :
    sub_brands brand_relation_brands b b2 ->
    brand_join brand_relation_brands b b2 =
    (canon_brands brand_relation_brands b2).
  Proof.
    unfold sub_brands, brand_join.
    intros sub. 
    apply canon_equiv.
    red; split; intros x inx.
    - specialize (sub x inx).
      destruct sub as [y [iny suby]].
      exists x.
      split; try reflexivity.
      apply set_inter_intro.
      + apply in_flat_map.
        exists y; split; trivial.
        apply parents_and_self_In; trivial.
      + apply incl_explode_brands; trivial.
    - apply set_inter_elim in inx. destruct inx as [inb inb2].
      unfold explode_brands in inb2.
      apply in_flat_map in inb2.
      destruct inb2 as [xb2 [inxb2 subxb2]].
      apply parents_and_self_In in subxb2.
      eauto.
  Qed.
    
  Lemma brand_join_consistent2 `{brand_relation} b b2 :
    brand_join brand_relation_brands b b2
    = canon_brands brand_relation_brands b2
    -> sub_brands brand_relation_brands b b2.
  Proof.
    unfold brand_join, sub_brands.
    intros eqq y iny.
    apply canon_equiv in eqq.
    destruct eqq as [sub1 sub2].
    unfold sub_brands in *.
    specialize (sub1 _ iny).
    destruct sub1 as [x [inx subx]].
    apply set_inter_elim in inx.
    destruct inx as [inx1 inx2].
    unfold explode_brands in inx1.
    apply in_flat_map in inx1.
    destruct inx1 as [z [inz subz]].
    apply parents_and_self_In in subz.
    rewrite subx in subz.
    eauto.
  Qed.

  Theorem brand_join_consistent `{brand_relation} b b2 :
    sub_brands brand_relation_brands b b2 <->
    brand_join brand_relation_brands b b2
    = canon_brands brand_relation_brands b2.
  Proof.
    split.
    - apply brand_join_consistent1.
    - apply brand_join_consistent2.
  Qed.
  
  Lemma brand_join_consistent_can `{brand_relation} b b2 :
    is_canon_brands brand_relation_brands b2 ->
    (sub_brands brand_relation_brands b b2 <->
     brand_join brand_relation_brands b b2 = b2).
  Proof.
    intros.
    rewrite brand_join_consistent; trivial.
    rewrite is_canon_brands_canon_brands; trivial.
    reflexivity.
  Qed.

End brand_join.

Section brand_meet.

  Definition brand_meet (hs:brand_relation_t) (a b:brands)
    := canon_brands hs (a ++ b).

  Lemma brand_meet_is_canon hs a b :
    is_canon_brands hs (brand_meet hs a b).
  Proof.
    unfold brand_meet.
    apply canon_brands_is_canon_brands.
  Qed.

  Lemma brand_meet_canon_l `{brand_relation} a b :
    brand_meet brand_relation_brands (canon_brands brand_relation_brands a) b
    = brand_meet brand_relation_brands a b.
  Proof.
    unfold brand_meet.
    rewrite canon_brands_canon_brands_app1; trivial.
  Qed.

  Lemma brand_meet_canon_r `{brand_relation} a b :
    brand_meet brand_relation_brands a (canon_brands brand_relation_brands b)
    = brand_meet brand_relation_brands a b.
  Proof.
    unfold brand_meet.
    rewrite app_commutative_equivlist.
    rewrite canon_brands_canon_brands_app1.
    rewrite app_commutative_equivlist; trivial.
  Qed.
  
  Theorem brand_meet_idempotent `{brand_relation} a :
    brand_meet brand_relation_brands a a
    = canon_brands brand_relation_brands a.
  Proof.
    unfold brand_meet.
    intros.
    rewrite app_idempotent_equivlist.
    reflexivity.
  Qed.

  Lemma brand_meet_idempotent_can `{brand_relation} a :
    is_canon_brands brand_relation_brands a ->
    brand_meet brand_relation_brands a a = a.
  Proof.
    intros.
    rewrite brand_meet_idempotent; trivial.
    apply is_canon_brands_canon_brands; trivial.
  Qed.
  
  Theorem brand_meet_commutative `{brand_relation}  a b :
    brand_meet brand_relation_brands a b = brand_meet brand_relation_brands b a.
  Proof.
    unfold brand_meet.
    rewrite app_commutative_equivlist.
    trivial.
  Qed.

  Theorem brand_meet_associative`{brand_relation} a b c:
    brand_meet brand_relation_brands
               (brand_meet brand_relation_brands a b)
               c
    = brand_meet brand_relation_brands a
                 (brand_meet brand_relation_brands b c).
  Proof.
    unfold brand_meet.                  
    rewrite (app_commutative_equivlist a (canon_brands brand_relation_brands (b ++ c))).
    repeat rewrite canon_brands_canon_brands_app1.
    rewrite (app_commutative_equivlist (b++c) a).
    rewrite app_ass.
    reflexivity.
  Qed.
  
  Lemma brand_meet_consistent1 `{brand_relation} b b2 :
    sub_brands brand_relation_brands b b2 ->
    brand_meet brand_relation_brands b b2 =
    (canon_brands brand_relation_brands b).
  Proof.
    unfold sub_brands, brand_meet.
    intros sub. 
    apply canon_equiv.
    red; split; intros x inx.
    - exists x; rewrite in_app_iff; intuition.
    - apply in_app_iff in inx. destruct inx as [inx|inx].
      + exists x; intuition.
      + eauto. 
  Qed.
    
  Lemma brand_meet_consistent2 `{brand_relation} b b2 :
    brand_meet brand_relation_brands b b2
    = canon_brands brand_relation_brands b
    -> sub_brands brand_relation_brands b b2.
  Proof.
    unfold brand_meet, sub_brands.
    intros eqq y iny.
    apply canon_equiv in eqq.
    destruct eqq as [sub1 sub2].
    unfold sub_brands in *.
    destruct (sub2 y).
    - rewrite in_app_iff; intuition.
    - eauto.
  Qed.

  Theorem brand_meet_consistent `{brand_relation} b b2 :
    sub_brands brand_relation_brands b b2 <->
    brand_meet brand_relation_brands b b2
    = canon_brands brand_relation_brands b.
  Proof.
    split.
    - apply brand_meet_consistent1.
    - apply brand_meet_consistent2.
  Qed.
  
  Lemma brand_meet_consistent_can `{brand_relation} b b2 :
    is_canon_brands brand_relation_brands b ->
    (sub_brands brand_relation_brands b b2 <->
     brand_meet brand_relation_brands b b2 = b).
  Proof.
    intros.
    rewrite brand_meet_consistent; trivial.
    rewrite is_canon_brands_canon_brands; trivial.
    reflexivity.
  Qed.
  
End brand_meet.

Section meet_join.

  Theorem brand_join_absorptive `{brand_relation} a b:
    brand_join brand_relation_brands
               a
               (brand_meet brand_relation_brands a b)
    = canon_brands brand_relation_brands a.
  Proof.
    unfold brand_join, brand_meet.
    rewrite explode_canon_explode.
    rewrite set_inter_contained.
    rewrite explode_brands_equivbrands; trivial.
    intros.
    apply explode_brands_app_incl; trivial.
  Qed.
  
  Lemma brand_join_absorptive_can `{brand_relation} a b:
    is_canon_brands brand_relation_brands a ->
    brand_join brand_relation_brands
               a
               (brand_meet brand_relation_brands a b)
    = a.
  Proof.
    intros; rewrite brand_join_absorptive, is_canon_brands_canon_brands; trivial.
  Qed.
  
  Theorem brand_meet_absorptive `{brand_relation} a b:
    brand_meet brand_relation_brands
               a
               (brand_join brand_relation_brands a b)
    = canon_brands brand_relation_brands a.
  Proof.
    unfold brand_join, brand_meet.
    replace (canon_brands brand_relation_brands
                          (a ++
                             canon_brands brand_relation_brands
                             (set_inter string_dec (explode_brands brand_relation_brands a)
                                        (explode_brands brand_relation_brands b))))
      with (canon_brands brand_relation_brands
                         (explode_brands brand_relation_brands a ++
                                         canon_brands brand_relation_brands
                                         (set_inter string_dec (explode_brands brand_relation_brands a)
                                                    (explode_brands brand_relation_brands b)))).
    - rewrite app_contained_equivlist; trivial.
      { rewrite explode_brands_equivbrands; reflexivity. }
      intros x xin.
      apply canon_brands_incl in xin.
      apply set_inter_elim in xin.
      intuition.
    - apply canon_equiv.
      apply equiv_brands_app_proper.
      + apply explode_brands_equivbrands.
      + reflexivity.
  Qed.

  Lemma brand_meet_absorptive_can `{brand_relation} a b:
    is_canon_brands brand_relation_brands a ->
    brand_meet brand_relation_brands
               a
               (brand_join brand_relation_brands a b)
    = a.
  Proof.
    intros; rewrite brand_meet_absorptive, is_canon_brands_canon_brands; trivial.
  Qed.
  
End meet_join.

Section brands_lattice.

  Context {br:brand_relation}.
  
  Global Instance brands_lattice : Lattice brands (equiv_brands brand_relation_brands)
    := { meet:=brand_meet brand_relation_brands;
         join:=brand_join brand_relation_brands
       }.
  Proof.
    - unfold Proper, respectful.
      unfold brand_meet; intros.
      rewrite H, H0.
      reflexivity.
    - unfold Proper, respectful.
      unfold brand_join; intros.
      rewrite H, H0.
      reflexivity.
    - red; intros. rewrite brand_meet_commutative; reflexivity.
    - red; intros. rewrite brand_meet_associative; reflexivity.
    - red; intros. rewrite brand_meet_idempotent.
      rewrite canon_brands_equiv.
      reflexivity.
    - red; intros. rewrite brand_join_commutative; reflexivity.
    - red; intros. rewrite brand_join_associative; reflexivity.
    - red; intros. rewrite brand_join_idempotent.
      rewrite canon_brands_equiv; reflexivity.
    - red; intros. rewrite brand_meet_absorptive.
      rewrite canon_brands_equiv; reflexivity.
    - red; intros. rewrite brand_join_absorptive.
      rewrite canon_brands_equiv; reflexivity.
  Defined.
    
  Global Instance brands_olattice :
    OLattice (equiv_brands brand_relation_brands) (sub_brands brand_relation_brands).
  Proof.
    constructor; intros.
    unfold part_le; simpl.
    rewrite brand_meet_consistent.
    split; intros eqq.
    - rewrite eqq.
      rewrite canon_brands_equiv; reflexivity.
    - transitivity (canon_brands brand_relation_brands
                                 (brand_meet brand_relation_brands a b)).
      + rewrite is_canon_brands_canon_brands; trivial.
        apply brand_meet_is_canon.
      + apply canon_equiv. apply eqq.
  Defined.
  
End brands_lattice.
  
Global Instance brand_relation_eqdec : EqDec brand_relation eq.
Proof.
  red; unfold equiv, complement.
  intros x y.
  destruct (@brand_relation_brands x == @brand_relation_brands y).
  - left.
    apply brand_relation_fequal; trivial.
  - right. intros; subst.
    apply c. reflexivity.
Defined.
   
Hint Resolve canon_brands_is_canon_brands.
  
