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

Require Import Bool.
Require Import String.
Require Import List.
Require Import Eqdep_dec.
Require Import RelationClasses.
Require Import Utils.
Require Import ForeignType.
Require Import RType.
Require Import BrandRelation.

Section RSubtype.

  Context {ftype:foreign_type}.
  Context {br:brand_relation}.
  
Inductive subtype : rtype -> rtype -> Prop :=
  | STop r : subtype r ⊤
  | SBottom r : subtype ⊥ r
  | SRefl r : subtype r r
  | SColl r1 r2 : subtype r1 r2 -> subtype (Coll r1) (Coll r2)
  (** Allow width subtyping of open records and depth subtyping of both types of records. Also, a closed record can be a subtype of an open record (but not vice versa) *)
  | SRec k1 k2 rl1 rl2 pf1 pf2 : (forall s r',
                      lookup string_dec rl2 s = Some r' -> 
                      exists r, lookup string_dec rl1 s = Some r /\
                                subtype r r') ->
                                (k2 = Closed -> k1 = Closed /\ 
                                 (forall s, In s (domain rl1) -> In s (domain rl2))) ->
                                subtype (Rec k1 rl1 pf1) (Rec k2 rl2 pf2)
  | SEither l1 l2 r1 r2 :
      subtype l1 l2 ->
      subtype r1 r2 ->
      subtype (Either l1 r1) (Either l2 r2)
  | SArrow in1 in2 out1 out2:
      subtype in2 in1 ->
      subtype out1 out2 ->
      subtype (Arrow in1 out1) (Arrow in2 out2)
  | SBrand b1 b2 : sub_brands brand_relation_brands b1 b2 -> subtype (Brand b1) (Brand b2)
  | SForeign ft1 ft2 :
      foreign_type_sub ft1 ft2 ->
      subtype (Foreign ft1) (Foreign ft2)
.

Lemma SRec_open k1 rl1 rl2 pf1 pf2 :
  (forall s r',
     lookup string_dec rl2 s = Some r' -> 
     exists r, lookup string_dec rl1 s = Some r /\
               subtype r r') ->
  subtype (Rec k1 rl1 pf1) (Rec Open rl2 pf2).
Proof.
  intros; constructor; intuition; discriminate.
Qed.

Lemma SRec_closed_in_domain {k1 k2 rl1 rl2 pf1 pf2} :
  subtype (Rec k1 rl1 pf1) (Rec k2 rl2 pf2) ->
  (forall x, In x (domain rl2) -> In x (domain rl1)).
Proof.
  inversion 1; rtype_equalizer; subst; intuition.
  destruct (in_dom_lookup string_dec H0).
  destruct (H3 _ _ H1) as [? [inn ?]].
  apply lookup_in in inn.
  apply in_dom in inn.
  trivial.
Qed.

Lemma SRec_closed_equiv_domain {k1 rl1 rl2 pf1 pf2} :
  subtype (Rec k1 rl1 pf1) (Rec Closed rl2 pf2) ->
  (forall x, In x (domain rl1) <-> In x (domain rl2)).
Proof.
  inversion 1; rtype_equalizer; subst; intuition.
  eapply SRec_closed_in_domain; eauto.
Qed.

  Lemma UIP_refl_dec 
        {A:Type}
        (dec:forall x y:A, {x = y} + {x <> y}) 
        {x:A} 
        (p1:x = x) : p1 = eq_refl x.
  Proof.
    intros. apply (UIP_dec); auto.
  Qed.

  (** This follows trivially from the consistency of join and subtype.
      However, this version should have better computational properties.*)

  Lemma subtype_both_dec x y :
    (prod ({subtype x y} + {~ subtype x y}) ({subtype y x} + {~ subtype y x})).
  Proof.
    Ltac simp := match goal with
            | [H:(@eq bool ?x ?x) |- _ ] => generalize (UIP_refl_dec bool_dec H); intro; subst H
          end.
    destruct x.
    Hint Constructors subtype.
    revert y; induction x
    ; intros y; destruct y as [y pfy]; destruct y; constructor;
    try solve[right; inversion 1 | left; simpl in *; repeat simp; eauto ].
    - destruct (IHx e (exist _ y pfy)) as [[?|?]_].
      + left. repeat rewrite (Coll_canon).
        auto.
      + right. intro ss; apply n. inversion ss; subst.
         * erewrite (rtype_ext); eauto.
         * destruct r1; destruct r2; simpl in *.
           erewrite (rtype_ext e); erewrite (rtype_ext pfy); eauto.
    - destruct (IHx e (exist _ y pfy)) as [_[?|?]].
      + left. repeat rewrite (Coll_canon).
        auto.
      + right. intro ss; apply n. inversion ss; subst.
         * erewrite (rtype_ext); eauto.
         * destruct r1; destruct r2; simpl in *.
           erewrite (rtype_ext e); erewrite (rtype_ext pfy); eauto.
    - rename srl into srl0; rename r into srl.
      assert (sub:{forall s r' pf',
      lookup string_dec srl0 s = Some r' -> 
      exists r pf, lookup string_dec srl s = Some r /\
                subtype (exist _ r pf) (exist _ r' pf')} + {~ (forall s r' pf',
      lookup string_dec srl0 s = Some r' -> 
      exists r pf, lookup string_dec srl s = Some r /\
                subtype (exist _ r pf) (exist _ r' pf'))}).
      + induction srl0; simpl; [left; intros; discriminate | ].
         destruct a.
         case_eq (lookup string_dec srl s).
        * intros ? inn.
          assert (wfr:wf_rtype₀ r = true)
                 by (eapply (wf_rtype₀_Rec_In pfy); simpl; left; reflexivity).
          destruct (Forallt_In H _ (lookup_in string_dec _ inn) (wf_rtype₀_Rec_In e _ _ ((lookup_in string_dec _ inn))) (exist _ r wfr)) as [[?|?]_].
          
            destruct (IHsrl0 (wf_rtype₀_cons_tail pfy)).
              left. intros ? ? ? eqq. match_destr_in eqq; subst; eauto 2.
                inversion eqq; subst.
                rewrite (rtype_ext pf' wfr); eauto.
              right; intro nin. apply n; intros ss rr rrpf sin.
              specialize (nin ss rr). 
              match_destr_in nin; [| intuition ].
              subst.
              apply wf_rtype₀_cons_nin in pfy.
              congruence.
          right; intro nin. specialize (nin s r).
          match_destr_in nin; [| intuition ].
          destruct (nin wfr (eq_refl _)) as [? [?[??]]]; simpl in *.
          rewrite inn in H0. inversion H0; subst.
          apply n.
          rewrite (rtype_ext _ x0). trivial.
        * right; intro nin. specialize (nin s r).
          match_destr_in nin; [| intuition ].
          assert (wfr:wf_rtype₀ r = true)
                 by (eapply (wf_rtype₀_Rec_In pfy); simpl; left; reflexivity).
          destruct (nin wfr (eq_refl _)) as [? [?[??]]].
          congruence.
      + destruct sub.
        * destruct k0.
          left.
          destruct (from_Rec₀ srl e) as [? [?[??]]]; subst.
          rewrite <- H1.
          destruct (from_Rec₀ _ pfy) as [? [?[??]]]; subst.
          rewrite <- H2.
          econstructor; try discriminate.
          intros ? ? lo. destruct r'.
          apply lookup_map_some' in lo.
          destruct (e0 _ _ e1 lo) as [?[?[??]]].
          rewrite <- (lookup_map_some' _ _ _ x5) in H0.
          exists (exist _ x4 x5). intuition.
          destruct k.
             right; inversion 1; intuition; discriminate.
           destruct (incl_list_dec string_dec (domain srl) (domain srl0)).
             left.
             destruct (from_Rec₀ srl e) as [? [?[??]]]; subst.
             rewrite <- H1.
             destruct (from_Rec₀ _ pfy) as [? [?[??]]]; subst.
             rewrite <- H2.
             constructor; intros.
               destruct r'.
               rewrite (lookup_map_some' _ _ _ e1) in H0.
               destruct (e0 _ _ e1 H0) as [?[?[??]]].
               rewrite <- (lookup_map_some' _ _ _ x5) in H3.
               exists (exist _ x4 x5). intuition.
               intuition.
                 specialize (i s).
                 unfold domain in i; repeat rewrite map_map in i.
                 simpl in i.
                 auto.
             right; inversion 1; rtype_equalizer; subst; eauto 2.
             intuition.  apply n.
             intros ? .
             unfold domain; repeat rewrite map_map.
             simpl.
             auto.
        * right; inversion 1; apply n; rtype_equalizer; subst; eauto.
          intros.
          rewrite <- (lookup_map_some' _ _ _ pf') in H1.
          destruct (H4 _ _ H1) as [? [??]].
          destruct x.
          exists x; exists e0.
          rewrite <- (lookup_map_some' _ _ _ e0).
          intuition.
    - rename srl into srl0; rename r into srl.
      assert (sub:{forall s r' pf',
      lookup string_dec srl s = Some r' -> 
      exists r pf, lookup string_dec srl0 s = Some r /\
                subtype (exist _ r pf) (exist _ r' pf')} + {~ (forall s r' pf',
      lookup string_dec srl s = Some r' -> 
      exists r pf, lookup string_dec srl0 s = Some r /\
                   subtype (exist _ r pf) (exist _ r' pf'))}).
      + induction srl; simpl; [left; intros; discriminate | ].
        destruct a.
        case_eq (lookup string_dec srl0 s).
        * intros ? inn.
          assert (wfr0:wf_rtype₀ r0 = true)
            by (eapply (wf_rtype₀_Rec_In pfy); eapply lookup_in; eauto).
          assert (wfr:wf_rtype₀ r = true)
            by (eapply (wf_rtype₀_Rec_In e); simpl; left; reflexivity).
          invcs H.
          simpl in H2.
          destruct (H2 wfr (exist _ r0 wfr0)) as [_ issub].
          { destruct issub.
            - destruct (IHsrl H3 (wf_rtype₀_cons_tail e)).
              + left; intros ? ? ? eqq.
                match_destr_in eqq; subst; eauto 2.
                inversion eqq; subst.
                rewrite (rtype_ext pf' wfr); eauto.
              + right; intro nin. apply n; intros ss rr rrpf sin.
                specialize (nin ss rr). 
                match_destr_in nin; [| intuition ].
                subst.
                apply wf_rtype₀_cons_nin in e.
                congruence.
            - right; intro nin. specialize (nin s r).
              match_destr_in nin; [| intuition ].
              destruct (nin wfr (eq_refl _)) as [? [?[??]]]; simpl in *.
              rewrite inn in H. inversion H; subst.
              apply n.
              rewrite (rtype_ext _ x0). trivial.
          } 
        * right; intro nin. specialize (nin s r).
          match_destr_in nin; [| intuition ].
          assert (wfr:wf_rtype₀ r = true)
            by (eapply (wf_rtype₀_Rec_In e); simpl; left; reflexivity).
          destruct (nin wfr (eq_refl _)) as [? [?[??]]].
          congruence.
      + destruct sub.
        * {destruct k.
           - left.
             destruct (from_Rec₀ srl e) as [? [?[??]]]; subst.
             rewrite <- H1.
             destruct (from_Rec₀ _ pfy) as [? [?[??]]]; subst.
             rewrite <- H2.
             econstructor; try discriminate.
             intros ? ? lo. destruct r'.
             apply lookup_map_some' in lo.
             destruct (e0 _ _ e1 lo) as [?[?[??]]].
             rewrite <- (lookup_map_some' _ _ _ x5) in H0.
             exists (exist _ x4 x5). intuition.
           - destruct k0.
             + right.
               inversion 1; subst.
               intuition; discriminate.
             + destruct (incl_list_dec string_dec (domain srl0) (domain srl)).
               * left.
                 destruct (from_Rec₀ srl e) as [? [?[??]]]; subst.
                 rewrite <- H1.
                 destruct (from_Rec₀ _ pfy) as [? [?[??]]]; subst.
                 rewrite <- H2.
                 { constructor; intros.
                   - destruct r'.
                     rewrite (lookup_map_some' _ _ _ e1) in H0.
                     destruct (e0 _ _ e1 H0) as [?[?[??]]].
                     rewrite <- (lookup_map_some' _ _ _ x5) in H3.
                     exists (exist _ x4 x5). intuition.
                   - intuition.
                     specialize (i s).
                     unfold domain in i; repeat rewrite map_map in i.
                     simpl in i.
                     auto.
                 } 
               * right; inversion 1; rtype_equalizer; subst; eauto 2.
                 intuition.  apply n.
                 intros ? .
                 unfold domain; repeat rewrite map_map.
                 simpl.
                 auto.
          } 
        * right; inversion 1; apply n; rtype_equalizer; subst; eauto.
          intros.
          rewrite <- (lookup_map_some' _ _ _ pf') in H1.
          destruct (H4 _ _ H1) as [? [??]].
          destruct x.
          exists x; exists e0.
          rewrite <- (lookup_map_some' _ _ _ e0).
          intuition.
    - destruct (Either₀_wf_inv e) as [pfl1 pfr1].
      destruct (Either₀_wf_inv pfy) as [pfl2 pfr2].
      destruct (IHx1 pfl1 (exist _ _ pfl2)) as [[?|?]_].
      + destruct (IHx2 pfr1 (exist _ _ pfr2)) as [[?|?]_].
        * left.
          rewrite (Either_canon _ _ _ pfl1 pfr1).
          rewrite (Either_canon _ _ _ pfl2 pfr2).
          eauto.
        * right; inversion 1; subst.
            apply n. rewrite (rtype_ext pfr1 pfr2). eauto.
            rewrite (Either_canon _ _ _ pfl1 pfr1) in H.
            rewrite (Either_canon _ _ _ pfl2 pfr2) in H.
            apply n.
            inversion H; rtype_equalizer; subst.
              rewrite (rtype_ext pfr1 pfr2). eauto.
              subst.
              rewrite (rtype_ext pfr1 (proj2_sig r1)).
              rewrite (rtype_ext pfr2 (proj2_sig r2)).
              destruct r1; destruct r2. simpl in *.
              trivial.
      + right; inversion 1; subst.
         apply n. rewrite (rtype_ext pfl1 pfl2). eauto.
            rewrite (Either_canon _ _ _ pfl1 pfr1) in H.
            rewrite (Either_canon _ _ _ pfl2 pfr2) in H.
            apply n.
            inversion H. rtype_equalizer.
              subst. rewrite (rtype_ext pfl1 pfl2). eauto.

            subst.
            rewrite (rtype_ext pfl1 (proj2_sig l1)).
            rewrite (rtype_ext pfl2 (proj2_sig l2)).
            destruct l1; destruct l2. simpl in *.
            trivial.
    - destruct (Either₀_wf_inv e) as [pfl1 pfr1].
      destruct (Either₀_wf_inv pfy) as [pfl2 pfr2].
      destruct (IHx1 pfl1 (exist _ _ pfl2)) as [_[?|?]].
      + destruct (IHx2 pfr1 (exist _ _ pfr2)) as [_[?|?]].
        * left.
          rewrite (Either_canon _ _ _ pfl1 pfr1).
          rewrite (Either_canon _ _ _ pfl2 pfr2).
          eauto.
        * right; inversion 1; subst.
            apply n. rewrite (rtype_ext pfr1 pfr2). eauto.
            rewrite (Either_canon _ _ _ pfl1 pfr1) in H.
            rewrite (Either_canon _ _ _ pfl2 pfr2) in H.
            apply n.
            { inversion H; rtype_equalizer; subst.
              - rewrite (rtype_ext pfr1 pfr2). eauto.
              - subst.
              rewrite (rtype_ext pfr2 (proj2_sig r1)).
              rewrite (rtype_ext pfr1 (proj2_sig r2)).
              destruct r1; destruct r2. simpl in *.
              trivial.
            } 
      + right; inversion 1; subst.
         apply n. rewrite (rtype_ext pfl1 pfl2). eauto.
            rewrite (Either_canon _ _ _ pfl1 pfr1) in H.
            rewrite (Either_canon _ _ _ pfl2 pfr2) in H.
            apply n.
            inversion H. rtype_equalizer.
              subst. rewrite (rtype_ext pfl1 pfl2). eauto.

            subst.
            rewrite (rtype_ext pfl2 (proj2_sig l1)).
            rewrite (rtype_ext pfl1 (proj2_sig l2)).
            destruct l1; destruct l2. simpl in *.
            trivial.
    - destruct (Arrow₀_wf_inv e) as [pfl1 pfr1].
      destruct (Arrow₀_wf_inv pfy) as [pfl2 pfr2].
      destruct (IHx1 pfl1 (exist _ _ pfl2)) as [?[?|?]].
      + destruct (IHx2 pfr1 (exist _ _ pfr2)) as [[?|?]?].
        * left.
          rewrite (Arrow_canon _ _ _ pfl1 pfr1).
          rewrite (Arrow_canon _ _ _ pfl2 pfr2).
          econstructor; eauto.
        * right; inversion 1; subst.
            apply n. rewrite (rtype_ext pfr1 pfr2). eauto.
            rewrite (Arrow_canon _ _ _ pfl1 pfr1) in H.
            rewrite (Arrow_canon _ _ _ pfl2 pfr2) in H.
            apply n.
            inversion H; rtype_equalizer; subst.
              rewrite (rtype_ext pfr1 pfr2). eauto.
              subst.
              rewrite (rtype_ext pfr1 (proj2_sig out1)).
              rewrite (rtype_ext pfr2 (proj2_sig out2)).
              destruct out1; destruct out2. simpl in *.
              trivial.
      + right; inversion 1; subst.
         apply n. rewrite (rtype_ext pfl1 pfl2). eauto.
            rewrite (Arrow_canon _ _ _ pfl1 pfr1) in H.
            rewrite (Arrow_canon _ _ _ pfl2 pfr2) in H.
            apply n.
            inversion H. rtype_equalizer.
            subst. rewrite (rtype_ext pfl1 pfl2). eauto.
            rtype_equalizer.
            subst.
            rewrite (rtype_ext pfl1 (proj2_sig in1)).
            rewrite (rtype_ext pfl2 (proj2_sig in2)).
            destruct in1; destruct in2. simpl in *.
              trivial.
    - destruct (Arrow₀_wf_inv e) as [pfl1 pfr1].
      destruct (Arrow₀_wf_inv pfy) as [pfl2 pfr2].
      destruct (IHx1 pfl1 (exist _ _ pfl2)) as [[?|?]?].
      + destruct (IHx2 pfr1 (exist _ _ pfr2)) as [?[?|?]].
        * left.
          rewrite (Arrow_canon _ _ _ pfl1 pfr1).
          rewrite (Arrow_canon _ _ _ pfl2 pfr2).
          econstructor; eauto.
        * right; inversion 1; subst.
            apply n. rewrite (rtype_ext pfr1 pfr2). eauto.
            rewrite (Arrow_canon _ _ _ pfl1 pfr1) in H.
            rewrite (Arrow_canon _ _ _ pfl2 pfr2) in H.
            apply n.
            inversion H; rtype_equalizer; subst.
              rewrite (rtype_ext pfr1 pfr2). eauto.
              subst.
              rewrite (rtype_ext pfr1 (proj2_sig out2)).
              rewrite (rtype_ext pfr2 (proj2_sig out1)).
              destruct out1; destruct out2. simpl in *.
              trivial.
      + right; inversion 1; subst.
         apply n. rewrite (rtype_ext pfl1 pfl2). eauto.
            rewrite (Arrow_canon _ _ _ pfl1 pfr1) in H.
            rewrite (Arrow_canon _ _ _ pfl2 pfr2) in H.
            apply n.
            inversion H. rtype_equalizer.
            subst. rewrite (rtype_ext pfl1 pfl2). eauto.
            rtype_equalizer.
            subst.
            rewrite (rtype_ext pfl1 (proj2_sig in2)).
            rewrite (rtype_ext pfl2 (proj2_sig in1)).
            destruct in1; destruct in2. simpl in *.
              trivial.
    - destruct (sub_brands_dec brand_relation_brands b b0).
      + left; repeat rewrite Brand_canon; eauto.
      + right. inversion 1; subst; eauto 2.
        * intuition.
        * apply n.
          repeat rewrite (canon_brands_equiv).
          trivial.
    - destruct (sub_brands_dec brand_relation_brands b0 b).
      + left; repeat rewrite Brand_canon; eauto.
      + right. inversion 1; subst; eauto 2.
        * intuition.
        * apply n.
          repeat rewrite (canon_brands_equiv).
          trivial.
    - destruct (foreign_type_sub_dec ft ft0).
      + left. repeat rewrite Foreign_canon.
        apply SForeign; trivial.
      + right; intros sub.
        invcs sub.
        * apply n; reflexivity.
        * intuition.
    - destruct (foreign_type_sub_dec ft0 ft).
      + left. repeat rewrite Foreign_canon.
        apply SForeign; trivial.
      + right; intros sub.
        invcs sub.
        * apply n; reflexivity.
        * intuition.
  Defined.
  
  Theorem subtype_dec x y : {subtype x y} + {~ subtype x y}.
  Proof.
    destruct (subtype_both_dec x y) as [? _].
    trivial.
  Defined.

End RSubtype.

Lemma subtype_ext {ftype:foreign_type} {br:brand_relation} {a b pfa pfb} :
  subtype (exist _ a pfa) (exist _ b pfb) ->
             forall pfa' pfb',
               subtype (exist _ a pfa') (exist _ b pfb').
Proof.
  intros.
  rewrite (rtype_ext pfa' pfa).
  rewrite (rtype_ext pfb' pfb).
  trivial.
Qed.

Lemma subtype_Either_inv {ftype:foreign_type} {br:brand_relation} {τl τr τl' τr'} :
  subtype (Either τl τr) (Either τl' τr') ->
  subtype τl τl'  /\
  subtype τr τr'.
Proof.
  inversion 1; rtype_equalizer; subst.
  - subst; split; econstructor.
  - subst. intuition.
Qed.

Lemma subtype_Arrow_inv {ftype:foreign_type} {br:brand_relation} {τl τr τl' τr'} :
  subtype (Arrow τl τr) (Arrow τl' τr') ->
  subtype τl' τl  /\
  subtype τr τr'.
Proof.
  inversion 1; rtype_equalizer; subst.
  - subst; split; econstructor.
  - subst. intuition.
Qed.

Notation "r1 <: r2" := (subtype r1 r2) (at level 70).

