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
Require Import RelationClasses.
Require Import EquivDec.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignType.
Require Import RType.
Require Import RSubtypeProp.
Require Import RTypeMeetJoin.

Section RConsistentSubtype.

  Context {ftype:foreign_type}.
  Context {br:brand_relation}.

Hint Constructors subtype.

Section rtype_join_meet.
  
  Lemma consistent_rtype_join_meet1:
    forall a b, subtype a b ->
                rtype_join a b = b
                /\ rtype_meet a b = a.
Proof.
  destruct a as [a awf]; destruct b as [b bwf]; intros.
  cut (  rtype_join₀ a b = b
         /\ rtype_meet₀ a b = a).
  { intros HH.
    split; apply rtype_fequal; simpl; apply HH.
  }
  revert H.
  cut (
      (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) a awf <:
         exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) b bwf ->
         rtype_join₀ a b = b /\ rtype_meet₀ a b = a)
      /\ (            exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) b bwf <:
                      exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) a awf ->

            rtype_join₀ b a = a /\ rtype_meet₀ b a = b)
    ).
  { intros HH; intuition.
  } 
  revert awf b bwf.
  induction a; split; inversion 1; unfold rtype_join₀; unfold rtype_meet₀; simpl; subst; fold rtype_join₀ rtype_meet₀;
    try tauto.
  - (* ⊤₀ *) destruct b; simpl; try tauto.
  - (* ⊤₀ *) destruct b; simpl; try tauto.
  - (* Coll₀ *)
    rewrite rtype_join₀_idempotent; trivial.
    rewrite rtype_meet₀_idempotent; trivial.
    tauto.
  - (* Coll₀ *)
    simpl in *. specialize (IHa awf _ bwf).
    inversion H; subst.
    + repeat split; f_equal.
      * apply rtype_join₀_idempotent; auto.
      * apply rtype_meet₀_idempotent; auto.
    + rtype_equalizer. subst.
      repeat split; f_equal; apply IHa;
       destruct r1; destruct r2;
       simpl in *;
       assert (e = awf) by (apply wf_rtype₀_ext);
       assert (e0 = bwf) by (apply wf_rtype₀_ext);
       subst; auto.
  - (* Coll₀ *)
    rewrite rtype_join₀_idempotent; trivial.
    rewrite rtype_meet₀_idempotent; trivial.
    tauto.
  - (* Coll₀ *)
    simpl in *. specialize (IHa awf _ bwf).
    inversion H; subst.
    + repeat split; f_equal.
      * apply rtype_join₀_idempotent; auto.
      * apply rtype_meet₀_idempotent; auto.
    + rtype_equalizer. subst.
      repeat split; f_equal; apply IHa;
       destruct r1; destruct r2;
         simpl in *;
      eapply subtype_ext; eauto.
  - (* Rec₀ *)
    rewrite (record_kind_rtype_join_idempotent),
    (@map_rtype_join₀_idempotent ftype br k r); auto.
    generalize (rtype_meet₀_idempotent (Rec₀ k r)); simpl in *; intuition.
  - (* Rec₀ *)
    repeat split.
    + { f_equal.
        destruct k2; trivial; [apply record_kind_rtype_join_open_r | ].
      intuition; subst. simpl.
      match goal with
          [|- context[if ?X then _ else _ ]] => destruct X
      end; trivial.
      elim c.
      generalize awf bwf. simpl; repeat rewrite andb_true_iff.
      intuition.
      apply Sorted_incl_both_eq; trivial; try (eapply is_list_sorted_Sorted_iff; eauto);
      unfold domain; repeat rewrite map_map; simpl;
      (rewrite (@map_eq _ _ _ fst rl1) by (apply Forall_forall; intuition));
      (rewrite (@map_eq _ _ _ fst rl2) by (apply Forall_forall; intuition));
      trivial.
      intros ? inn.
      apply (in_dom_lookup string_dec) in inn.
      destruct inn as [? lo].
      destruct (H4 _ _ lo) as [? [lo2 _]].
      apply lookup_in in lo2. apply in_dom in lo2.
      apply lo2.
    revert rl2 H awf bwf H0 H4 H5. induction rl1; intros.
     + destruct rl2; simpl; trivial.
        destruct p. specialize (H4 s r). simpl in H4.
        destruct (string_dec s s); intuition.
        destruct H1 as [?[??]]; discriminate.
     + inversion H; subst.
       destruct rl2; [simpl in *; rewrite (@map_rtype_join₀_nil_r ftype br); trivial|].
        generalize awf bwf; intros awf' bwf'.
       rewrite map_cons in awf', bwf'.
       generalize (wf_rtype₀_cons_tail awf'); intros awf'';
       generalize (wf_rtype₀_cons_tail bwf'); intros bwf''.
       destruct a; destruct p; simpl.
       case_eq (string_dec s s0);
      [intros t teq | intros neq neqpf].
      * subst. simpl in H.
        simpl in awf',bwf'. repeat rewrite andb_true_iff in awf',bwf'.
        intuition.
       destruct (to_Rec k ((s0,r) :: rl1) awf).
       destruct (to_Rec k2 ((s0,r0):: rl2) bwf).
       rewrite H8, H12 in H0.

       generalize (Rec_subtype_cons_inv H0); intros [pf' [pf'' subinv]].
       specialize (IHrl1 rl2 H6 awf'' bwf'').
       simpl in H3.
       f_equal.
       f_equal.
       apply  (H3 H9 _ H2).
       apply Rec_subtype_cons_eq in H0.
       destruct r; destruct r0; simpl.
       eapply subtype_ext; eauto.
       etransitivity; [|eapply IHrl1].
       apply (@map_rtype_join₀_lookup_none2 ftype br).
       apply lookup_nin_none.
       intro inn.
       unfold domain in inn; rewrite map_map in inn.
       simpl in inn.
       rewrite (map_eq (g:=fst)) in inn by (rewrite Forall_forall; trivial).
       generalize x; intros isl;
       apply is_list_sorted_NoDup in isl; [|eapply StringOrder.lt_strorder].
       inversion isl; subst. intuition.
       eapply subtype_ext; eauto.
       inversion subinv; subst; rtype_equalizer.
       subst; eauto.       
       subst; eauto.
       intuition; subst.
       eapply (SRec_closed_equiv_domain subinv); trivial.
     * generalize (H4 s0 r0); simpl.
       destruct (string_dec s0 s0);  [|intuition].
       destruct (string_dec s0 s);  [congruence|].
       destruct 1 as [r1 [los0 r1sub]]; trivial.
       assert (slt:StringOrder.lt s s0).
         unfold wf_rtype₀ in awf'.
         rewrite andb_true_iff in awf'.
         destruct awf' as [isl _].
         apply is_list_sorted_Sorted_iff in isl.
         apply Sorted_StronglySorted in isl; [|eapply StringOrder.lt_strorder].
         simpl in isl.
         unfold domain in isl; rewrite map_map in isl.
         simpl in isl.
         inversion isl; subst.
         rewrite Forall_forall in H8.
         apply H8.
         rewrite (map_eq (g:=fst)) by (rewrite Forall_forall; trivial).
         rewrite <- domain_eq.
         eapply in_dom; eapply lookup_in; eauto.
       assert (snin:lookup string_dec rl2 s = None).
       case_eq (lookup string_dec rl2 s); [intros t teq|auto].
       unfold wf_rtype₀ in bwf'.
         rewrite andb_true_iff in bwf'.
         destruct bwf' as [isl _].
         apply is_list_sorted_Sorted_iff in isl.
         apply Sorted_StronglySorted in isl; [|eapply StringOrder.lt_strorder].
         simpl in isl.
         unfold domain in isl; rewrite map_map in isl.
         simpl in isl.
         inversion isl; subst.
         rewrite Forall_forall in H8.
         specialize (H8 s).
         rewrite (map_eq (g:=fst)) in H7 by (rewrite Forall_forall; trivial).
         fold (domain rl2) in H5.
         apply lookup_in in teq. apply in_dom in teq.
         specialize (H8 teq).
         rewrite H8 in slt.
         eelim ODT_lt_irr; eauto.
       apply lookup_map_none in snin.
       rewrite snin.
       rewrite (map_rtype_join₀_commutative k k2 (ftype:=ftype) (br:=br)); auto.
       simpl.
       generalize los0; intros los0'.
       apply lookup_map_some in los0'; rewrite los0'.
       rewrite (map_rtype_join₀_commutative k k2 (ftype:=ftype) (br:=br)); auto.
       simpl in H3. f_equal.
         f_equal.
         revert H6 los0 r1sub. clear.
         induction rl1; simpl; intros F leq sub; try discriminate.
         destruct a; simpl in *.
         inversion F; subst.
         destruct (string_dec s0 s); intros; subst; [|auto].
           inversion leq; subst.
           simpl in H1.
           destruct r0; destruct r1; simpl in *.
           rewrite rtype_join₀_commutative; auto.
           apply (H1 e0 _ e); auto.
       apply (IHrl1 _ H6 (wf_rtype₀_cons_tail awf) (wf_rtype₀_cons_tail bwf)).
       destruct (to_Rec k ((s,r) :: rl1) awf).
       destruct (to_Rec k2 ((s0,r0):: rl2) bwf).
       rewrite H1, H2 in H0.
       apply Rec_subtype_cons_inv2 in H0.
       destruct H0 as [pf' rec1].
       apply Rec_subtype_cons_inv1 in rec1.
       destruct rec1 as [pf'' rec1].
       destruct (to_Rec k rl1 (wf_rtype₀_cons_tail awf)) as [? re1].
       destruct (to_Rec k2 rl2 (wf_rtype₀_cons_tail bwf)) as [? re2].
       rewrite re1, re2.
       rewrite (Rec_pr_irrel _ _ _ pf').
       rewrite (Rec_pr_irrel _ _ _ pf'').
       destruct k2; trivial.
       intuition; subst.
       specialize (H7 s).
       simpl in H7.
       intuition.
       apply lookup_map_none in snin.
       apply lookup_none_nin in snin.
       elim snin; trivial.
       apply lookup_map_none in snin.
       trivial.
       intros ss rr inn.
       assert (isl:is_list_sorted ODT_lt_dec (s0 :: domain rl2) = true)
       by (simpl in bwf';
           generalize bwf'; repeat rewrite andb_true_iff; unfold domain; rewrite map_map; intuition).
       assert (ss <> s0).
       apply is_list_sorted_NoDup in isl. inversion isl; subst.
       apply lookup_in in inn.
       apply in_dom in inn.
       congruence.
       eapply StringOrder.lt_strorder.
       destruct (H4 ss rr).
       simpl.
       destruct (string_dec ss s0); congruence.
       destruct H2 as [inn2 sub].
       simpl in inn2.
       destruct (string_dec ss s); try eauto.
       assert (isl2:is_list_sorted ODT_lt_dec (s :: domain rl2) = true).
        simpl.
        apply is_list_sorted_cons in isl.
        destruct (domain rl2); simpl in *; intuition.
        destruct (StringOrder.lt_dec s s1); trivial.
        rewrite <- slt in H7.
        congruence.
        apply is_list_sorted_NoDup in isl2. inversion isl2; subst.
        apply lookup_in in inn.
        apply in_dom in inn.
        congruence.
       eapply StringOrder.lt_strorder.

       intuition.
       specialize (H7 s1). simpl in H7; intuition.
       subst.
       destruct (to_Rec Closed ((s,r)::rl1) awf) as [? re1].
       destruct (to_Rec Closed ((s1,r0)::rl2) bwf) as [? re2].
       rewrite re1, re2 in H0.
       destruct (SRec_closed_equiv_domain H0 s) as [inn _].
       simpl in inn. intuition.
       apply lookup_map_none in snin.
       apply lookup_none_nin in snin.
       elim snin; assumption.
      }
    + {
       assert (incl21:incl (domain rl2) (domain rl1)).
     {
       unfold domain.
       intros s inn.
        apply in_map_iff in inn.
        apply in_map_iff.
        destruct inn as [[s' τ'] [eqq1 inn]]; simpl in eqq1, inn.
        subst.
        apply (in_lookup string_dec) in inn.
        subst.
        destruct inn as [v lo].
        specialize (H4 _ _ lo).
        destruct H4 as [r [rin rt]].
        exists (s,r).
        simpl; split; trivial.
        eapply lookup_in; eauto.
     }
     assert (subl21:sublist (domain rl2) (domain rl1)).
     {
       generalize awf bwf; simpl.
       repeat rewrite andb_true_iff.
       unfold domain; repeat rewrite map_map; simpl; intros [??] [??].
       apply Sorted_incl_sublist.
       - apply (is_list_sorted_Sorted_iff ODT_lt_dec); auto.
       - apply (is_list_sorted_Sorted_iff ODT_lt_dec); auto.
       - apply incl21.
     }
    match_destr.
    + {
      f_equal.
      { destruct k; destruct k2; intuition. }
      rewrite lookup_diff_domain_bounded.
      - unfold rec_concat_sort.
        rewrite app_nil_r.
        rewrite sort_sorted_is_id.
        + apply drec_sorted_perm_eq.
          * generalize (map_rtype_meet₀_domain (br:=br)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl1)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl2)); intros eqq.
             rewrite eqq.
             generalize awf; simpl; rewrite andb_true_iff; intuition.
          * generalize awf; simpl; rewrite andb_true_iff; intuition.
          * {
              apply (NoDup_domain_lookups_Permutation string_dec).
              - generalize (map_rtype_meet₀_domain (br:=br)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl1)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl2)); intros eqq.
             rewrite eqq.
             generalize awf; simpl; rewrite andb_true_iff; intuition eauto 2.
          - generalize awf; simpl; rewrite andb_true_iff; intuition eauto 2. 
          - intros s.
            {
              case_eq ( lookup string_dec
                               (map
                                  (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                     (fst x, proj1_sig (snd x))) rl1) s); [intros τ srin | intros snin].
              -  case_eq ( lookup string_dec
                               (map
                                  (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                     (fst x, proj1_sig (snd x))) rl2) s); [intros τ2 srin2 | intros s2nin].
                 + generalize (@map_rtype_meet₀_rtype_meets _ _ (map
                                                    (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                       (fst x, proj1_sig (snd x))) rl1)
                                               (map
                                                  (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                     (fst x, proj1_sig (snd x))) rl2) s τ τ2); intros eqq.
                   rewrite eqq; trivial.
                   f_equal.
                   rewrite Forall_forall in H.
                   generalize (H _ (lookup_in _ _ srin)); simpl; intros eqq2.
                   apply lookup_map_some_ex in srin.
                   apply lookup_map_some_ex in srin2.
                   destruct srin as [pfτ srin].
                   destruct srin2 as [pfτ2 srin2].
                   apply (eqq2 pfτ τ2 pfτ2).
                   destruct (H4 _ _ srin2) as [r' [lor subr]].
                   unfold rtype in lor, srin; rewrite lor in srin.
                   inversion srin; subst.
                   trivial.
                 + generalize (@map_rtype_meet₀_some_none _ _ (map
                                                    (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                       (fst x, proj1_sig (snd x))) rl1)
                                               (map
                                                  (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                     (fst x, proj1_sig (snd x))) rl2) s τ); intros eqq.
                   rewrite eqq; trivial.
                   - generalize (@map_rtype_meet₀_none _ _ (map
                                                      (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                         (fst x, proj1_sig (snd x))) rl1)
                                                 (map
                                                    (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                       (fst x, proj1_sig (snd x))) rl2) s); intros eqq.
                   rewrite eqq; trivial.
            }
            }
        + simpl.
          generalize (map_rtype_meet₀_domain (br:=br)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl1)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl2)); intros eqq.
          rewrite eqq.
          generalize awf; simpl; rewrite andb_true_iff; intuition.
      - unfold domain in *.
        repeat rewrite map_map; simpl.
        apply incl21.
      }
    + destruct k; destruct k2; simpl in *.
      * intuition.
      * intuition; discriminate.
      * elim n.
        unfold domain; repeat rewrite map_map; simpl.
        apply subl21.
      * elim n.
        generalize awf bwf; simpl.
       repeat rewrite andb_true_iff.
       unfold domain; repeat rewrite map_map; simpl; intros [??] [??].
        { apply sublist_antisymm.
          - apply subl21.
          - apply Sorted_incl_sublist.
            + apply (is_list_sorted_Sorted_iff StringOrder.lt_dec); auto.
            +  apply (is_list_sorted_Sorted_iff StringOrder.lt_dec); auto.
            + intuition.
        }
      }
  - (* Rec₀ *)
    rewrite (record_kind_rtype_join_idempotent),
    (@map_rtype_join₀_idempotent ftype br k r); auto.
    generalize (rtype_meet₀_idempotent (Rec₀ k r)); simpl in *; intuition.
  - (* Rec₀ *)
    repeat split.
    + { f_equal.
        destruct k; trivial; [apply record_kind_rtype_join_open_r | ].
      intuition; subst. simpl.
      match goal with
          [|- context[if ?X then _ else _ ]] => destruct X
      end; trivial.
      elim c.
      generalize awf bwf. simpl; repeat rewrite andb_true_iff.
      intuition.
      apply Sorted_incl_both_eq; trivial; try (eapply is_list_sorted_Sorted_iff; eauto);
      unfold domain; repeat rewrite map_map; simpl;
      (rewrite (@map_eq _ _ _ fst rl1) by (apply Forall_forall; intuition));
      (rewrite (@map_eq _ _ _ fst rl2) by (apply Forall_forall; intuition));
      trivial.
      intros ? inn.
      apply (in_dom_lookup string_dec) in inn.
      destruct inn as [? lo].
      destruct (H4 _ _ lo) as [? [lo2 _]].
      apply lookup_in in lo2. apply in_dom in lo2.
      apply lo2.
    revert rl2 H awf bwf H0 H4 H5. induction rl1; intros.
     + destruct rl2; simpl; trivial.
        destruct p. specialize (H4 s r). simpl in H4.
        destruct (string_dec s s); intuition.
        destruct H1 as [?[??]]; discriminate.
     + inversion H; subst.
       { destruct rl2.
         - simpl in *; rewrite (@map_rtype_join₀_nil_r ftype br); simpl; trivial.
         - discriminate.
       } 
       destruct rl2.
       { simpl in *; discriminate. }
       generalize awf bwf; intros awf' bwf'.
       generalize (wf_rtype₀_cons_tail awf'); intros awf'';
       generalize (wf_rtype₀_cons_tail bwf'); intros bwf''.
       destruct a; destruct p; simpl.
       destruct x; simpl.
       simpl in H1.
       inversion H1; clear H1; subst.
       case_eq (string_dec s s0);
      [intros t teq | intros neq neqpf].
      * subst. simpl in H.
        simpl in awf',bwf'. repeat rewrite andb_true_iff in awf',bwf'.
        intuition.
       destruct (to_Rec k1 ((s0,r) :: rl1) bwf).
       destruct (to_Rec k ((s0,r0):: rl2) awf).
       rewrite H8, H12 in H0.

       generalize (Rec_subtype_cons_inv H0); intros [pf' [pf'' subinv]].
       inversion H; clear H; subst.
       specialize (IHrl1 rl2 H16 awf'' bwf'').
       f_equal.
       f_equal.
       simpl in H15.
       apply Rec_subtype_cons_eq in H0.
       eapply H15.
       destruct r; destruct r0; simpl.
       eapply subtype_ext; eauto.
       etransitivity; [|eapply IHrl1].
       apply (@map_rtype_join₀_lookup_none2 ftype br).
       apply lookup_nin_none.
       intro inn.
       unfold domain in inn; rewrite map_map in inn.
       simpl in inn.
       rewrite (map_eq (g:=fst)) in inn by (rewrite Forall_forall; trivial).
       generalize x; intros isl;
       apply is_list_sorted_NoDup in isl; [|eapply StringOrder.lt_strorder].
       inversion isl; subst. intuition.
       eapply subtype_ext; eauto.
       inversion subinv; subst; rtype_equalizer.
       subst; eauto.       
       subst; eauto.
       intuition; subst.
       eapply (SRec_closed_equiv_domain subinv); trivial.
     * generalize (H4 s0 r0); simpl.
       destruct (string_dec s0 s0);  [|intuition].
       destruct (string_dec s0 s);  [congruence|].
       destruct 1 as [r1 [los0 r1sub]]; trivial.
       assert (slt:StringOrder.lt s s0).
         unfold wf_rtype₀ in bwf'.
         rewrite andb_true_iff in bwf'.
         destruct bwf' as [isl _].
         apply is_list_sorted_Sorted_iff in isl.
         apply Sorted_StronglySorted in isl; [|eapply StringOrder.lt_strorder].
         simpl in isl.
         unfold domain in isl; rewrite map_map in isl.
         simpl in isl.
         inversion isl; subst.
         rewrite Forall_forall in H8.
         apply H8.
         rewrite (map_eq (g:=fst)) by (rewrite Forall_forall; trivial).
         rewrite <- domain_eq.
         eapply in_dom; eapply lookup_in; eauto.
         
       assert (snin:lookup string_dec rl2 s = None).
       case_eq (lookup string_dec rl2 s); [intros t teq|auto].
       unfold wf_rtype₀ in awf'.
         rewrite andb_true_iff in awf'.
         destruct awf' as [isl _].
         apply is_list_sorted_Sorted_iff in isl.
         apply Sorted_StronglySorted in isl; [|eapply StringOrder.lt_strorder].
         simpl in isl.
         unfold domain in isl; rewrite map_map in isl.
         simpl in isl.
         inversion isl; subst.
         rewrite Forall_forall in H8.
         specialize (H8 s).
         rewrite (map_eq (g:=fst)) in H7 by (rewrite Forall_forall; trivial).
         fold (domain rl2) in H5.
         apply lookup_in in teq. apply in_dom in teq.
         specialize (H8 teq).
         rewrite H8 in slt.
         eelim ODT_lt_irr; eauto.
       apply lookup_map_none in snin.
       rewrite snin.
       rewrite (map_rtype_join₀_commutative k k1 (ftype:=ftype) (br:=br)); auto.
       simpl.
       generalize los0; intros los0'.
       apply lookup_map_some in los0'; rewrite los0'.
       rewrite (map_rtype_join₀_commutative k k1 (ftype:=ftype) (br:=br)); auto.
       simpl in H3. f_equal.
       f_equal.
       simpl in *.
         destruct r1 as [r1 r1wf]; destruct r0 as [r0 r0wf]; simpl in *.
         rewrite rtype_join₀_commutative; trivial.
         apply (H2 r0wf _ r1wf).
         eapply subtype_ext; eauto.
         apply (IHrl1 _ H3 (wf_rtype₀_cons_tail awf) (wf_rtype₀_cons_tail bwf)).
       destruct (to_Rec k1 ((s,r) :: rl1) bwf).
       destruct (to_Rec k ((s0,r0):: rl2) awf).
       rewrite H1,H6 in H0.
       apply Rec_subtype_cons_inv2 in H0.
       destruct H0 as [pf' rec1].
       apply Rec_subtype_cons_inv1 in rec1.
       destruct rec1 as [pf'' rec1].
       destruct (to_Rec k1 rl1 (wf_rtype₀_cons_tail bwf)) as [? re1].
       destruct (to_Rec k rl2 (wf_rtype₀_cons_tail awf)) as [? re2].
       rewrite re1, re2.
       rewrite (Rec_pr_irrel _ _ _ pf').
       rewrite (Rec_pr_irrel _ _ _ pf'').
       destruct k; trivial.
       intuition; subst.
       specialize (H7 s).
       simpl in H7.
       intuition.
       apply lookup_map_none in snin.
       apply lookup_none_nin in snin.
       elim snin; trivial.
       apply lookup_map_none in snin.
       trivial.
       intros ss rr inn.
       assert (isl:is_list_sorted ODT_lt_dec (s0 :: domain rl2) = true)
       by (simpl in awf';
           generalize awf'; repeat rewrite andb_true_iff; unfold domain; rewrite map_map; intuition).
       assert (ss <> s0).
       apply is_list_sorted_NoDup in isl. inversion isl; subst.
       apply lookup_in in inn.
       apply in_dom in inn.
       congruence.
       eapply StringOrder.lt_strorder.
       destruct (H4 ss rr).
       simpl.
       destruct (string_dec ss s0); congruence.
       destruct H6 as [inn2 sub].
       simpl in inn2.
       destruct (string_dec ss s); try eauto.
       assert (isl2:is_list_sorted ODT_lt_dec (s :: domain rl2) = true).
        simpl.
        apply is_list_sorted_cons in isl.
        destruct (domain rl2); simpl in *; intuition.
        destruct (StringOrder.lt_dec s s1); trivial.
        rewrite <- slt in H7.
        congruence.
        apply is_list_sorted_NoDup in isl2. inversion isl2; subst.
        apply lookup_in in inn.
        apply in_dom in inn.
        congruence.
       eapply StringOrder.lt_strorder.

       intuition.
       specialize (H7 s1). simpl in H7; intuition.
       subst.
       destruct (to_Rec Closed ((s,r)::rl1) bwf) as [? re1].
       destruct (to_Rec Closed ((s1,r0)::rl2) awf) as [? re2].
       rewrite re1, re2 in H0.
       destruct (SRec_closed_equiv_domain H0 s) as [inn _].
       simpl in inn. intuition.
       apply lookup_map_none in snin.
       apply lookup_none_nin in snin.
       elim snin; assumption.
      }
    + {
       assert (incl21:incl (domain rl2) (domain rl1)).
     {
       unfold domain.
       intros s inn.
        apply in_map_iff in inn.
        apply in_map_iff.
        destruct inn as [[s' τ'] [eqq1 inn]]; simpl in eqq1, inn.
        subst.
        apply (in_lookup string_dec) in inn.
        subst.
        destruct inn as [v lo].
        specialize (H4 _ _ lo).
        destruct H4 as [r [rin rt]].
        exists (s,r).
        simpl; split; trivial.
        eapply lookup_in; eauto.
     }
     assert (subl21:sublist (domain rl2) (domain rl1)).
     {
       generalize awf bwf; simpl.
       repeat rewrite andb_true_iff.
       unfold domain; repeat rewrite map_map; simpl; intros [??] [??].
       apply Sorted_incl_sublist.
       - apply (is_list_sorted_Sorted_iff ODT_lt_dec); auto.
       - apply (is_list_sorted_Sorted_iff ODT_lt_dec); auto.
       - apply incl21.
     }
    match_destr.
    + {
      f_equal.
      { destruct k; destruct k1; intuition. }
      rewrite lookup_diff_domain_bounded.
      - unfold rec_concat_sort.
        rewrite app_nil_r.
        rewrite sort_sorted_is_id.
        + apply drec_sorted_perm_eq.
          * generalize (map_rtype_meet₀_domain (ftype:=ftype) (br:=br)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl1)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl2)); intros eqq.
             rewrite eqq.
             generalize bwf; simpl; rewrite andb_true_iff; intuition.
          * generalize bwf; simpl; rewrite andb_true_iff; intuition.
          * {
              apply (NoDup_domain_lookups_Permutation string_dec).
              - generalize (map_rtype_meet₀_domain (ftype:=ftype) (br:=br)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl1)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl2)); intros eqq.
             rewrite eqq.
             generalize bwf; simpl; rewrite andb_true_iff; intuition eauto 2.
          - generalize bwf; simpl; rewrite andb_true_iff; intuition eauto 2. 
          - intros s.
            {
              case_eq ( lookup string_dec
                               (map
                                  (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                     (fst x, proj1_sig (snd x))) rl1) s); [intros τ srin | intros snin].
              -  case_eq ( lookup string_dec
                               (map
                                  (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                     (fst x, proj1_sig (snd x))) rl2) s); [intros τ2 srin2 | intros s2nin].
                 + generalize (@map_rtype_meet₀_rtype_meets _ _ (map
                                                    (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                       (fst x, proj1_sig (snd x))) rl1)
                                               (map
                                                  (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                     (fst x, proj1_sig (snd x))) rl2) s τ τ2); intros eqq.
                   rewrite eqq; trivial.
                   f_equal.
                   rewrite Forall_forall in H.
                   generalize (H _ (lookup_in _ _ srin2)); simpl; intros eqq2.
                   apply lookup_map_some_ex in srin.
                   apply lookup_map_some_ex in srin2.
                   destruct srin as [pfτ srin].
                   destruct srin2 as [pfτ2 srin2].
                   apply (eqq2 pfτ2 τ pfτ).
                   destruct (H4 _ _ srin2) as [r' [lor subr]].
                   unfold rtype in lor, srin; rewrite lor in srin.
                   inversion srin; subst.
                   trivial.
                 + generalize (@map_rtype_meet₀_some_none _ _ (map
                                                    (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                       (fst x, proj1_sig (snd x))) rl1)
                                               (map
                                                  (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                     (fst x, proj1_sig (snd x))) rl2) s τ); intros eqq.
                   rewrite eqq; trivial.
                   - generalize (@map_rtype_meet₀_none _ _ (map
                                                      (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                         (fst x, proj1_sig (snd x))) rl1)
                                                 (map
                                                    (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                                                       (fst x, proj1_sig (snd x))) rl2) s); intros eqq.
                   rewrite eqq; trivial.
            }
            }
        + simpl.
          generalize (map_rtype_meet₀_domain (ftype:=ftype) (br:=br)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl1)
                  (map
              (fun x : string * {τ₀ : rtype₀ | wf_rtype₀ τ₀ = true} =>
                 (fst x, proj1_sig (snd x))) rl2)); intros eqq.
          rewrite eqq.
          generalize bwf; simpl; rewrite andb_true_iff; intuition eauto 2.
      - unfold domain in *.
        repeat rewrite map_map; simpl.
        apply incl21.
      }
    + destruct k; destruct k1; simpl in *.
      * intuition. 
      * elim n.
        unfold domain; repeat rewrite map_map; simpl.
        apply subl21.
      * intuition; discriminate.
      * elim n.
        generalize awf bwf; simpl.
       repeat rewrite andb_true_iff.
       unfold domain; repeat rewrite map_map; simpl; intros [??] [??].
        { apply sublist_antisymm.
          - apply subl21.
          - apply Sorted_incl_sublist.
            + apply (is_list_sorted_Sorted_iff StringOrder.lt_dec); auto.
            +  apply (is_list_sorted_Sorted_iff StringOrder.lt_dec); auto.
            + intuition.
        }
      }
  - destruct (Either₀_wf_inv awf).
    repeat rewrite rtype_join₀_idempotent; trivial.
    repeat rewrite rtype_meet₀_idempotent; trivial.
    tauto.
  - destruct (Either₀_wf_inv awf) as [l1wf r1wf].
    destruct (Either₀_wf_inv bwf) as [l2wf r2wf].
    inversion H; subst; rtype_equalizer; subst.
    + repeat rewrite rtype_join₀_idempotent; trivial.
      repeat rewrite rtype_meet₀_idempotent; trivial.
      tauto.
    + subst. repeat split; f_equal.
      * apply (IHa1 l1wf _ l2wf).
        destruct l1; destruct l2; simpl in *.
        eapply subtype_ext; eauto.
      * apply (IHa2 r1wf _ r2wf).
        destruct r1; destruct r2; simpl in *.
        eapply subtype_ext; eauto.
      * apply (IHa1 l1wf _ l2wf).
        destruct l1; destruct l2; simpl in *.
        eapply subtype_ext; eauto.
      * apply (IHa2 r1wf _ r2wf).
        destruct r1; destruct r2; simpl in *.
        eapply subtype_ext; eauto.
  - destruct (Either₀_wf_inv awf).
    repeat rewrite rtype_join₀_idempotent; trivial.
    repeat rewrite rtype_meet₀_idempotent; trivial.
    tauto.
  - destruct (Either₀_wf_inv awf) as [l1wf r1wf].
    destruct (Either₀_wf_inv bwf) as [l2wf r2wf].
    inversion H; subst; rtype_equalizer; subst.
    + repeat rewrite rtype_join₀_idempotent; trivial.
      repeat rewrite rtype_meet₀_idempotent; trivial.
      tauto.
    + subst. repeat split; f_equal.
      * apply (IHa1 l1wf _ l2wf).
        destruct l1; destruct l2; simpl in *.
        eapply subtype_ext; eauto.
      * apply (IHa2 r1wf _ r2wf).
        destruct r1; destruct r2; simpl in *.
        eapply subtype_ext; eauto.
      * apply (IHa1 l1wf _ l2wf).
        destruct l1; destruct l2; simpl in *.
        eapply subtype_ext; eauto.
      * apply (IHa2 r1wf _ r2wf).
        destruct r1; destruct r2; simpl in *.
        eapply subtype_ext; eauto.
  - destruct (Arrow₀_wf_inv awf).
    repeat rewrite rtype_join₀_idempotent; trivial.
    repeat rewrite rtype_meet₀_idempotent; trivial.
    tauto.
  - destruct (Arrow₀_wf_inv awf) as [l1wf r1wf].
    destruct (Arrow₀_wf_inv bwf) as [l2wf r2wf].
    inversion H; subst; rtype_equalizer; subst.
    + repeat rewrite rtype_join₀_idempotent; trivial.
      repeat rewrite rtype_meet₀_idempotent; trivial.
      tauto.
    + subst. repeat split; f_equal.
      * rewrite rtype_meet₀_commutative by trivial.
        apply (IHa1 l1wf _ l2wf).
        destruct in1; destruct in2; simpl in *.
        eapply subtype_ext; eauto.
      * apply (IHa2 r1wf _ r2wf).
        destruct out1; destruct out2; simpl in *.
        eapply subtype_ext; eauto.
      * rewrite rtype_join₀_commutative by trivial.
        apply (IHa1 l1wf _ l2wf).
        destruct in1; destruct in2; simpl in *.
        eapply subtype_ext; eauto.
      * apply (IHa2 r1wf _ r2wf).
        destruct out1; destruct out2; simpl in *.
        eapply subtype_ext; eauto.
  - destruct (Arrow₀_wf_inv awf).
    repeat rewrite rtype_join₀_idempotent; trivial.
    repeat rewrite rtype_meet₀_idempotent; trivial.
    tauto.
  - destruct (Arrow₀_wf_inv awf) as [l1wf r1wf].
    destruct (Arrow₀_wf_inv bwf) as [l2wf r2wf].
    inversion H; subst; rtype_equalizer; subst.
    + repeat rewrite rtype_join₀_idempotent; trivial.
      repeat rewrite rtype_meet₀_idempotent; trivial.
      tauto.
    + subst. repeat split; f_equal.
      * rewrite rtype_meet₀_commutative by trivial.
        apply (IHa1 l1wf _ l2wf).
        destruct in1; destruct in2; simpl in *.
        eapply subtype_ext; eauto.
      * apply (IHa2 r1wf _ r2wf).
        destruct out1; destruct out2; simpl in *.
        eapply subtype_ext; eauto.
      * rewrite rtype_join₀_commutative by trivial.
        apply (IHa1 l1wf _ l2wf).
        destruct in1; destruct in2; simpl in *.
        eapply subtype_ext; eauto.
      * apply (IHa2 r1wf _ r2wf).
        destruct out1; destruct out2; simpl in *.
        eapply subtype_ext; eauto.
  - rewrite brand_join_idempotent_can; trivial.
    rewrite brand_meet_idempotent_can; trivial.
    tauto.
    apply wf_rtype₀_Brand₀; trivial.
    apply wf_rtype₀_Brand₀; trivial.
  - f_equal.
    rewrite brand_join_canon_l, brand_join_canon_r.
    rewrite brand_meet_canon_l, brand_meet_canon_r.
    split; f_equal.
    + apply brand_join_consistent; trivial.
    + apply brand_meet_consistent; trivial.
  - rewrite brand_join_idempotent_can; trivial.
    rewrite brand_meet_idempotent_can; trivial.
    tauto.
    apply wf_rtype₀_Brand₀; trivial.
    apply wf_rtype₀_Brand₀; trivial.
  - f_equal.
    rewrite brand_join_canon_l, brand_join_canon_r.
    rewrite brand_meet_canon_l, brand_meet_canon_r.
    split; f_equal.
    + apply brand_join_consistent; trivial.
    + apply brand_meet_consistent; trivial.
  - rewrite join_idempotent.
    rewrite meet_idempotent.
    tauto.
  - split.
    + apply consistent_join in H2.
      congruence.
    + apply consistent_meet in H2.
      congruence.
  - rewrite join_idempotent.
    rewrite meet_idempotent.
    tauto.
  - split.
    + apply consistent_join in H2.
      congruence.
    + apply consistent_meet in H2.
      congruence.
      Grab Existential Variables.
      solve[eauto].
      solve[eauto].
Qed.

Corollary consistent_rtype_join1:
    forall a b, subtype a b -> rtype_join a b = b.
Proof.
  intros; apply consistent_rtype_join_meet1; trivial.
Qed.

Corollary consistent_rtype_meet1:
    forall a b, subtype a b -> rtype_meet a b = a.
Proof.
  intros; apply consistent_rtype_join_meet1; trivial.
Qed.

Lemma consistent_rtype_join_meet2:
  forall a b,  (rtype_join a b = b -> subtype a b)
               /\ (rtype_meet a b = a -> subtype a b).
Proof.
  Hint Resolve STop₀ SBottom₀ SColl₀.
  destruct a as [a awf]; destruct b as [b bwf].
  unfold rtype_join, rtype_meet; simpl.

  cut ((rtype_join₀ a b = b ->
        exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) a awf <:
          exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) b bwf)
       /\ (rtype_meet₀ a b = a ->
           exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) a awf <:
             exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) b bwf)
       /\ (rtype_join₀ b a = a ->
           exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) b bwf <:
             exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) a awf)
       /\ (rtype_meet₀ b a = b ->
           exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) b bwf <:
             exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) a awf)).
  { split; inversion 1; intuition. }
  revert awf b bwf.
  induction a; try solve[
                     intuition;
                     inversion H;
                     destruct b; try discriminate;
                     eapply subtype_ext; eauto 3].
  - intuition; simpl in *; inversion H; destruct b; try discriminate;
      try solve [eapply subtype_ext; eauto];
      simpl in *;
        inversion H;
      repeat rewrite Coll_canon;
      econstructor;
      destruct (IHa awf b bwf) as [pf1 [pf2 [pf3 pf4]]];
      intuition.
  - repeat split.
    + destruct b; unfold rtype_join₀; simpl; fold rtype_join₀; inversion 1; eauto 2.
      clear H0.
      apply SRec₀;
        [| intros rc; apply record_kind_rtype_join_closed_inv in rc; intuition; congruence].
      simpl in *.
  clear H2 k0.
  revert H awf srl bwf H3. 
  induction r; intros X awf srl bwf eqsrl s r' pf' los;
  [subst; simpl in los; discriminate|].
  destruct a. inversion X. subst x l.
  clear X. specialize (IHr H2 (wf_rtype₀_cons_tail (k:=k) awf)).
  case_eq (string_dec s s0); intros seq seqpf;
    simpl; rewrite seqpf.
    subst s0.
    assert (r0pf: wf_rtype₀ r0 = true)
     by (simpl in awf; repeat rewrite andb_true_iff in awf; intuition).
    exists r0, r0pf. intuition.
    destruct (H1 r0pf _ pf') as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
    apply Hpf1. simpl.
    rewrite los in eqsrl.
    destruct srl; inversion eqsrl.
    destruct p; simpl in *.
    inversion H0; subst s0 r1.
    rewrite seqpf in los.
    simpl in * .
    inversion los; congruence.
  case_eq (lookup string_dec srl s0); [intros r0' r0'in | intros r0'in];
      rewrite r0'in in eqsrl; eauto.
    destruct srl; inversion eqsrl.
    destruct p; inversion H0.
    subst s1 r1.
    simpl in r0'in,los.
    destruct (string_dec s0 s0); try congruence.
    destruct (string_dec s s0); try congruence.
    clear e. inversion r0'in. clear H0 r0'in; rename H4 into r0'eq.
    clear eqsrl. rename H3 into eqsrl.
    rewrite r0'eq in eqsrl. rewrite r0'eq in bwf.
    rewrite (map_rtype_join₀_commutative Closed Closed (ftype:=ftype) (br:=br)) in eqsrl; auto; 
    [| eapply wf_rtype₀_cons_tail; eauto].
    generalize (wf_rtype₀_cons_nin (k:=k) awf); intros nin.
    generalize (wf_rtype₀_cons_lt bwf los (k:=Closed)); intros s0lt.
    rewrite nin in eqsrl.
    generalize (wf_rtype₀_cons_tail (k:=k) awf).
    generalize (wf_rtype₀_cons_tail bwf (k:=Closed)).
    intros.
    rewrite (map_rtype_join₀_commutative Closed Closed (ftype:=ftype) (br:=br)) in eqsrl; auto.
    eauto.
    + destruct b; unfold rtype_meet₀; simpl; fold rtype_meet₀; inversion 1; eauto 2.
      clear H2.
    match_destr_in H0.
    inversion H0; clear H0.
    { apply SRec₀.
    + { intros s τ pfτ los.
        assert (ndr:NoDup (domain r))
               by (generalize awf bwf; simpl; repeat rewrite andb_true_iff; intros [??] [??];
                   intuition eauto 2).
        assert (ndsrl:NoDup (domain srl))
               by (generalize awf bwf; simpl; repeat rewrite andb_true_iff; intros [??] [??];
                   intuition eauto 2).
        case_eq (lookup string_dec r s).
        - intros τ2 lors.
          generalize lors; intros lors'.
          rewrite <- H3 in lors.
          generalize (map_rtype_meet₀_domain_rec_concat_sort r srl); intros eqq.
          rewrite eqq in lors; clear eqq; trivial.
          rewrite lookup_app in lors.
            generalize (@map_rtype_meet₀_rtype_meets _ _ r srl s _ _ lors' los); intros eqq.
            rewrite eqq in lors; clear eqq.
            inversion lors; clear lors.
            generalize (lookup_in _ _ lors'); intros inrs.
            assert (pfτ2: wf_rtype₀ τ2 = true).
            { simpl in awf; rewrite andb_true_iff in awf; rewrite forallb_forall in awf.
              destruct awf as [? fawf]. apply (fawf _ inrs). }
            exists τ2; exists pfτ2.
            rewrite H1. split; trivial.
            rewrite Forall_forall in H.
            destruct (H _ inrs pfτ2 _ pfτ) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]]; simpl; eauto.
        - intros lors.
          generalize lors; intros lors'.
          rewrite <- H3 in lors.
          generalize (map_rtype_meet₀_domain_rec_concat_sort r srl); intros eqq.
          rewrite eqq in lors; clear eqq; trivial.
          rewrite lookup_app in lors.
            generalize (@map_rtype_meet₀_none _ _ r srl s lors'); intros eqq.
            rewrite eqq in lors; clear eqq.
            rewrite lookup_diff_none2 in lors
              by trivial.
            congruence.
      }
    + destruct k0; [ intros; discriminate | ].
      destruct k; simpl in *; [ discriminate | ].
      rewrite r0; intuition.
    }
    + destruct b; unfold rtype_join₀; simpl; fold rtype_join₀; inversion 1; eauto 2.
      clear H0.
      apply SRec₀;
        [| intros rc; apply record_kind_rtype_join_closed_inv in rc; intuition; congruence].
      simpl in *.
  clear H2 k0.
  revert H awf srl bwf H3. 
  induction r; intros X awf srl bwf eqsrl s r' pf' los;
  [subst; simpl in los; discriminate|].
  destruct a. inversion X. subst x l.
  clear X. specialize (IHr H2 (wf_rtype₀_cons_tail (k:=k) awf)).
  simpl in los.
  simpl.
  case_eq (lookup string_dec srl s0); [intros r0' r0'in | intros r0'in].
      * generalize (@map_rtype_join₀_lookup_some2 _ _ _ r s0 r0' r0 r0'in); intros eqq1.
        { rewrite eqq1 in eqsrl.
          - inversion eqsrl; clear eqsrl.
            clear eqq1.
            case_eq (string_dec s s0); intros seq seqpf;
              rewrite seqpf in los.
            + inversion los; clear los; subst r0 s0.
              simpl in H1.
              assert (r0'pf: wf_rtype₀ r0' = true).
              * simpl in bwf; repeat rewrite andb_true_iff in bwf; intuition.
                rewrite forallb_forall in H4.
                apply (H4 _ (lookup_in _ _ r0'in)).
              * exists r0', r0'pf.
                split; trivial.
                destruct (H1 pf' _ r0'pf) as [?[?[??]]]; auto.
            + apply IHr; trivial.
          - rewrite andb_true_iff in *; intuition.
          - rewrite andb_true_iff in*; intuition.
        }
      * apply (f_equal domain) in eqsrl.
        assert (inn:In s0 (domain ((s0,r0)::r))) by (simpl; tauto).
        rewrite <- eqsrl in inn.
        generalize (map_rtype_join₀_domain_subset srl ((s0,r0)::r) s0); intros eqq1.
        apply eqq1 in inn.
        apply lookup_none_nin in r0'in.
        intuition.
    + destruct b; unfold rtype_meet₀; simpl; fold rtype_meet₀; inversion 1; eauto 2.
      clear H2.
    match_destr_in H0.
    inversion H0; clear H0.
    { apply SRec₀.
    + { intros s τ pfτ los.
        assert (ndr:NoDup (domain r))
               by (generalize awf bwf; simpl; repeat rewrite andb_true_iff; intros [??] [??];
                   intuition eauto 2).
        assert (ndsrl:NoDup (domain srl))
               by (generalize awf bwf; simpl; repeat rewrite andb_true_iff; intros [??] [??];
                   intuition eauto 2).
        case_eq (lookup string_dec srl s).
        - intros τ2 lors.
          generalize lors; intros lors'.
          rewrite <- H3 in lors.
          generalize (map_rtype_meet₀_domain_rec_concat_sort srl r s); intros eqq.
          rewrite eqq in lors; clear eqq; trivial.
          rewrite lookup_app in lors.
          generalize (@map_rtype_meet₀_rtype_meets _ _ srl r s _ _ lors' los); intros eqq.
            rewrite eqq in lors; clear eqq.
            inversion lors; clear lors.
            generalize (lookup_in _ _ lors'); intros inrs.
            assert (pfτ2: wf_rtype₀ τ2 = true).
            { simpl in bwf; rewrite andb_true_iff in bwf; rewrite forallb_forall in bwf.
              destruct bwf as [? fbwf]. apply (fbwf _ inrs). }
            exists τ2; exists pfτ2.
            rewrite H1. split; trivial.
            rewrite Forall_forall in H.
            destruct (H _ (lookup_in _ _ los) pfτ _ pfτ2) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]]; simpl; eauto.
        - intros lors.
          generalize lors; intros lors'.
          rewrite <- H3 in lors.
          generalize (map_rtype_meet₀_domain_rec_concat_sort srl r); intros eqq.
          rewrite eqq in lors; clear eqq; trivial.
          rewrite lookup_app in lors.
          generalize (@map_rtype_meet₀_none _ _ srl r s lors'); intros eqq.
          rewrite eqq in lors; clear eqq.
          rewrite lookup_diff_none2 in lors
            by trivial.
            congruence.
      }
    + destruct k; [ intros; discriminate | ].
      destruct k0; simpl in *; [ discriminate | ].
      rewrite r0; intuition.
    }
  - simpl. intros.
    destruct b; repeat split; try discriminate; eauto 2.
    + intros.
      destruct (Either₀_wf_inv awf) as [a1wf a2wf].
      destruct (Either₀_wf_inv bwf) as [b1wf b2wf].
      inversion H; clear H.
      rewrite (Either_canon _ _ _ a1wf a2wf).
      rewrite (Either_canon _ _ _ b1wf b2wf).
      constructor.
      * destruct (IHa1 a1wf _ b1wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
      * destruct (IHa2 a2wf _ b2wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
    + intros.
      destruct (Either₀_wf_inv awf) as [a1wf a2wf].
      destruct (Either₀_wf_inv bwf) as [b1wf b2wf].
      inversion H; clear H.
      rewrite (Either_canon _ _ _ a1wf a2wf).
      rewrite (Either_canon _ _ _ b1wf b2wf).
      constructor.
      * destruct (IHa1 a1wf _ b1wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
      * destruct (IHa2 a2wf _ b2wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
    + intros.
      destruct (Either₀_wf_inv awf) as [a1wf a2wf].
      destruct (Either₀_wf_inv bwf) as [b1wf b2wf].
      inversion H; clear H.
      rewrite (Either_canon _ _ _ a1wf a2wf).
      rewrite (Either_canon _ _ _ b1wf b2wf).
      constructor.
      * destruct (IHa1 a1wf _ b1wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
      * destruct (IHa2 a2wf _ b2wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
    + intros.
      destruct (Either₀_wf_inv awf) as [a1wf a2wf].
      destruct (Either₀_wf_inv bwf) as [b1wf b2wf].
      inversion H; clear H.
      rewrite (Either_canon _ _ _ a1wf a2wf).
      rewrite (Either_canon _ _ _ b1wf b2wf).
      constructor.
      * destruct (IHa1 a1wf _ b1wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
      * destruct (IHa2 a2wf _ b2wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
  - simpl. intros.
    destruct b; unfold rtype_meet₀, rtype_join₀; simpl; fold rtype_meet₀; fold rtype_join₀; repeat split; try discriminate; eauto 2.
    + intros.
      destruct (Arrow₀_wf_inv awf) as [a1wf a2wf].
      destruct (Arrow₀_wf_inv bwf) as [b1wf b2wf].
      inversion H; clear H.
      rewrite (Arrow_canon _ _ _ a1wf a2wf).
      rewrite (Arrow_canon _ _ _ b1wf b2wf).
      constructor.
      * rewrite rtype_meet₀_commutative in H1; trivial.
        destruct (IHa1 a1wf _ b1wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
      * destruct (IHa2 a2wf _ b2wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
    + intros.
      destruct (Arrow₀_wf_inv awf) as [a1wf a2wf].
      destruct (Arrow₀_wf_inv bwf) as [b1wf b2wf].
      inversion H; clear H.
      rewrite (Arrow_canon _ _ _ a1wf a2wf).
      rewrite (Arrow_canon _ _ _ b1wf b2wf).
      constructor.
      * rewrite rtype_join₀_commutative in H1; trivial.
        destruct (IHa1 a1wf _ b1wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
      * destruct (IHa2 a2wf _ b2wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
    + intros.
      destruct (Arrow₀_wf_inv awf) as [a1wf a2wf].
      destruct (Arrow₀_wf_inv bwf) as [b1wf b2wf].
      inversion H; clear H.
      rewrite (Arrow_canon _ _ _ a1wf a2wf).
      rewrite (Arrow_canon _ _ _ b1wf b2wf).
      constructor.
      * rewrite rtype_meet₀_commutative in H1; trivial.
        destruct (IHa1 a1wf _ b1wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
      * destruct (IHa2 a2wf _ b2wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
    + intros.
      destruct (Arrow₀_wf_inv awf) as [a1wf a2wf].
      destruct (Arrow₀_wf_inv bwf) as [b1wf b2wf].
      inversion H; clear H.
      rewrite (Arrow_canon _ _ _ a1wf a2wf).
      rewrite (Arrow_canon _ _ _ b1wf b2wf).
      constructor.
      * rewrite rtype_join₀_commutative in H1; trivial.
        destruct (IHa1 a1wf _ b1wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
      * destruct (IHa2 a2wf _ b2wf) as [Hpf1 [Hpf2 [Hpf3 Hpf4]]].
        intuition.
  - simpl; intros.
    destruct b0; unfold rtype_meet₀, rtype_join₀; simpl; fold rtype_meet₀; fold rtype_join₀; repeat split; try discriminate; eauto 2.
    + inversion 1.
      repeat rewrite brand_ext.
       apply SBrand.
       apply brand_join_consistent_can; trivial.
       apply wf_rtype₀_Brand₀; trivial.
    + inversion 1.
      repeat rewrite brand_ext.
       apply SBrand.
       apply brand_meet_consistent_can; trivial.
       apply wf_rtype₀_Brand₀; trivial.
    + inversion 1.
      repeat rewrite brand_ext.
       apply SBrand.
       apply brand_join_consistent_can; trivial.
       apply wf_rtype₀_Brand₀; trivial.
    + inversion 1.
      repeat rewrite brand_ext.
       apply SBrand.
       apply brand_meet_consistent_can; trivial.
       apply wf_rtype₀_Brand₀; trivial.
  - simpl; intros.
    destruct b; unfold rtype_meet₀, rtype_join₀; simpl; fold rtype_meet₀; fold rtype_join₀; repeat split; try discriminate; eauto 2.
    + inversion 1.
      repeat rewrite Foreign_canon.
      apply SForeign.
      apply consistent_join.
      congruence.
    + inversion 1.
      repeat rewrite Foreign_canon.
      apply SForeign.
      apply consistent_meet.
      congruence.
    + inversion 1.
      repeat rewrite Foreign_canon.
      apply SForeign.
      apply consistent_join.
      congruence.
    + inversion 1.
      repeat rewrite Foreign_canon.
      apply SForeign.
      apply consistent_meet.
      congruence.
      Grab Existential Variables.
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
       solve[eauto]. solve[eauto]. solve[eauto]. solve[eauto].
Qed.

Corollary consistent_rtype_join2:
  forall a b, rtype_join a b = b -> subtype a b.
Proof.
  intros a b ?.
  destruct (consistent_rtype_join_meet2 a b).
  auto.
Qed.

Corollary consistent_rtype_meet2:
  forall a b, rtype_meet a b = a -> subtype a b.
Proof.
  intros a b ?.
  destruct (consistent_rtype_join_meet2 a b).
  intuition.
Qed.

Theorem consistent_rtype_join: forall a b, subtype a b <-> rtype_join a b = b.
Proof.
  Hint Resolve consistent_rtype_join1 consistent_rtype_join2.
  intuition.
Qed.

  Lemma  rtype_join_subtype_l a b: subtype a (rtype_join a b).
  Proof.    
    rewrite consistent_rtype_join, <- rtype_join_associative, rtype_join_idempotent.
    trivial.
  Qed.

  Lemma  rtype_join_subtype_r a b: subtype b (rtype_join a b).
  Proof.    
    rewrite rtype_join_commutative.
    apply rtype_join_subtype_l.
  Qed.

  Theorem rtype_join_least {a b c} : a <: c -> b <: c -> rtype_join a b <: c.
  Proof.
    intros sub1 sub2.
    rewrite consistent_rtype_join in sub1,sub2.
    rewrite <- sub1, <- sub2.
    rewrite <- rtype_join_associative.
    apply rtype_join_subtype_l.
  Qed.

  (** We can compute if the subtype relation holds using 
       its relationship with rtype_join
       and the computable equality of types *)
  Theorem subtype_dec_rtype_join a b : {a <: b} + {~ a <: b}.
  Proof.
    generalize (consistent_rtype_join a b).
    destruct (rtype_join a b == b); unfold equiv, complement in *; intuition.
  Defined.
 
  Theorem consistent_rtype_meet : forall a b, subtype a b <-> rtype_meet a b = a.
  Proof.
    Hint Resolve consistent_rtype_meet1 consistent_rtype_meet2.
    intuition.
  Qed.
  
  Lemma  rtype_meet_subtype_l a b: subtype (rtype_meet a b) a.
  Proof.    
    rewrite consistent_rtype_meet, rtype_meet_commutative, <- rtype_meet_associative, rtype_meet_idempotent.
    trivial.
  Qed.

  Lemma  rtype_meet_subtype_r a b: subtype (rtype_meet a b) b.
  Proof.    
    rewrite rtype_meet_commutative.
    apply rtype_meet_subtype_l.
  Qed.

  Theorem rtype_meet_most {a b c} : a <: b -> a <: c -> a <: (rtype_meet b c).
  Proof.
    intros sub1 sub2.
    rewrite consistent_rtype_meet in sub1,sub2.
    rewrite <- sub1, <- sub2.
    rewrite rtype_meet_associative.
    rewrite (rtype_meet_commutative c b).
    apply rtype_meet_subtype_r.
  Qed.

  (** We can compute if the subtype relation holds using 
       its relationship with rtype_meet
       and the computable equality of types *)
  Theorem subtype_dec_rtype_meet a b : {a <: b} + {~ a <: b}.
  Proof.
    generalize (consistent_rtype_meet a b).
    destruct (rtype_meet a b == a); unfold equiv, complement in *; intuition.
  Defined.

End rtype_join_meet.

Theorem rtype_join_absorptive: forall a b, rtype_join a (rtype_meet a b) = a.
Proof.
  intros.
  rewrite rtype_join_commutative.
  rewrite <- consistent_rtype_join.
  apply rtype_meet_subtype_l.
Qed.

Theorem rtype_meet_absorptive: forall a b, rtype_meet a (rtype_join a b) = a.
Proof.
  intros.
  rewrite <- consistent_rtype_meet.
  apply rtype_join_subtype_l.
Qed.

End RConsistentSubtype.

