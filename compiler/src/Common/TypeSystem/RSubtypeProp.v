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
Require Import RelationClasses.
Require Import Utils.
Require Import ForeignType.
Require Import RType.
Require Import BrandRelation.
Require Export RSubtype.

Section RSubtypeProp.

Context {ftype:foreign_type}.
Context {m:brand_relation}.

Lemma top_subtype z : ⊤ <: z -> z = ⊤.
Proof.
  inversion 1; subst; eauto.
Qed.

Lemma subtype_bottom z : z <: ⊥ -> z = ⊥.
Proof.
  inversion 1; subst; eauto.
Qed.

Ltac simpl_type :=
  repeat match goal with
      | [H: ?z <: ⊥ |- _] => apply subtype_bottom in H; subst
      | [H: ⊤ <: ?z |- _] => apply top_subtype in H; subst
  end.

Instance subtype_trans : Transitive subtype.
Proof.
  Hint Constructors subtype.
  red.
  intros x y.
  revert x.
  induction y using rtype_rect; intros x z sub1 sub2; inversion sub1; subst; simpl_type; eauto.
  - inversion sub2; subst; eauto.
    rtype_equalizer. subst; eauto.
  - inversion sub2; subst; eauto.
    rtype_equalizer. subst.
    constructor.
    + intros s' r' lsr'.
       destruct (H5 _ _  lsr') as [?[look3 sub3]].
       destruct (H3 _ _ look3) as [?[??]].
       exists x0; intuition.
       generalize (Forallt_In H (s',x)). 
       simpl; intros P; eapply P; eauto.
       apply (lookup_in string_dec); trivial.
    + intuition.
  - inversion sub2; subst; eauto.
    rtype_equalizer. subst. eauto.
  - rtype_equalizer. subst.
    inversion sub2; subst; trivial.
    rtype_equalizer. subst.
    econstructor; eauto.
  - inversion sub2; subst; trivial.
    apply canon_equiv in H; apply canon_equiv in H0.
    rewrite H in H1.
    rewrite H0 in H2.
    constructor; etransitivity; eassumption.
  - invcs sub2; trivial.
    econstructor.
    transitivity ft; trivial.
Qed.

Global Instance subtype_pre : PreOrder subtype.
Proof.
  constructor; eauto.
  apply subtype_trans.
Qed.

Lemma Rec_subtype_cons_weaken k s r l₁ pf pf2: 
  Rec k ((s, r) :: l₁) pf <: Rec Open l₁ pf2.
Proof.
  apply SRec_open; intros.
  simpl.
  case_eq (string_dec s0 s); [intros ? ?; subst | eauto].
  assert False; [|intuition].
  rewrite domain_cons in pf.
  apply is_list_sorted_NoDup in pf; [|apply StringOrder.lt_strorder].
  inversion pf; subst. elim H3. 
  eapply in_dom; eapply lookup_in; eauto.
Qed.

Lemma Rec_subtype_cons_inv2 {k1 k2 s r l₁ l₂ pf pf2}: 
  Rec k1 l₁ pf <: Rec k2 ((s, r) :: l₂) pf2 ->
       exists pf', 
         Rec k1 l₁ pf <: Rec Open l₂ pf'.
Proof.
  intros sub.
  generalize pf2.
  rewrite domain_cons, is_list_sorted_cons.
  intros [pf' _].
  rewrite (Rec_subtype_cons_weaken k2 s r l₂ pf2 pf') in sub.
  eauto.
Qed.

Lemma Rec_subtype_cons_inv1_open {k1 k2 s r l₁ l₂ pf pf2}: 
  Rec k1 ((s, r) :: l₁) pf <: Rec k2 l₂ pf2 ->
     lookup string_dec l₂ s = None ->
     k2 = Open.
Proof.
  intro rt.
  destruct k2; trivial.
  intros lo.
  apply lookup_none_nin in lo.
  elim lo.
  generalize (SRec_closed_equiv_domain rt); intros inns.
  simpl in inns.
  destruct (inns s).
  apply H; intuition.
Qed.

Lemma Rec_subtype_cons_inv1 {k1 k2 s r l₁ l₂ pf pf2}: 
  Rec k1 ((s, r) :: l₁) pf <: Rec k2 l₂ pf2 ->
    lookup string_dec l₂ s = None ->
       exists pf', 
         Rec k1 l₁ pf' <: Rec Open l₂ pf2.
Proof.
  intros rt lo.
  generalize (Rec_subtype_cons_inv1_open rt lo); intros; subst.
  inversion rt; subst; rtype_equalizer.
  - destruct l₂; simpl in H2; try discriminate.
    inversion H2; subst. rtype_equalizer.
    subst. destruct p; simpl in *.
    destruct (string_dec s s); intuition congruence.
  - subst. destruct rl1; simpl in H0; try discriminate.
    inversion H0; rtype_equalizer. subst.
    destruct p; simpl in lo |- *.
    generalize pf.
    rewrite domain_cons, is_list_sorted_cons; simpl.
    intros [pf' _].
    exists pf'.
    apply SRec_open; intros s0 r0 ls0.
    specialize (H2 _ _ ls0); simpl in H2.
    destruct (string_dec s0 s); eauto.
    destruct H2 as [? [inv _]].
    inversion inv; subst. congruence.
Qed.

(** Note that unlike the biased inverses, since we are removing 
     an element from both sides, it is possible for k2 to be Closed *)
Lemma Rec_subtype_cons_inv {k1 k2 s r1 r2 l₁ l₂ pf pf2}: 
  Rec k1 ((s, r1) :: l₁) pf <: Rec k2 ((s, r2) :: l₂) pf2 ->
  exists pf' pf2', 
    Rec k1 l₁ pf' <: Rec k2 l₂ pf2'.
Proof.
  intros rt.
  inversion rt; subst; rtype_equalizer; subst.
  - repeat (exists (is_list_sorted_cons_inv _ pf)). reflexivity.
  - destruct rl1; simpl in H0; try discriminate.
    destruct rl2; simpl in H3; try discriminate.
    inversion H0; inversion H3; clear H0; clear H3.
    rtype_equalizer. subst.
    exists (is_list_sorted_cons_inv _ pf).
    exists (is_list_sorted_cons_inv _ pf2).
    generalize (is_list_sorted_NoDup ODT_lt_dec _ pf).
    generalize (is_list_sorted_NoDup ODT_lt_dec _ pf2).
    intros.
    constructor.
    + intros. 
      specialize (H2 s r').
      simpl in H2.
      destruct p; destruct p0; simpl in *; subst.
      destruct (string_dec s s0).
      * inversion H; subst.
        apply lookup_in in H1.
        apply in_dom in H1.
        intuition.
      * auto.
    + intuition; subst.
       destruct p; destruct p0; simpl in *; subst.
       specialize (H5 s). intuition.
       inversion H0; subst.
       intuition.
Qed.

Global Instance subtype_part : PartialOrder eq subtype.
Proof.
  unfold PartialOrder, relation_equivalence, predicate_equivalence,
    relation_conjunction, predicate_intersection, Basics.flip; simpl.
  split; intros; subst; intuition.
  revert x0 H0 H1.
  induction x using rtype_rect; intros y sub1 sub2;
  simpl_type; trivial;
  inversion sub1; subst; simpl_type; trivial.
  - f_equal. inversion sub2; subst;
      rtype_equalizer.
    + subst; eauto.
    + subst; eauto.
  - rtype_equalizer; subst.
    intros.
    apply rtype_fequal; simpl.
    inversion sub2; rtype_equalizer; subst; try apply Rec_pr_irrel; auto 1.
    f_equal; [ destruct k; destruct k2; intuition | ].
    f_equal.
    apply Forall2_eq.
    assert (deq:domain srl = domain rl2) by
     (eapply (@Sorted_incl_both_eq _ StringOrder.lt);
     [ apply string_eqdec
     | apply StringOrder.lt_strorder
     | eapply is_list_sorted_Sorted_iff; eauto
     | eapply is_list_sorted_Sorted_iff; eauto
     | apply (SRec_closed_in_domain sub2)
     | apply (SRec_closed_in_domain sub1)]).
    revert k k2 rl2 pf2 H sub1 sub2 H2 H4 H5 H7 deq.
    induction srl; destruct rl2; trivial; intros.
    + destruct p. 
      generalize (H2 s r); simpl.
      destruct (string_dec s s); intuition.
      destruct H1; intuition; discriminate.
    + destruct a. 
      generalize (H5 s r); simpl.
      destruct (string_dec s s); intuition.
      destruct H1; intuition; discriminate.
    + inversion H; subst. destruct a; destruct p.
       simpl in deq. inversion deq; subst; clear deq.
       simpl in H3.
       specialize (H3 r0).
       specialize (H5 s0 r); specialize (H2 s0 r0).
       simpl in H2, H5.
       destruct (string_dec s0 s0); intuition.
       destruct H0 as [? [eq1 su1]].
       destruct H1 as [? [eq2 su2]].
       inversion eq1; inversion eq2; subst.
       intuition; subst.
       
       constructor; trivial.
       destruct (Rec_subtype_cons_inv sub1) as [pf'11 [pf'12 sub'1]].
       destruct (Rec_subtype_cons_inv sub2) as [pf'21 [pf'22 sub'2]].
       eapply (IHsrl (is_list_sorted_cons_inv _ pf) k k2); trivial.
        * erewrite (Rec_pr_irrel); eauto.
        * erewrite (Rec_pr_irrel _ _ pf'12).
          erewrite (Rec_pr_irrel _ _ (is_list_sorted_cons_inv ODT_lt_dec pf)).
          eauto.
        * inversion sub'1; rtype_equalizer; subst; eauto.
        * inversion sub'1; rtype_equalizer; subst; eauto.
        * inversion sub'2; rtype_equalizer; subst; eauto.
        * inversion sub'2; rtype_equalizer; subst; eauto.
  - inversion sub2; subst; trivial;
    rtype_equalizer; subst; trivial.
    subst. f_equal; eauto.
  - inversion sub2; subst; trivial;
    rtype_equalizer; subst; trivial.
    subst. f_equal; eauto.
  - apply canon_equiv in H. rewrite H in H0.
    apply rtype_fequal; simpl.
    f_equal. apply canon_equiv. split; trivial.
    inversion sub2; subst; trivial.
    + apply canon_equiv in H3. destruct H3; trivial.
    + apply canon_equiv in H1. apply canon_equiv in H2.
      rewrite <- H1, <- H2; trivial.
  - invcs sub2; trivial.
    f_equal.
    apply foreign_type_sub_part; split; trivial.
Qed.

Lemma wf_rtype_subtype_refl τ pf1 pf2:
  exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) τ pf1 <:
  exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) τ pf2.
Proof.
  generalize (wf_rtype₀_ext pf1 pf2); intros s.
  subst. reflexivity.
Qed.

Lemma Rec_subtype_cons_eq {k₁ k₂ s r₁ r₂ rl₁ rl₂ pf1 pf2}  :
      Rec k₁ ((s, r₁) :: rl₁) pf1 <: Rec k₂ ((s, r₂) :: rl₂) pf2 ->
                                  r₁ <: r₂.
Proof.
  inversion 1; subst; rtype_equalizer.
  subst; intros. reflexivity.
  destruct rl1; try discriminate.
  destruct rl2; try discriminate.
  destruct p; destruct p0.
  simpl in H1, H4.
  inversion H1; subst.
  inversion H4; subst.
  rtype_equalizer. subst.
  specialize (H3 s r₂).
  simpl in H3.
  destruct (string_dec s s); intuition.
  destruct H0 as [? [inv sub]].
  inversion inv; subst.
  auto.
Qed.

Lemma STop₀ pf τ : τ <: exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) ⊤₀ pf.
Proof.
  generalize (STop τ).
  destruct τ; unfold Top; intros.
  eapply subtype_ext; eauto.
Qed.

Lemma SBottom₀ pf τ : exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) ⊥₀ pf <: τ.
Proof.
  generalize (SBottom τ).
  destruct τ; unfold Top; intros.
  eapply subtype_ext; eauto.
Qed.

Lemma SRefl₀ τ₀ pf : exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) τ₀ pf <: exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) τ₀ pf.
Proof.
  apply SRefl.
Qed.

Lemma SColl₀ τ₁ pf₁ τ₂ pf₂ : 
   exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) τ₁ pf₁ <: exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) τ₂ pf₂ ->
   exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ τ₁) pf₁ <: exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Coll₀ τ₂) pf₂.
Proof.
  apply SColl.
Qed.

Lemma SRec₀ k1 rl1 rl2 k2 pf1 pf2 : (forall s r' pf',
                      lookup string_dec rl2 s = Some r' -> 
                      exists r pf, lookup string_dec rl1 s = Some r /\
                                   subtype (exist _ r pf) (exist _ r' pf')) ->
                                    (k2 = Closed -> k1 = Closed /\ 
                                 (forall s, In s (domain rl1) -> In s (domain rl2))) ->
exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Rec₀ k1 rl1) pf1 <:
exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Rec₀ k2 rl2) pf2.
Proof.
  intros.
  destruct (from_Rec₀ rl1 pf1) as [l1' [pf1' [eq11 eq12]]].
  destruct (from_Rec₀ rl2 pf2) as [l2' [pf2' [eq21 eq22]]].
  subst.
  rewrite <- eq12, <- eq22.
  apply SRec.
  intros.
  apply lookup_map_some in H1.
  destruct (H s _ (proj2_sig r') H1) as [r [rpf [l1 s1]]].
  exists (exist _ r rpf).
  split.
    apply lookup_map_some; simpl. auto.
    destruct r'; simpl in *; auto.

    intuition.
    specialize (H3 s).
    unfold domain in H3; repeat rewrite map_map in H3.
    simpl in H3.
    auto.
Qed.

Lemma subtype_Rec_sublist {k₁ l₁ pf₁ k₂ l₂ pf₂} :
  Rec k₁ l₁ pf₁ <: Rec k₂ l₂ pf₂ -> sublist (domain l₂) (domain l₁).
Proof.
  inversion 1; subst; rtype_equalizer; subst; try reflexivity.
  generalize pf₁ pf₂.
  repeat rewrite sorted_StronglySorted by eapply StrictOrder_Transitive.
  intros.
  eapply StronglySorted_incl_sublist; eauto.
  eapply SRec_closed_in_domain; eauto.
Qed.


Lemma subtype_Rec_closed_domain {k₁ l₁ pf₁ l₂ pf₂} :
  Rec k₁ l₁ pf₁ <: Rec Closed l₂ pf₂ -> (domain l₂) = (domain l₁).
Proof.
  intros sub.
  apply Sorted_incl_both_eq; try eapply is_list_sorted_Sorted_iff; eauto
  ;  intros; eapply (SRec_closed_equiv_domain sub); trivial.
Qed.

Lemma subtype_Rec_closed2_closed1 {k1 l1 pf1 l2 pf2}:
  Rec k1 l1 pf1 <: Rec Closed l2 pf2 ->
                   k1 = Closed.
Proof.
  inversion 1; subst; intuition.
Qed.

  Lemma is_list_sorted_in_cons_lookup_none {B} {b τ₃ s} (τ₁:B) {rl0 rl1 τ₀} (τ₂:B) 
   (pf1 : is_list_sorted ODT_lt_dec (domain ((b, τ₃) :: rl1)) = true)
   (x : is_list_sorted ODT_lt_dec (domain ((s, τ₁) :: rl0)) = true)
   (inn:In (b, τ₀) rl0) :
    lookup string_dec ((b, τ₂) :: rl1) s = None.
  Proof.
    apply (sorted_cons_in _ _ _ x) in inn.
    simpl in inn.
    assert (isl:is_list_sorted ODT_lt_dec (s::domain ((b, τ₃) :: rl1)) = true) by (apply is_list_sorted_cons; intuition).
    apply is_list_sorted_NoDup in isl; try eapply StringOrder.lt_strorder.
    inversion isl; subst.
    apply lookup_nin_none.
    rewrite domain_cons; trivial.
 Qed.
    
  Lemma Rec_subtype_In  {rl0 pf0 rl1 pf1 b τ₁ τ₂} :
   Rec Open rl0 pf0 <:
   Rec Open rl1 pf1 ->
   In (b, τ₁) rl0 -> In (b, τ₂) rl1 -> τ₁ <: τ₂.
  Proof.
    revert rl0 pf0 pf1 b τ₁ τ₂. induction rl1; [simpl; intuition| ].
    intros.
    destruct rl0; simpl in H1; [intuition |].
    destruct a; destruct p.
    simpl in H0.
    destruct H0.
    - inversion H0; subst; clear H0.
      destruct H1.
      + inversion H0; subst; clear H0.
         eapply Rec_subtype_cons_eq; eauto.
      + apply Rec_subtype_cons_inv2 in H.
         destruct H. eapply (IHrl1 _ _ _ _ _ _ H); simpl; eauto.
    - destruct H1.
      + inversion H1; subst; clear H1.
        apply Rec_subtype_cons_inv1 in H.
        * destruct H as [??].
          revert H0 H. clear.
          revert rl1 b τ₁ τ₂  pf1 x. induction rl0; [simpl; intuition | ].
          intros.  simpl in H0. destruct H0; subst.
            apply Rec_subtype_cons_eq in H; trivial.
            destruct a.
            apply Rec_subtype_cons_inv1 in H.
            destruct H as [??].
            eauto.
            eapply is_list_sorted_in_cons_lookup_none; eauto.
        * eapply is_list_sorted_in_cons_lookup_none; eauto.
      + rewrite  (Rec_subtype_cons_weaken Open s r rl1
                                        pf1 (is_list_sorted_cons_inv _ pf1)) in H.
        apply (IHrl1 _ _ _ b τ₁ τ₂ H); simpl; auto.
  Qed.
  
End RSubtypeProp.

