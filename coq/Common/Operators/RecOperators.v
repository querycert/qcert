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

Section RecOperators.
  Require Import List.
  Require Import ListSet.
  Require Import String.
  Require Import ZArith.
  Require Import Permutation.
  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Program.
  Require Import EquivDec.
  Require Import Bool.
  Require Import Utils.
  Require Import ForeignData.
  Require Import Data.
  Require Import DataLift.

  Context {fdata:foreign_data}.

  Section RecProject.
    Definition rproject {A} (l:list (string*A)) (s:list string) : list (string*A) :=
      filter (fun x => if in_dec string_dec (fst x) s then true else false) l.

    Lemma rproject_nil_l {A} (s:list string) :
      @rproject A [] s = [].
    Proof.
      reflexivity.
    Qed.
  
    Lemma rproject_nil_r {A} (l:list (string*A)) :
      @rproject A l [] = [].
    Proof.
      induction l. reflexivity.
      simpl. apply IHl.
    Qed.

    Lemma rproject_rec_sort_commute {B} (l1:list (string*B)) sl:
      rproject (rec_sort l1) sl = rec_sort (rproject l1 sl).
    Proof.
      unfold rproject.
      apply rec_sort_filter_fst_commute; intros.
      simpl.
      match_destr.
    Qed.

    Lemma rproject_map_fst_same {B C} (f:string*B->string*C) (l:list (string*B)) sl
          (samedom:forall a, In a l -> fst (f a) = fst a) :
      rproject (map f l) sl = map f (rproject l sl).
    Proof.
      induction l; simpl; trivial.
      simpl in samedom.
      destruct (in_dec string_dec (fst (f a)) sl);
        destruct (in_dec string_dec (fst a) sl).
      - rewrite IHl; intuition.
      - rewrite samedom in i; intuition.
      - rewrite <- samedom in i; intuition.
      - rewrite IHl; intuition.
    Qed.
  
    Lemma rproject_app {B} (l1 l2:list (string*B)) sl:
      rproject (l1 ++ l2) sl = (rproject l1 sl) ++ (rproject l2 sl).
    Proof.
      unfold rproject.
      apply filter_app.
    Qed.

    Lemma rproject_rproject  {B} (l:list (string*B)) sl1 sl2:
      rproject (rproject l sl2) sl1 = rproject l (set_inter string_dec sl2 sl1).
    Proof.
      unfold rproject.
      rewrite filter_and; simpl.
      apply filter_ext; intros.
      repeat match_destr; simpl; trivial.
      - specialize (set_inter_intro string_dec (fst x) sl2 sl1); intuition.
      - specialize (set_inter_elim1 string_dec (fst x) sl2 sl1); intuition.
      - specialize (set_inter_elim2 string_dec (fst x) sl2 sl1); intuition.
      - apply set_inter_elim in i; intuition.
    Qed.

    Lemma rproject_Forall2_same_domain {B C} P (l1:list(string*B)) (l2:list (string*C)) ls :
      Forall2 P l1 l2 ->
      domain l1 = domain l2 ->
      Forall2 P (rproject l1 ls) (rproject l2 ls).
    Proof.
      unfold rproject; intros.
      apply filter_Forall2_same; trivial.
      revert H0; clear. revert l2.
      induction l1; destruct l2; simpl; trivial; try discriminate.
      inversion 1.
      rewrite H1.
      match_destr; f_equal; auto.
    Qed.

    Lemma sublist_rproject {A} (l:list(string*A)) sl: sublist (rproject l sl) l.
    Proof.
      induction l; simpl.
      - constructor.
      - match_destr.
        + apply sublist_cons; auto.
        + apply sublist_skip; auto.
    Qed.
  
    Lemma rproject_remove_all {B} s sl (l1:list(string*B)):
      rproject l1 (remove_all s sl) =
      filter (fun x => nequiv_decb s (fst x)) (rproject l1 sl).
    Proof.
      rewrite remove_all_filter.
      induction l1; simpl; trivial.
      rewrite IHl1.
      destruct (in_dec string_dec (fst a) sl); destruct (in_dec string_dec (fst a) (filter (nequiv_decb s) sl)); simpl.
      - apply filter_In in i0. destruct i0 as [inn neq].
        rewrite neq; trivial.
      - match_case; intros eqq.
        elim n. apply filter_In; intuition.
      - apply filter_In in i; intuition.
      - trivial.
    Qed.

    Lemma rec_sort_rproject_remove_all_in {B} s sl l1 l2 :
      In s sl ->
      In s (@domain _ B l2) -> 
      rec_sort (rproject l1 sl ++ l2) = 
      rec_sort (rproject l1 (remove_all s sl) ++ l2).
    Proof.
      intros.
      rewrite rproject_remove_all.
      rewrite (rec_sort_filter_latter_from_former s); trivial.
    Qed.

    Lemma rec_sort_rproject_remove_in {B} s sl l1 l2 :
      In s sl ->
      In s (@domain _ B l2) -> 
      rec_sort (rproject l1 sl ++ l2) = 
      rec_sort (rproject l1 (remove string_dec s sl) ++ l2).
    Proof.
      intros.
      rewrite (rec_sort_rproject_remove_all_in s); trivial.
    Qed.

    Lemma rproject_with_lookup {A} (l1 l2:list (string * A)) (s:list string):
      is_list_sorted ODT_lt_dec (domain l1) = true ->
      is_list_sorted ODT_lt_dec (domain l2) = true ->
      sublist l1 l2 ->
      (forall x, In x s -> assoc_lookupr string_dec l1 x = assoc_lookupr string_dec l2 x) ->
      rproject l1 s = rproject l2 s.
    Proof.
      intros.
      revert l1 H H1 H2; induction l2; simpl; intros.
      - apply sublist_nil_r in H1; subst; simpl; auto 1.
      - destruct a.
        simpl.
        assert (is_list_sorted ODT_lt_dec (domain l2) = true)
          by (apply (@rec_sorted_skip_first string ODT_string _ l2 (s0,a)); assumption).
        specialize (IHl2 H3).
        assert (NoDup (domain ((s0,a)::l2)))
          by (apply is_list_sorted_NoDup_strlt; assumption).
        generalize (sublist_cons_inv' H1 H4); intros.
        elim H5; clear H5; intros.
        + elim H5; clear H5; intros.
          elim H5; clear H5; intros.
          rewrite H5 in *.
          assert (is_list_sorted ODT_lt_dec (domain x) = true)
            by (apply (@rec_sorted_skip_first string ODT_string _  x (s0,a)); assumption).
          simpl.
          specialize (IHl2 x H7 H6).
          simpl in H2.
          rewrite IHl2; try reflexivity; intros.
          simpl in H2.
          case_eq (string_dec x0 s0); intros.
          * subst.
            assert (NoDup (domain ((s0,a)::x))) by (apply is_list_sorted_NoDup_strlt; assumption).
            assert (assoc_lookupr string_dec x s0 = None) by
                (apply assoc_lookupr_nin_none; inversion H5; assumption).
            assert (assoc_lookupr string_dec l2 s0 = None) by
                (apply assoc_lookupr_nin_none; inversion H4; assumption).
            rewrite H10; rewrite H11; reflexivity.
          * specialize (H2 x0 H8).
            destruct(string_dec x0 s0) ; try congruence.
            destruct (assoc_lookupr string_dec x x0);
              destruct (assoc_lookupr string_dec l2 x0); try congruence.
        + elim H5; clear H5; intros.
          case_eq (in_dec string_dec s0 s); intros.
          specialize (H2 s0 i).
          destruct (string_dec s0 s0); try congruence.
          simpl in H5.
          assert (assoc_lookupr string_dec l1 s0 = None)
            by (apply assoc_lookupr_nin_none; assumption).
          rewrite H8 in *.
          destruct (assoc_lookupr string_dec l2 s0); congruence.
          rewrite (IHl2 l1 H H6); try reflexivity; intros.
          specialize (H2 x H8).
          case_eq (string_dec x s0); intros; subst.
          congruence.
          rewrite H9 in *.
          destruct (assoc_lookupr string_dec l1 x); destruct (assoc_lookupr string_dec l2 x); try congruence.
    Qed.

    Lemma rproject_sublist {A} (l1 l2:list (string * A)) (s:list string) :
      is_list_sorted ODT_lt_dec (domain l1) = true ->
      is_list_sorted ODT_lt_dec (domain l2) = true ->
      sublist s (domain l1) ->
      sublist l1 l2 ->
      rproject l1 s = rproject l2 s.
    Proof.
      intros.
      assert (sublist s (domain l2))
        by (apply (sublist_trans s (domain l1) (domain l2)); try assumption;
            apply sublist_domain; assumption).
      apply rproject_with_lookup; try assumption; intros.
      assert (In x (domain l1)) by (apply (sublist_In H1); assumption).
      assert (In x (domain l2)) by (apply (sublist_In H3); assumption).
      generalize (in_dom_lookupr l1 x string_dec); intros.
      elim (H7 H5); intros.
      assert (assoc_lookupr string_dec l2 x = Some x0).
      assert (NoDup (domain l2)) by (apply is_list_sorted_NoDup_strlt; assumption).
      apply (assoc_lookupr_nodup_sublist H9 H2); assumption.
      rewrite H8; rewrite H9; reflexivity.
    Qed.
  
    Lemma rproject_equivlist {B} (l:list (string*B)) sl1 sl2 :
      equivlist sl1 sl2 ->
      rproject l sl1 = rproject l sl2.
    Proof.
      induction l; simpl; trivial.
      intros eqq.
      rewrite (IHl eqq).
      destruct (in_dec string_dec (fst a) sl1);
        destruct (in_dec string_dec (fst a) sl2); trivial.
      - apply eqq in i; intuition.
      - apply eqq in i; intuition.
    Qed.

    Lemma rproject_sortfilter {B} (l:list (string*B)) sl1 :
      rproject l (insertion_sort ODT_lt_dec sl1) = rproject l sl1.
    Proof.
      apply rproject_equivlist.
      apply insertion_sort_trich_equiv.
      apply StringOrder.trichotemy.
    Qed.

    Lemma rproject_concat_dist {A} (l1 l2:list (string * A)) (s:list string) :
      rproject (rec_concat_sort l1 l2) s = rec_concat_sort (rproject l1 s) (rproject l2 s).
    Proof.
      unfold rec_concat_sort.
      rewrite rproject_rec_sort_commute.
      rewrite rproject_app.
      reflexivity.
    Qed.

  End RecProject.

  Section RecConcat.
    (** Semantics of the [rec_concat] operator. *)
    Definition recconcat (r1 r2:list (string*data)) :=
      rec_concat_sort r1 r2.

    Inductive rec_concat_sem: data -> data -> data -> Prop :=
    | sem_rec_concat:
        forall r1 r2,
          rec_concat_sem (drec r1) (drec r2)
                         (drec (recconcat r1 r2)).

    (* [orecconcat] is correct and complete wrt. the [rec_concat_sem]
       semantics. *)
      
    Definition orecconcat (a:data) (x:data) :=
      match a with
      | drec r2 =>
        match x with
        | drec r1 => Some (drec (rec_concat_sort r2 r1))
        | _ => None
        end
      | _ => None
      end.

    Lemma orecconcat_correct : forall d d1 d2,
        orecconcat d d1 = Some d2 ->
        rec_concat_sem d d1 d2.
    Proof.
      intros.
      destruct d; destruct d1; simpl in *; try congruence.
      inversion H; econstructor; reflexivity.
    Qed.

    Lemma orecconcat_complete : forall d d1 d2,
        rec_concat_sem d d1 d2 ->
        orecconcat d d1 = Some d2.
    Proof.
      intros.
      inversion H; subst.
      reflexivity.
    Qed.

    Lemma orecconcat_correct_and_complete : forall d d1 d2,
        orecconcat d d1 = Some d2 <->
        rec_concat_sem d d1 d2.
    Proof.
      split.
      apply orecconcat_correct.
      apply orecconcat_complete.
    Qed.
  End RecConcat.

  Section RecRemove.
    Definition rremove {A} (l:list (string*A)) (s:string) : list (string*A) :=
      filter (fun x => if string_dec s (fst x) then false else true) l.
    
    Lemma is_sorted_rremove {A} (l:list (string * A)) (s:string):
      is_list_sorted ODT_lt_dec (domain l) = true ->
      is_list_sorted ODT_lt_dec (domain (rremove l s)) = true.
    Proof.
      unfold rremove; intros.
      apply (@sorted_over_filter string ODT_string); assumption.
    Qed.

    Lemma domain_rremove {A} s (l:list (string*A)) :
      domain (rremove l s) = remove_all s (domain l).
    Proof.
      induction l; simpl; trivial.
      unfold equiv_dec, string_eqdec.
      destruct (string_dec s (fst a)); simpl; trivial.
      f_equal; trivial.
    Qed.

    Lemma rremove_rec_sort_commute {B} (l1:list (string*B)) s:
      rremove (rec_sort l1) s = rec_sort (rremove l1 s).
    Proof.
      unfold rremove.
      apply rec_sort_filter_fst_commute; intros.
      simpl.
      match_destr.
    Qed.

    Lemma rremove_app {B} (l1 l2:list (string*B)) s:
      rremove (l1 ++ l2) s = rremove l1 s ++ rremove l2 s.
    Proof.
      unfold rremove.
      apply filter_app.
    Qed.

    Lemma nin_rremove {B} (l:list (string*B)) s :
      ~ In s (domain l) ->
      rremove l s = l.
    Proof.
      intros nin.
      apply true_filter; intros ? inn.
      destruct x.
      apply in_dom in inn.
      simpl.
      match_destr.
      congruence.
    Qed.

  End RecRemove.

  Section SRProject.
    Definition sorted_vector (s:list string) : list string :=
      insertion_sort ODT_lt_dec s.
    
    Lemma sorted_vector_sorted (s:list string) :
      is_list_sorted ODT_lt_dec (sorted_vector s) = true.
    Proof.
      rewrite is_list_sorted_Sorted_iff.
      apply insertion_sort_Sorted.
    Qed.

    Definition projected_subset (s1 s2:list string) : list string :=
      filter (fun x => if in_dec string_dec x s2 then true else false) s1.
    
    Lemma projected_subst_sorted (s1 s2:list string) :
      is_list_sorted ODT_lt_dec s1 = true ->
      is_list_sorted ODT_lt_dec (projected_subset s1 s2) = true.
    Proof.
      intros.
      rewrite sorted_StronglySorted.
      apply StronglySorted_filter.
      rewrite <- sorted_StronglySorted.
      eauto.
      apply StrictOrder_Transitive.
      apply StrictOrder_Transitive.
    Qed.
  
    Lemma sorted_projected_subset_is_sublist (s1 s2:list string):
      is_list_sorted ODT_lt_dec s1 = true ->
      is_list_sorted ODT_lt_dec s2 = true ->
      sublist (projected_subset s1 s2) s2.
    Proof.
      intros.
      apply StronglySorted_incl_sublist.
      rewrite <- sorted_StronglySorted.
      eapply projected_subst_sorted; assumption.
      apply StrictOrder_Transitive.
      rewrite <- sorted_StronglySorted.
      eauto.
      apply StrictOrder_Transitive.
      intros.
      unfold projected_subset in *.
      induction s1; simpl in H1.
      contradiction.
      assert (is_list_sorted ODT_lt_dec s1 = true).
      apply (@is_list_sorted_cons_inv string _ _ a s1); assumption.
      specialize (IHs1 H2); clear H.
      destruct (in_dec string_dec a s2); simpl in *.
      - elim H1; clear H1; intros.
        subst.
        assumption.
        apply (IHs1 H).
      - apply (IHs1 H1).
    Qed.
    
    (* This is a form of projection that guarantees that the projection
       list is first sorted then pruned to the domain of its input. *)
  
    Definition srproject {A} (l:list (string*A)) (s:list string) : list (string*A) :=
      let ps := (projected_subset (sorted_vector s) (domain l)) in
      rproject l ps.
    
    Lemma insertion_sort_insert_equiv_vec (x a:string) (l:list string) :
      In x
         (SortingAdd.insertion_sort_insert ODT_lt_dec a l) <->
      a = x \/ In x l.
    Proof.
      induction l; simpl; [intuition|].
      destruct a; destruct a0; simpl in *.
      split; intros.
      intuition.
      intuition.
      split; intros.
      intuition.
      intuition.
      split; intros.
      intuition.
      intuition.
      destruct (StringOrder.lt_dec (String a a1) (String a0 a2)); simpl; [intuition|].
      destruct (StringOrder.lt_dec (String a0 a2) (String a a1)); simpl; [intuition|].
      split; intros.
      intuition.
      intuition.
      subst; clear H0.
      revert n n0 H1 H3.
      generalize (String a a1), (String a0 a2); intros.
      left.
      destruct (trichotemy s s0); intuition.
    Qed.

    Lemma sorted_vector_equivlist l : 
      equivlist (sorted_vector l) l.
    Proof.
      unfold equivlist.
      induction l; simpl; [intuition|]; intros x.
      rewrite <- IHl. apply insertion_sort_insert_equiv_vec.
    Qed.

    Lemma equivlist_in_dec (x:string) (s1 s2:list string) :
      (equivlist s1 s2) ->
      (if (in_dec string_dec x s1) then true else false) =
      (if (in_dec string_dec x s2) then true else false).
    Proof.
      intros.
      destruct (in_dec string_dec x s1); destruct (in_dec string_dec x s2); try reflexivity.
      assert (In x s2). rewrite <- H; assumption. congruence.
      assert (In x s1). rewrite H; assumption. congruence.
    Qed.

    Lemma sorted_vector_in_dec (x:string) (s1:list string):
      (if (in_dec string_dec x s1) then true else false) =
      (if (in_dec string_dec x (sorted_vector s1)) then true else false).
    Proof.
      rewrite (equivlist_in_dec x s1 (sorted_vector s1)).
      reflexivity.
      rewrite sorted_vector_equivlist.
      reflexivity.
    Qed.

    Lemma in_intersection_projected (x:string) (s1 s2:list string) :
      In x s1 /\ In x s2 -> In x (projected_subset s1 s2).
    Proof.
      intros.
      elim H; clear H; intros.
      induction s1.
      simpl in *. contradiction.
      simpl in *.
      elim H; clear H; intros.
      subst.
      destruct (in_dec string_dec x s2); try congruence.
      simpl; left; reflexivity.
      specialize (IHs1 H); clear H0 H.
      destruct (in_dec string_dec a s2); auto.
      simpl; right; assumption.
    Qed.

    Lemma in_projected (x:string) (s1 s2:list string) :
      In x (projected_subset s1 s2) -> In x s1.
    Proof.
      intros.
      induction s1; simpl in *; [contradiction|].
      destruct (in_dec string_dec a s2); simpl in *.
      elim H; clear H; intros.
      left; assumption.
      right; apply (IHs1 H).
      right; apply (IHs1 H).
    Qed.
 
    Lemma sproject_in_dec {A} (x:string) (s1:list string) (l:list (string*A)) :
      In x (domain l) ->
      (if (in_dec string_dec x s1) then true else false) =
      (if (in_dec string_dec x (projected_subset s1 (domain l))) then true else false).
    Proof.
      intros.
      destruct (in_dec string_dec x s1); destruct (in_dec string_dec x (projected_subset s1 (domain l))); try reflexivity.
      - assert (In x (projected_subset s1 (domain l))) by
            (apply in_intersection_projected; auto).
        congruence.
      - assert (In x s1) by (apply (in_projected x s1 (domain l)); assumption).
        congruence.
    Qed.
    
    Lemma rproject_sproject {A} (l:list (string*A)) (s:list string) :
      is_list_sorted ODT_lt_dec (domain l) = true ->
      rproject l s = srproject l s.
    Proof.
      intros.
      unfold srproject.
      unfold rproject.
      assert (filter
                (fun x : string * A =>
                   if in_dec string_dec (fst x) s then true else false) l =
              filter
                (fun x : string * A =>
                   if in_dec string_dec (fst x) (sorted_vector s) then true else false) l).
      apply filter_eq; intros.
      rewrite sorted_vector_in_dec; reflexivity.
      rewrite H0; clear H0;
        generalize (sorted_vector s) as ss; intros.
      apply filter_ext; intros.
      apply sproject_in_dec.
      destruct x; simpl in *.
      induction l; try auto.
      assert (is_list_sorted StringOrder.lt_dec (domain l) = true).
      apply (@is_list_sorted_cons_inv string _ _ (fst a0) (domain l)); assumption.
      specialize (IHl H1); clear H1 H.
      simpl in *.
      elim H0; clear H0; intros.
      subst; simpl; left; reflexivity.
      right; apply (IHl H).
    Qed.

  End SRProject.
End RecOperators.

