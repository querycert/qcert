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

Section RecOperators.
  Context {fdata:foreign_data}.

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

