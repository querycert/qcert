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

(** Record fields and record domain manipulation *)

Section RDomain.
  Require Import String.
  Require Import List.
  Require Import Utils.

  Definition domains_included (ats1 ats2:list string):=
    Forall (fun x => In x ats2) ats1. 

  Definition domains_included_alt (ats1 ats2:list string):=
    forall x, In x ats1 -> In x ats2. 

  Lemma domains_included_eq (ats1 ats2:list string) :
    domains_included ats1 ats2 <-> domains_included_alt ats1 ats2.
  Proof.
    unfold domains_included, domains_included_alt.
    apply Forall_forall.
  Qed.

  Definition domains_intersect (ats1 ats2 iats:list string):=
    forall x, In x iats -> (In x ats1 /\ In x ats2).

  Fixpoint domains_intersection (ats1 ats2:list string) : list string :=
    match ats1 with
      | nil => nil
      | a :: ats1' =>
        if (existsb (fun x => if string_dec x a then true else false) ats2)
        then a :: (domains_intersection ats1' ats2)
        else (domains_intersection ats1' ats2)
    end.

  Definition domains_disjoint (ats1 ats2:list string) :=
    domains_intersection ats1 ats2 = nil.

  Definition in_domain (ats1:list string) (x:string) :=
    In x ats1.
  
  Definition not_in_domain (ats1:list string) (x:string) :=
    In x ats1 -> False.
  
  Lemma domains_intersection_nil_r (ats:list string) :
    domains_intersection ats nil = nil.
  Proof.
    induction ats.
    simpl; reflexivity.
    simpl; assumption.
  Qed.

  Lemma not_so_in (x a:string) (l1 l2:list string) :
    x <> a -> In x (domains_intersection l1 (a :: l2)) -> In x (domains_intersection l1 l2).
  Proof.
    induction l1; intros.
    simpl; assumption.
    simpl in *; revert H0.
    elim (string_dec a a0); intros; simpl in *.
    - rewrite a1 in *; clear a1; simpl.
      elim H0; intros; clear H0.
      congruence.
      case (existsb
              (fun x0 : string => if string_dec x0 a0 then true else false) l2).
      simpl in *; right.
      apply IHl1; assumption.
      apply IHl1; assumption.
    - revert H0.
      case (existsb
              (fun x0 : string => if string_dec x0 a0 then true else false) l2).
      intros.
      simpl in *.
      elim H0; intros; clear H0.
      left; assumption.
      right; apply IHl1; assumption.
      intros; apply IHl1; assumption.
  Qed.

  Lemma intersection_intersects (ats1 ats2:list string) :
    domains_intersect ats1 ats2 (domains_intersection ats1 ats2).
  Proof.
    unfold domains_intersect; split.
    - revert H; revert ats2.
      induction ats1; simpl; intros; try assumption.
      generalize (string_dec x a); intros.
      elim H0; intros; clear H0.
      rewrite a0 in *; clear a0.
      left; reflexivity.
      generalize (two_cases (fun x => (existsb (fun x0 : string => if string_dec x0 a then true else false) x)) ats2).
      intros; elim H0; intros; clear H0; revert H; rewrite H1; intros.
      * clear H1; simpl in *.
        elim H; intro; clear H.
      + left; assumption.
      + specialize (IHats1 ats2).
        right; apply IHats1; assumption.
        * specialize (IHats1 ats2).
          right; apply IHats1; assumption.
    - revert H; revert ats1.
      induction ats2; try( intros; rewrite domains_intersection_nil_r in H; assumption ).
      intros; simpl.
      generalize (string_dec x a); intros.
      elim H0; intros; clear H0.
      rewrite a0 in *; clear a0.
      left; reflexivity.
      assert (In x (domains_intersection ats1 ats2)).
      apply (not_so_in x a ats1 ats2); assumption.
      right.
      apply (IHats2 ats1); assumption.
  Qed.

  Lemma self_domain (ats:list string) :
    domains_included ats ats.
  Proof.
    unfold domains_included.
    induction ats.
    apply Forall_nil. 
    simpl; apply Forall_cons.
    left; reflexivity.
    apply Forall_impl with (P := (fun x : string => In x ats)).
    intros.
    right; assumption.
    assumption.
  Qed.

  Lemma domains_included_nil_l l:
    domains_included nil l.
  Proof.
    apply domains_included_eq.
    induction l; unfold domains_included_alt in *; intros.
    assumption.
    simpl in *.
    contradiction.
  Qed.
  
  Lemma domains_included_nil_r l:
    domains_included l nil -> l = nil.
  Proof.
    intros.
    assert (domains_included_alt l nil); try (apply domains_included_eq; assumption); clear H.
    induction l; unfold domains_included_alt in *; intros.
    reflexivity.
    simpl in *.
    specialize (H0 a).
    elim H0.
    left; reflexivity.
  Qed.
  
  Lemma domains_included_cons l1 l2 (a:string):
    domains_included (a::l1) l2 -> domains_included l1 l2.
  Proof.
    intros.
    apply domains_included_eq.
    assert (domains_included_alt (a :: l1) l2); try (apply domains_included_eq; assumption); clear H.
    unfold domains_included_alt in *; intros.
    simpl in H0.
    specialize (H0 x).
    apply H0.
    right; assumption.
  Qed.


End RDomain.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
