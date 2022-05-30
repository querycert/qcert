(*
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

Require Import Orders.
Require Import Equivalence.
Require Import EquivDec.
Require Import Permutation.
Require Import Compare_dec.
Require Import Lia.
Require Import String.
Require Import List.
Require Import ZArith.
Require Import CoqLibAdd.
Require Import StringAdd.
Require Import Lift.
Require Import LiftIterators.
Require Import Bindings.
Require Import SortingAdd.

Section SortableItem.
  (*
      Definition sort_dstring_list := @insertion_sort string StringOrder.lt StringOrder.lt_dec.
      Definition sort_dnat_list := @insertion_sort Z Z.lt Z.lt_dec.
   *)

  Inductive sdata :=
  | sdnat : Z -> sdata
  | sdstring : string -> sdata
  .

  (** Equality is decidable for sdata *)
  Lemma sdata_eq_dec : forall x y:sdata, {x=y}+{x<>y}.
  Proof.
    destruct x; destruct y; try solve[right; inversion 1].
    - destruct (Z.eq_dec z z0).
      + left; f_equal; trivial.
      + right;intro;apply n;inversion H; trivial.
    - destruct (string_dec s s0).
      + left; f_equal; trivial.
      + right;intro;apply n;inversion H; trivial.
  Defined.

  (* begin hide *)
  Global Instance sdata_eqdec : EqDec sdata eq := sdata_eq_dec.
  (* begin hide *)

End SortableItem.

Module SortableDataOrder <: OrderedTypeFull with Definition t:=sdata.
  Definition t:=sdata.
  Definition eq := @eq t.
  Definition eq_equiv : (Equivalence eq) := eq_equivalence.
  Definition eq_dec := sdata_eq_dec.

  Definition compare (d1 d2:t) : comparison :=
    match d1,d2 with
    | sdnat n, sdstring s => Lt
    | sdstring s, sdnat n => Gt
    | sdnat n1, sdnat n2 => Z.compare n1 n2
    | sdstring s1, sdstring s2 => StringOrder.compare s1 s2
    end.

  Definition lt (d1 d2:sdata) : Prop
    := compare d1 d2 = Lt.

  Lemma compare_spec :
    forall x y : sdata,
      CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros; unfold eq, lt, compare.
    destruct x; destruct y; intros.
    - generalize (Z.compare_spec z z0); intros.
      inversion H; subst; auto.
    - constructor; trivial.
    - constructor; trivial.
    - generalize (StringOrder.compare_spec s s0); intros.
      inversion H; auto.
      assert (s = s0) by (apply StringOrder.compare_eq_iff;
                          rewrite H0; reflexivity).
      subst; auto.
  Qed.

  Lemma trichotemy a b : {lt a b} + {eq a b} + {lt b a}.
  Proof.
    generalize (compare_spec a b); intros nc.
    destruct (compare a b);
      [left; right|left;left|right]; inversion nc; trivial.
  Defined.

  Lemma compare_refl_eq a: compare a a = Eq.
  Proof.
    destruct a; simpl in *; eauto.
    rewrite Z.compare_refl; trivial.
    rewrite StringOrder.compare_refl_eq; trivial.
  Qed.

  Lemma compare_eq_iff a b: compare a b = Eq <-> a = b.
  Proof.
    split; [| intros; subst; apply compare_refl_eq].
    revert b.
    destruct a; destruct b; simpl in *; eauto; try congruence; intros.
    - rewrite Z.compare_eq_iff in H; subst; reflexivity.
    - rewrite StringOrder.compare_eq_iff in H; subst; reflexivity.
  Qed.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    split; repeat red; unfold lt, compare; intros.
    - destruct x.
      assert ((z ?= z)%Z = Eq).
      rewrite Z.compare_eq_iff; reflexivity.
      congruence.
      assert (StringOrder.compare s s = Eq).
      rewrite StringOrder.compare_eq_iff; reflexivity.
      congruence.
    - destruct x; destruct y; destruct z; try reflexivity; try congruence.
      + apply (Z.lt_trans z0 z1 z H H0).
      + generalize (@StrictOrder_Transitive _ _ (StringOrder.lt_strorder) s s0 s1);
          unfold StringOrder.lt; intros.
        auto.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, respectful, eq; intros; subst; intuition.
  Qed.

  Program Definition lt_dec (a b:sdata) : {lt a b} + {~lt a b}
    := match compare a b with
       | Lt => left _
       | Eq => right _
       | Gt => right _
       end.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    trivial.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    rewrite H0. apply irreflexivity.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    intro l2. apply (asymmetry H0 l2).
  Qed.
  
  Definition le (a b:sdata) :=
    match compare a b with
    | Lt => True
    | Eq => True
    | Gt => False
    end.

  Definition gt (a b:sdata) :=
    match compare a b with
    | Lt => False
    | Eq => False
    | Gt => True
    end.

  Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
  Proof.
    intros.
    generalize (compare_spec x y); inversion 1;
      unfold le, lt, eq in *;
      case_eq (compare x y); intuition congruence.
  Qed.

  Program Definition le_dec (a b:sdata) : {le a b} + {~le a b}
    := match compare a b with
       | Lt => left _
       | Eq => left _
       | Gt => right _
       end.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    apply le_lteq.
    intuition.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    apply le_lteq.
    intuition.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    intro l2.
    apply le_lteq in l2.
    destruct l2.
    - apply (asymmetry H0 H1).
    - rewrite H1 in H0. apply (irreflexivity H0).
  Qed.

  Lemma le_not_gt a b :
    le a b -> ~(gt a b).
  Proof.
    unfold not; intros.
    unfold le, gt in *.
    destruct (compare a b); simpl in *; congruence.
  Qed.

  Lemma compare_transitive x y z c:
    compare x y = c -> compare y z = c -> compare x z = c.
  Proof.
    intros; destruct c.
    - rewrite compare_eq_iff in *; subst; reflexivity.
    - generalize (@StrictOrder_Transitive t lt lt_strorder); unfold Transitive; intros.
      apply (H1 x y z); assumption.
    - unfold compare in *.
      destruct x; destruct y; destruct z; try reflexivity; try congruence.
      + apply (Zgt_trans z0 z1 z H H0).
      + generalize (StringOrder.gt_transitive s s0 s1); intros.
        auto.
  Qed.

End SortableDataOrder.

Section LexicographicData.
  (** Equality is decidable for lists of sortable data *)
  Lemma list_sdata_eq_dec : forall x y:list sdata, {x=y}+{x<>y}.
  Proof.
    induction x; destruct y; try solve[right; inversion 1].
    - left; reflexivity.
    - destruct (sdata_eq_dec a s).
      + subst.
        destruct (IHx y); subst.
        left; reflexivity.
        right; inversion 1; auto.
      + right; inversion 1; auto.
  Defined.

  (* begin hide *)
  Global Instance list_sdata_eqdec : EqDec (list sdata) eq := list_sdata_eq_dec.
  (* begin hide *)

End LexicographicData.

Module LexicographicDataOrder <: OrderedTypeFull with Definition t:=list sdata.
  Definition t := list sdata.
  Definition eq := @eq t.
  Definition eq_equiv : (Equivalence eq) := eq_equivalence.
  Definition eq_dec := list_sdata_eq_dec.

  Fixpoint compare (l1 l2:list sdata) : comparison :=
    match l1, l2 with
    | nil, nil => Eq
    | nil, _ :: _ => Lt
    | _ :: _, nil => Gt
    | d1 :: l1', d2 :: l2' => 
      match SortableDataOrder.compare d1 d2 with
      | Lt => Lt
      | Eq => compare l1' l2'
      | Gt => Gt
      end
    end.
  
  Definition lt (l1 l2:t) : Prop
    := compare l1 l2 = Lt.

  Lemma compare_spec :
    forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    unfold eq, lt. 
    induction x; destruct y; simpl in *; eauto.
    specialize (IHx y).
    case_eq (SortableDataOrder.compare_spec a s); intros.
    - unfold SortableDataOrder.eq in *; subst.
      inversion IHx; simpl; subst; eauto.
      rewrite H1.
      constructor.
      rewrite SortableDataOrder.compare_refl_eq; reflexivity.
    - eauto.
    - unfold SortableDataOrder.lt in *. rewrite l; eauto.
  Qed.
  
  Lemma trichotemy a b : {lt a b} + {eq a b} + {lt b a}.
  Proof.
    generalize (compare_spec a b); intros nc.
    destruct (compare a b);
      [left; right|left;left|right]; inversion nc; trivial.
  Defined.

  Lemma compare_refl_eq a: compare a a = Eq.
  Proof.
    induction a; simpl in *; eauto.
    rewrite SortableDataOrder.compare_refl_eq; trivial.
  Qed.

  Lemma compare_eq_iff a b: compare a b = Eq <-> a = b.
  Proof.
    split; [| intros; subst; apply compare_refl_eq].
    revert b.
    induction a; destruct b; simpl in *; eauto; try congruence.
    generalize (SortableDataOrder.compare_eq_iff a s).
    intros. specialize (IHa b).
    destruct (SortableDataOrder.compare a s); intuition; congruence.
  Qed.

  Lemma compare_transitive x y z c:
    compare x y = c -> compare y z = c -> compare x z = c.
  Proof.
    revert x y z.
    induction x; destruct y; destruct z; simpl; eauto; try congruence.
    intros. specialize (IHx y z).
    generalize (@StrictOrder_Transitive _ _ (SortableDataOrder.lt_strorder) a s s0).
    unfold SortableDataOrder.lt. intros AC.
    case_eq (SortableDataOrder.compare a s); 
      intros re; rewrite re in *; try congruence;
        case_eq (SortableDataOrder.compare s s0); 
        intros re2; rewrite re2 in *; try congruence;
          try rewrite SortableDataOrder.compare_eq_iff in *; subst;
            try rewrite re in*; try rewrite re2 in *;
              try rewrite AC by trivial; 
              try rewrite SortableDataOrder.compare_refl_eq; 
              auto.
    rewrite (SortableDataOrder.compare_transitive _ _ _ Gt re re2).
    reflexivity.
  Qed.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    split; repeat red; unfold lt.
    - intros a H; rewrite compare_refl_eq in H. discriminate. 
    - intros. apply (compare_transitive x y z Lt); assumption.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, respectful, eq; intros; subst; intuition.
  Qed.

  Program Definition lt_dec (a b:list sdata) : {lt a b} + {~lt a b}
    := match compare a b with
       | Lt => left _
       | Eq => right _
       | Gt => right _
       end.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    trivial.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    rewrite H0.  apply irreflexivity.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    intro l2. apply (asymmetry H0 l2).
  Qed.

  Definition le (a b:t) :=
    match compare a b with
    | Lt => True
    | Eq => True
    | Gt => False
    end.

  Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
  Proof.
    intros.
    generalize (compare_spec x y); inversion 1;
      unfold le, lt, eq in *;
      case_eq (compare x y); intuition congruence.
  Qed.

  Program Definition le_dec (a b:t) : {le a b} + {~le a b}
    := match compare a b with
       | Lt => left _
       | Eq => left _
       | Gt => right _
       end.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    apply le_lteq.
    intuition.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    apply le_lteq.
    intuition.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    intro l2.
    apply le_lteq in l2.
    destruct l2.
    - apply (asymmetry H0 H1).
    - rewrite H1 in H0. apply (irreflexivity H0).
  Qed.

  Lemma lt_transitive (x y z:t) :
    lt x y -> lt y z -> lt x z.
  Proof.
    apply StrictOrder_Transitive.
  Qed.
    
  Lemma le_transitive (x y z:t) :
    le x y -> le y z -> le x z.
  Proof.
    repeat (rewrite le_lteq); intros.
    elim H; elim H0; intros; clear H; clear H0.
    - left; revert H2 H1; apply StrictOrder_Transitive.
    - rewrite H1 in H2; left; assumption.
    - rewrite H2; left; assumption.
    - rewrite H1 in H2; rewrite H2; right; reflexivity.
  Qed.

  Lemma flip_not_le l l0:
    ~le l l0 -> le l0 l.
  Proof.
    intros.
    unfold le in *.
    unfold not in *.
    case_eq (compare l l0); intros; rewrite H0 in H; try congruence.
    - assert False by (apply H; trivial); contradiction.
    - assert False by (apply H; trivial); contradiction.
    - case_eq (compare l0 l); intros; try trivial.
      assert (compare l l = Gt)
        by (apply (compare_transitive l l0 l); assumption).
      assert (compare l l = Eq).
      rewrite compare_eq_iff; reflexivity.
      congruence.
  Qed.

End LexicographicDataOrder.

Section DictSort.

  Program Instance ODT_lexdata : (@ODT (list sdata))
    := mkODT _ _ LexicographicDataOrder.lt
             LexicographicDataOrder.lt_strorder
             LexicographicDataOrder.lt_dec
             LexicographicDataOrder.compare _.
  Next Obligation.
    simpl.
    apply LexicographicDataOrder.compare_spec.
  Qed.

  (** Can be sorted:
        - Empty collection
        - Collection of integers
        - Collection of strings
   *)

  Context {A:Set}.
  Definition sortable_data : Set := (list sdata) * A.
  Definition sortable_coll : Set := list sortable_data.

  (* Collection sort *)

  Definition dict_field_le (a b:sortable_data) :=
    LexicographicDataOrder.le (fst a) (fst b).

  Lemma dict_field_le_dec (a b:sortable_data) :
    {dict_field_le a b} + {~dict_field_le a b}.
  Proof.
    destruct a.
    destruct b.
    unfold dict_field_le; simpl.
    apply LexicographicDataOrder.le_dec.
  Defined.

  Lemma dict_field_le_transitive :
    forall x y z : sortable_data, dict_field_le x y -> dict_field_le y z -> dict_field_le x z.
  Proof.
    destruct x.
    destruct y.
    destruct z.
    unfold dict_field_le; simpl.
    apply LexicographicDataOrder.le_transitive.
  Qed.

  Definition dict_sort :=
    @insertion_sort ((list sdata)*A) dict_field_le dict_field_le_dec.

  Lemma dict_sort_sorted (l:sortable_coll) :
    is_list_sorted dict_field_le_dec (dict_sort l) = true.
  Proof.
    unfold dict_sort.
    apply insertion_sort_is_list_sorted.
  Qed.

  Lemma dict_sort_StronglySorted (l:sortable_coll) :
    StronglySorted dict_field_le (dict_sort l).
  Proof.
    apply insertion_sort_StronglySorted.
    unfold Transitive.
    apply dict_field_le_transitive.
  Qed.

  Definition sort_sortable_coll (sc:sortable_coll) : sortable_coll :=
    dict_sort sc.
  
  Definition coll_of_sortable_coll (sc:sortable_coll) : list A :=
    map snd sc.
  
  Lemma dict_field_le_anti :
    forall x y : sortable_data, ~ dict_field_le x y -> ~ dict_field_le y x -> x = y.
  Proof.
    unfold dict_field_le.
    intros.
    rewrite LexicographicDataOrder.le_lteq in *.
    intuition.
    destruct (LexicographicDataOrder.compare_spec (fst x) (fst y)); congruence.
  Qed.

  Lemma in_sort_sortable d l : 
    In d (sort_sortable_coll l) <-> In d l.
  Proof.
    unfold sort_sortable_coll, dict_sort.
    split; intros ind.
    - apply in_insertion_sort in ind; trivial.
    - apply insertion_sort_in; trivial.
      apply dict_field_le_anti.
  Qed.
    
  Lemma in_csc_ssc d l :
    In d (coll_of_sortable_coll (sort_sortable_coll l)) <->
    In d (coll_of_sortable_coll l).
  Proof.
    unfold coll_of_sortable_coll.
    repeat rewrite in_map_iff.
    split; intros [[??] [??]]; simpl in *; subst.
    - rewrite in_sort_sortable in *.
      eexists; split; try eassumption; reflexivity.
    - exists (l0, d); split; trivial.
      rewrite in_sort_sortable.
      trivial.
  Qed.

  Lemma in_csc_cons d s l :
      In d (coll_of_sortable_coll (s :: l)) <->
      (d = snd s \/ In d (coll_of_sortable_coll l)).
  Proof.
    unfold coll_of_sortable_coll.
    repeat rewrite in_map_iff.
    destruct s; simpl.
    split; intros ind.
    - destruct ind as [[? ?] [? ind]]; simpl in *; subst.
      destruct ind.
      + invcs H; tauto.
      + right.
        exists (l1, d); auto.
    - destruct ind as [| [[??] [??]]].
      + subst.
        exists (l0, a); auto.
      + simpl in *; subst.
        exists (l1, d); auto.
  Qed.

  Lemma flip_not_dict_field_le a a0:
    ~dict_field_le a a0 -> dict_field_le a0 a.
  Proof.
    intros.
    unfold dict_field_le in *.
    destruct a; destruct a0; simpl in *.
    apply LexicographicDataOrder.flip_not_le.
    assumption.
  Qed.

  Lemma insertion_sort_insert_perm (l:list sortable_data) (a:sortable_data) :
    Permutation (a::l) (insertion_sort_insert dict_field_le_dec a l).
  Proof.
    revert l.
    induction l; simpl.
    - repeat constructor.
    - destruct (dict_field_le_dec a a0); trivial.
      destruct (dict_field_le_dec a0 a); trivial.
      + rewrite perm_swap.
        rewrite Permutation_cons; try eassumption; trivial.
      + apply (flip_not_dict_field_le a a0) in n.
        contradiction.
  Qed.

  Lemma insertion_sort_on_perm_insert_perm (l l':list sortable_data) (a:sortable_data) :
    Permutation l l' ->
    Permutation (a::l) (insertion_sort_insert dict_field_le_dec a l').
  Proof.
    intros.
    assert (Permutation (a :: l') (a :: l))
      by (apply Permutation_sym; apply perm_skip; assumption).
    apply Permutation_sym in H0.
    generalize (insertion_sort_insert_perm l' a); intros.
    apply (Permutation_trans H0 H1).
  Qed.

  Lemma dict_sort_permutation l :
    Permutation (dict_sort l) l.
  Proof.
    revert l.
    induction l; simpl in *.
    - constructor.
    - apply Permutation_sym.
      apply insertion_sort_on_perm_insert_perm.
      apply Permutation_sym; assumption.
  Qed.

End DictSort.

Section SortByGen.
  Definition fget_criterias {A:Set}
             (d:A) (fl:list (A -> option sdata)) : option (list sdata) :=
    lift_map (fun f => f d) fl.

  Definition fsortable_data_of_data {A:Set}
             (d:A) (fl:list (A -> option sdata)) : option sortable_data :=
    lift (fun c => (c,d)) (fget_criterias d fl).

  Definition fsortable_coll_of_coll {A:Set}
             (fl:list (A -> option sdata)) (coll:list A) :
    option (list sortable_data)
    := lift_map (fun d => fsortable_data_of_data d fl) coll.

  Definition table_sort {A:Set} (scl:list (A -> option sdata))
             (coll: list A) : option (list A) :=
    lift coll_of_sortable_coll
         (lift sort_sortable_coll
               (fsortable_coll_of_coll scl coll)).

  Lemma sort_sortable_coll_sorted {A:Set} (l: @sortable_coll A):
    is_list_sorted dict_field_le_dec (sort_sortable_coll l) = true.
  Proof.
    intros.
    unfold sort_sortable_coll.
    apply dict_sort_sorted.
  Qed.

  Lemma lift_sort_sortable_coll_sorted {A:Set} (scl:list (A -> option sdata)) (l1: list A)
    (l2: sortable_coll):
    lift sort_sortable_coll (fsortable_coll_of_coll scl l1) = Some l2 ->
    is_list_sorted dict_field_le_dec l2 = true.
  Proof.
    intros.
    unfold lift in H.
    case_eq (fsortable_coll_of_coll scl l1); intros; rewrite H0 in H; simpl;
      [|congruence].
    inversion H; subst; clear H.
    apply sort_sortable_coll_sorted.
  Qed.

  Lemma sort_sortable_coll_StronglySorted {A:Set} (l: @sortable_coll A):
    StronglySorted dict_field_le (sort_sortable_coll l).
  Proof.
    rewrite <- is_list_sorted_StronglySorted.
    apply sort_sortable_coll_sorted.
    unfold Transitive; apply dict_field_le_transitive.
  Qed.

  Lemma lift_sort_sortable_coll_StronglySorted {A:Set} (scl:list (A -> option sdata))
        (l1: list A)
        (l2: sortable_coll) :
    lift sort_sortable_coll (fsortable_coll_of_coll scl l1) = Some l2 ->
    StronglySorted dict_field_le l2.
  Proof.
    intros.
    rewrite <- is_list_sorted_StronglySorted.
    eapply lift_sort_sortable_coll_sorted; apply H.
    unfold Transitive; apply dict_field_le_transitive.
  Qed.

  Lemma fsortable_data_of_data_snd {A:Set} (scl:list (A -> option sdata)) a s :
    fsortable_data_of_data a scl = Some s ->
    a = snd s.
  Proof.
    intros.
    destruct s; simpl in *.
    unfold fsortable_data_of_data in H.
    unfold fget_criterias in H.
    unfold lift in H.
    destruct (lift_map (fun f : A -> option sdata => f a) scl); simpl in H;
      [|congruence].
    inversion H; subst.
    reflexivity.
  Qed.

  Lemma lift_map_sortable_data_perm {A:Set} (scl:list (A -> option sdata)) l l':
    lift_map (fun d : A => fsortable_data_of_data d scl) l = Some l' ->
    Permutation (map snd l') l.
  Proof.
    intros.
    revert l' H.
    induction l; intros; simpl in *.
    - inversion H; constructor.
    - case_eq (fsortable_data_of_data a scl);
        intros; rewrite H0 in H; simpl in *; try congruence.
      unfold lift in H.
      case_eq (lift_map (fun d : A => fsortable_data_of_data d scl) l);
        intros; rewrite H1 in H; simpl in *; try congruence.
      inversion H; simpl.
      assert (a = snd s) by apply (fsortable_data_of_data_snd scl a s H0).
      subst.
      apply perm_skip.
      apply IHl.
      assumption.
  Qed.

  Lemma sort_sortable_coll_permuation {A:Set} (scl:list (A -> option sdata)) l l1 :
    fsortable_coll_of_coll scl l1 = Some l ->
    Permutation l1 (coll_of_sortable_coll (sort_sortable_coll l)).
  Proof.
    intros.
    unfold sort_sortable_coll.
    unfold fsortable_coll_of_coll in H.
    unfold coll_of_sortable_coll.
    assert (Permutation (map snd l) l1)
      by (apply (lift_map_sortable_data_perm scl); assumption).
    apply (Permutation_trans (l':= (map snd l))).
    - apply Permutation_sym; assumption.
    - apply Permutation_map. apply Permutation_sym. apply dict_sort_permutation.
  Qed.
  
End SortByGen.
