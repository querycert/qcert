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

Require Import Orders.
Require Import Equivalence.
Require Import EquivDec.
Require Import Compare_dec.
Require Import Omega.
Require Import String RString.
Require Import List.
Require Import ZArith.

Section SortableData.
  Inductive SortDesc : Set := | Descending | Ascending.
  Definition SortCriteria : Set := string * SortDesc.
  Definition SortCriterias : Set := list SortCriteria.

  (*
  Definition sort_dstring_list := @insertion_sort string StringOrder.lt StringOrder.lt_dec.
  Definition sort_dnat_list := @insertion_sort Z Z.lt Z_lt_dec.
   *)

  Inductive sdata :=
  | sdnat : Z -> sdata
  | sdstring : string -> sdata
  .

  Lemma sort_desc_eq_dec : forall x y:SortDesc, {x=y}+{x<>y}.
  Proof.
    decide equality.
  Defined.
  
  (** Equality is decidable for sdata *)
  Lemma sdata_eq_dec : forall x y:sdata, {x=y}+{x<>y}.
  Proof.
    destruct x; destruct y; try solve[right; inversion 1].
    - destruct (Z_eq_dec z z0).
      + left; f_equal; trivial.
      + right;intro;apply n;inversion H; trivial.
    - destruct (string_dec s s0).
      + left; f_equal; trivial.
      + right;intro;apply n;inversion H; trivial.
  Defined.

  (* begin hide *)
  Global Instance oql_eqdec : EqDec SortDesc eq := sort_desc_eq_dec.
    
  Global Instance sdata_eqdec : EqDec sdata eq := sdata_eq_dec.
  (* begin hide *)

End SortableData.

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
    rewrite Zcompare_refl; trivial.
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

  Instance lt_strorder : StrictOrder lt.
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
      + apply (Zlt_trans z0 z1 z H H0).
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

  Instance lt_strorder : StrictOrder lt.
  Proof.
    split; repeat red; unfold lt.
    - intros a H; rewrite compare_refl_eq in H. discriminate. 
    - induction x; destruct y; destruct z; simpl; eauto; try congruence.
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

End LexicographicDataOrder.
  
Section DataSort.
  Require Import RSort.
  Require Import RData.
  Require Import RBindings.

  Global Program Instance ODT_lexdata : (@ODT (list sdata))
    := mkODT _ _ LexicographicDataOrder.lt
             LexicographicDataOrder.lt_strorder
             LexicographicDataOrder.lt_dec
             LexicographicDataOrder.compare _.
  Next Obligation.
    simpl.
    apply LexicographicDataOrder.compare_spec.
  Qed.

  Require Import RRelation.
  Require Import ForeignData.
  Context {fdata:foreign_data}.
  
  Definition theotherdot d s :=
    match d with
    | drec r => edot r s
    | _ => None
    end.
  
  (** Can be sorted:
      - Empty collection
      - Collection of integers
      - Collection of strings
   *)

  Require Import RLift.
  Require Import RSort.

  Definition sortable_data : Set := (list sdata) * data.
  Definition sortable_coll : Set := list sortable_data.

  (* Collection sort *)

  Definition dict_field_le {A} (a b:(list sdata)*A) :=
    LexicographicDataOrder.le (fst a) (fst b).

  Lemma dict_field_le_dec {A} (a b:(list sdata)*A) :
    {dict_field_le a b} + {~dict_field_le a b}.
  Proof.
    destruct a.
    destruct b.
    unfold dict_field_le; simpl.
    apply LexicographicDataOrder.le_dec.
  Defined.

  Definition dict_sort {A} :=
    @insertion_sort ((list sdata)*A) dict_field_le dict_field_le_dec.

  Definition sort_sortable_coll (sc:sortable_coll) : sortable_coll :=
    dict_sort sc.

  Definition coll_of_sortable_coll (sc:sortable_coll) : list data :=
    map snd sc.
  
  Example scoll1 :=
    ((sdnat 2::sdstring "a"::nil,dnat 10)
     :: (sdnat 3::sdstring "x"::nil,dnat 11)
     :: (sdnat 2::sdstring "b"::nil,dnat 12)
     :: (sdnat 2::sdstring "b"::nil,dnat 2000)
     :: (sdnat 1::sdstring "a"::nil,dnat 13)
       ::nil).

  (* Eval vm_compute in (sort_sortable_coll scoll1). *)
  
  Definition get_criteria (d:data) (sc:SortCriteria) : option sdata :=
    let (att,sk) := sc in (* XXX IGNORES sort kind (asc|desc) XXX *)
    match theotherdot d att with
    | Some (dnat n) => Some (sdnat n)
    | Some (dstring s) => Some (sdstring s)
    | Some _ => None
    | None => None
    end.

  Definition get_criterias (d:data) (scl:SortCriterias) : option (list sdata) :=
    lift_map (get_criteria d) scl.

  Definition sortable_data_of_data (d:data) (scl:SortCriterias) : option sortable_data :=
    lift (fun c => (c,d)) (get_criterias d scl).

  Definition sortable_coll_of_coll (scl:SortCriterias) (coll:list data) :
    option (list sortable_data)
    := lift_map (fun d => sortable_data_of_data d scl) coll.
  
  Definition data_sort (scl:SortCriterias) (d:data) : option data :=
    match d with
    | dcoll coll =>
      lift dcoll
           (lift coll_of_sortable_coll
                 (lift sort_sortable_coll
                       (sortable_coll_of_coll scl coll)))
    | _ => None
    end.

  (* Example *)
  Definition mkperson (name:string) (age:Z) (zip:Z) (company:string) :=
    drec (("name", dstring name)
          :: ("age", dnat age)
          :: ("zip", dnat zip)
          :: ("company", dstring company)
          :: nil)%string.
  Definition mkpersons_aux l :=
    map (fun x =>
           match x with (name, age, zip, company) => mkperson name age zip company
           end) l.
  Definition mkpersons l :=
    dcoll (mkpersons_aux l).

  Open Scope Z_scope.
  Definition persons :=
    mkpersons
      (("John",23,1008,"IBM")
         :: ("Jane",24,1009,"AIG")
         :: ("Jill",25,1010,"IBM")
         :: ("Jack",27,1010,"CMU")
         :: nil)%string.

  (*
  Eval vm_compute in persons.
  Eval vm_compute in (data_sort (("name"%string,Ascending)::nil) persons).
  Eval vm_compute in (data_sort (("zip"%string,Ascending)::("name"%string,Ascending)::nil) persons).
  *)

End DataSort.

Section DataSortProps.
  (* XXX To be proven correct XXX *)
  Require Import RDataNorm.
  Require Import ForeignData.
  Require Import Utils.
  Context {fdata:foreign_data}.

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
        exists (l0, d0); auto.
      + simpl in *; subst.
        exists (l1, d); auto.
  Qed.

  Lemma sortable_data_normalized h a sc sd :
    data_normalized h a ->
    sortable_data_of_data a sc = Some sd ->
    data_normalized h (snd sd).
  Proof.
    unfold sortable_data_of_data; intros dn eqs.
    apply some_lift in eqs.
    destruct eqs as [? eqs ?]; subst.
    simpl; trivial.
  Qed.

  Lemma data_sort_normalized h s (d sd:data) :
    data_sort s d = Some sd -> data_normalized h d -> data_normalized h sd.
  Proof.
    destruct d; simpl; intros eqs; try solve [inversion eqs].
    repeat (
    apply some_lift in eqs;
    destruct eqs as [? eqs ? ]; subst).
    intros dn; invcs dn.
    constructor.
    rewrite Forall_forall in *.
    revert x eqs H0.
    induction l; simpl; intros x eqs dn d ind.
    - unfold sortable_coll_of_coll in eqs.
      simpl in eqs.
      invcs eqs.
      simpl in *; tauto.
    - unfold sortable_coll_of_coll in *.
      simpl in eqs.
      case_eq (sortable_data_of_data a s)
      ; [intros ? eqq1 | intros eqq1]; rewrite eqq1 in eqs
      ; try discriminate.
      case_eq (lift_map (fun d : data => sortable_data_of_data d s) l)
      ; [intros ? eqq2 | intros eqq2]; rewrite eqq2 in eqs
      ; try discriminate.
      invcs eqs.
      assert (dnimpl:(forall x : data, In x l -> data_normalized h x)) by auto.
      specialize (IHl _ eqq2 dnimpl).
      rewrite in_csc_ssc in ind.
      destruct ind.
      + subst.
        eapply sortable_data_normalized; eauto.
      + rewrite <- in_csc_ssc in H.
        auto.
  Qed.

End DataSortProps.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)

