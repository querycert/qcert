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

Section RRelation.
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
  Require Import RDomain.
  Require Import ForeignData.
  Require Import RData.

  Context {fdata:foreign_data}.

  Definition ldeq := (@Permutation data).
  Notation "X ≅ Y" := (ldeq X Y) (at level 70).                             (* ≅ = \cong *)

  (* note: right-rec so that new fields hide old fields *)
  Definition edot {A} (r:list (string*A)) (a:string) : option A :=
    assoc_lookupr ODT_eqdec r a.

  Lemma edot_nodup_perm {A:Type} (l l':list (string*A)) x :
    NoDup (domain l) -> Permutation l l' -> edot l x = edot l' x.
  Proof.
    apply assoc_lookupr_nodup_perm.
  Qed.

  Lemma edot_fresh_concat {A} x (d:A) b :
    ~ In x (domain b) ->
    edot (rec_concat_sort b ((x,d)::nil)) x = Some d.
   Proof.
     intros.
     apply (@assoc_lookupr_insertion_sort_fresh string ODT_string); trivial.
   Qed.

  Definition unbdbool (f:bool -> bool -> bool) (d1 d2:data) : option data :=
    match d1 with
      | dbool b1 =>
        match d2 with
          | dbool b2 => Some (dbool (f b1 b2))
          | _ => None
        end
      | _ => None
    end.

  Definition unudbool (f:bool -> bool) (d:data) : option data :=
    match d with
      | dbool b =>Some (dbool (f b))
      | _ => None
    end.

  Definition unbdnat (f:Z -> Z -> bool) (d1 d2:data) : option data :=
    match d1 with
      | dnat n1 =>
        match d2 with
          | dnat n2 => Some (dbool (f n1 n2))
          | _ => None
        end
      | _ => None
    end.

  Definition unbdata (f:data -> data -> bool) (d1 d2:data) : option data :=
    Some (dbool (f d1 d2)).

  Definition unsdstring (f:string -> string -> string) (d1 d2:data) : option data :=
    match d1 with
      | dstring s1 =>
        match d2 with
          | dstring s2 => Some (dstring (f s1 s2))
          | _ => None
        end
      | _ => None
    end.

  Lemma unsdstring_is_string f d1 d2 d3:
    unsdstring f d1 d2 = Some d3 -> exists s:string, d3 = dstring s.
  Proof.
    intros.
    destruct d1; destruct d2; simpl in *; try congruence.
    exists (f s s0); inversion H; reflexivity.
  Qed.

  Definition ondcoll2 {A} : (list data -> list data -> A) -> data -> data -> option A.
    intros f d1 d2.
    destruct d1.
    exact None. exact None. exact None. exact None.
    2: exact None. 2: exact None.
    2: exact None. 2: exact None.
    destruct d2.
    exact None. exact None. exact None. exact None. 2: exact None. 2: exact None. 2: exact None. 2: exact None.
    exact (Some (f l l0)).
    exact None.
    exact None.
  Defined.

  Definition rondcoll2 (f:(list data -> list data -> list data)) (d1 d2:data) : option data :=
    lift dcoll (ondcoll2 f d1 d2).

  Definition ondnat {A} (f : Z -> A) (d : data) :=
    match d with
      | dnat n => Some (f n)
      | _ => None
    end.

  Definition ondcoll {A} (f : list data -> A) (d : data) :=
    match d with
      | dcoll l => Some (f l)
      | _ => None
    end.

  Definition lift_oncoll {A} (f : list data -> option A) (d : data) :=
    match d with
      | dcoll l => f l
      | _ => None
    end.

  Definition lift_ondcoll2 (f:list data -> list data -> option (list data)) (d1 d2:data) : option data :=
    match d1,d2 with
      | dcoll l1, dcoll l2 => lift dcoll (f l1 l2)
      | _,_ => None
    end.

  Lemma lift_oncoll_dcoll {A} (f : list data -> option A) (dl : list data) :
    lift_oncoll f (dcoll dl) = f dl.
  Proof. reflexivity. Qed.

  Lemma olift_on_lift_dcoll (f:list data->option data) (d1:option (list data)):
    olift (lift_oncoll f) (lift dcoll d1) =
    olift f d1.
  Proof.
    destruct d1; reflexivity.
  Qed.

  Lemma olift_lift_dcoll (f:list data -> option (list data)) (d1:option (list data)):
    olift (fun c1 : list data => lift dcoll (f c1)) d1 =
    lift dcoll (olift f d1).
  Proof.
    destruct d1; reflexivity.
  Qed.

  Lemma lift_dcoll_inversion d1 d2:
    d1 = d2 -> lift dcoll d1 = lift dcoll d2.
  Proof.
    intros; rewrite H; reflexivity.
  Qed.

  Definition rondcoll (f:list data -> list data) (d:data) : option data :=
    lift dcoll (ondcoll f d).

  Lemma lift_filter_Forall {A} {f:A->option bool} {P} {l x} :
    lift_filter f l = Some x ->
    Forall P l ->
    Forall P x.
  Proof.
    revert x; induction l; simpl.
    - inversion 1; subst; eauto.
    - match_case; intros.
      inversion H1; subst.
      destruct (lift_filter f l); simpl in *; try discriminate; intros.
      destruct b; inversion H0; subst; eauto.
  Qed.
  
  Fixpoint oflat_map {A B} (f : A -> option (list B)) (l:list A) : option (list B) :=
    match l with
      | nil => Some nil
      | x :: t =>
        match f x with
          | None => None
          | Some x' =>
            lift (fun t' => x' ++ t') (oflat_map f t)
        end
    end.

  Fixpoint rmap {A B} (f : A -> option B) (l:list A) : option (list B) :=
    match l with
      | nil => Some nil
      | x :: t =>
        match f x with
          | None => None
          | Some x' =>
            lift (fun t' => x' :: t') (rmap f t)
        end
    end.

  Lemma rmap_Forall {A B} {f:A->option B} {P} {l x} :
    rmap f l = Some x ->
    Forall P l ->
    forall (P2:B->Prop),
    (forall x z, f x = Some z -> P x -> P2 z) ->
    Forall P2 x.
  Proof.
    revert x. induction l; simpl.
    - inversion 1; subst; trivial.
    - match_case; intros.
      inversion H1; subst.
      destruct (rmap f l); simpl in *; try discriminate.
      inversion H0; subst.
      eauto.
  Qed.

  Lemma oflat_map_Forall {A B} {f:A->option (list B)} {P} {l x} :
    oflat_map f l = Some x ->
    Forall P l ->
    forall P2,
    (forall x z, f x = Some z -> P x -> Forall P2 z) ->
    Forall P2 x.
  Proof.
     revert x. induction l; simpl.
    - inversion 1; subst; trivial.
    - match_case; intros.
      inversion H1; subst.
      destruct (oflat_map f l); simpl in *; try discriminate.
      inversion H0; subst.
      apply Forall_app; eauto.
  Qed.

  Lemma rmap_id l:
    rmap (fun d : data => Some d) l = Some l.
  Proof.
    induction l; try reflexivity.
    simpl.
    unfold lift.
    rewrite IHl; reflexivity.
  Qed.
  
  Lemma rmap_map {A} (f:data -> A) l:
    rmap (fun d : data => Some (f d)) l = Some (map f l).
  Proof.
    induction l; try reflexivity.
    simpl.
    unfold lift.
    rewrite IHl; reflexivity.
  Qed.
  
  Lemma rmap_map_merge {A} {B} {C} (f1:A -> B) (f2:B -> option C) (l: list A):
    (rmap (fun d => f2 (f1 d)) l) =
    rmap f2 (map f1 l).
  Proof.
    induction l; intros; simpl; [reflexivity| ].
    destruct (f2 (f1 a)); [|reflexivity].
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma lift_dcoll_cons_rmap d l1 l2 :
    lift dcoll l1 = lift dcoll l2 ->
    lift dcoll (lift (fun t => d :: t) l1) = lift dcoll (lift (fun t => d :: t) l2).
  Proof.
    intros.
    unfold lift in *.
    destruct l1; destruct l2; congruence.
  Qed.

  Lemma rmap_over_app {A B} (f:A -> option B) (l1:list A) (l2:list A) :
    rmap f (l1 ++ l2) = olift2 (fun x y => Some (x++y)) (rmap f l1) (rmap f l2).
  Proof.
    revert l2.
    induction l1; intros.
    - simpl; destruct (rmap f l2); reflexivity.
    - simpl.
      destruct (f a); try reflexivity.
      rewrite IHl1.
      generalize (rmap f l1); generalize (rmap f l2); intros.
      destruct o0; destruct o; reflexivity.
  Qed.

  Lemma rmap_data_exists {A} (f: A -> option data) dl x :
    match rmap f dl with
    | Some a' => Some (dcoll a')
    | None => None
    end = Some x ->
    exists x1, rmap f dl = Some x1 /\ (dcoll x1) = x.
  Proof.
    elim (rmap f dl); intros.
    - exists a; split; [|inversion H]; reflexivity.
    - congruence.
  Qed.

  (* sometimes useful when coq compiler chokes on Fixpoints with rmap *)
  Fixpoint listo_to_olist {a: Type} (l: list (option a)) : option (list a) :=
    match l with
    | nil => Some nil
    | Some x :: xs => match listo_to_olist xs with
                      | None => None
                      | Some xs => Some (x::xs)
                      end
    | None :: xs => None
    end.

  Lemma listo_to_olist_simpl_rmap {A B:Type} (f:A -> option B) (l:list A) :
    rmap f l = (listo_to_olist (map f l)).
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl.
      destruct (f a).
      * rewrite IHl; reflexivity.
      * reflexivity.
  Qed.

  Lemma listo_to_olist_some {A:Type} (l:list (option A)) (l':list A) :
    listo_to_olist l = Some l' ->
    l = (map Some l').
  Proof.
    revert l'.
    induction l; simpl; intros l' eqq.
    - invcs eqq; simpl; trivial.
    - destruct a; try discriminate.
      match_destr_in eqq.
      invcs eqq.
      simpl.
      rewrite <- IHl; trivial.
  Qed.
    
  (* filter, remove, etc *)
  Definition rfilter {A} (f:(string*A) -> bool) (l:list (string*A)) : list (string*A) :=
    filter f l.

  Definition rremove {A} (l:list (string*A)) (s:string) : list (string*A) :=
    filter (fun x => if string_dec s (fst x) then false else true) l.

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

  Lemma rondcoll2_dcoll f (l1 l2:list data):
    rondcoll2 f (dcoll l1) (dcoll l2) = Some (dcoll (f l1 l2)).
  Proof. reflexivity. Qed.
  
  Lemma rondcoll_dcoll f (l:list data):
    rondcoll f (dcoll l) = Some (dcoll (f l)).
  Proof. reflexivity. Qed.
  
  Lemma ondcoll_dcoll {A} (f:list data -> A) (l:list data):
    ondcoll f (dcoll l) = Some (f l).
  Proof. reflexivity. Qed.
  
  Lemma dcoll_map_app {A} (f:A -> data) (l1 l2:list A) :
    Some (dcoll (map f l1 ++ map f l2)) = rondcoll2 bunion (dcoll (map f l1)) (dcoll (map f l2)).
  Proof. reflexivity. Qed.

  Definition orecconcat (a:data) (x:data) :=
    match a with
      | drec r2 =>
        match x with
          | drec r1 => Some (drec (rec_concat_sort r2 r1))
          | _ => None
        end
      | _ => None
    end.
  
  Definition omap_concat (a:data) (d1:list data) : option (list data) :=
    rmap (fun x => orecconcat a x) d1.

  Definition oomap_concat
             (f:data -> option data)
             (a:data) :=
    match f a with
      | Some (dcoll y) => omap_concat a y
      | _ => None
    end.

  Definition rmap_product (f:data -> option data) (d:list data) : option (list data) :=
    oflat_map (oomap_concat f) d.

  Lemma rmap_product_cons f d a x y :
    rmap_product f d = Some x ->
    (oomap_concat f a) = Some y ->
    rmap_product f (a :: d) = Some (y ++ x).
  Proof.
    intros.
    induction d.
    - unfold rmap_product in *; simpl in *.
      rewrite H0; inversion H; reflexivity.
    - unfold rmap_product in *.
      simpl in *.
      revert H; elim (oomap_concat f a0); intros; simpl in *; try congruence.
      rewrite H0 in *; simpl in *.
      rewrite H.
      reflexivity.
  Qed.

  Lemma rmap_product_cons_none f d a :
    rmap_product f d = None -> rmap_product f ((drec a) :: d) = None.
  Proof.
    intros.
    unfold rmap_product, oflat_map in *.
    destruct (oomap_concat f (drec a)).
    - revert H. elim (oflat_map
                      (fun x : data =>
                         oomap_concat f x) d);
      intros; simpl in *; rewrite H; reflexivity.
    - reflexivity.
  Qed.

  Lemma rmap_product_cons_none_first f d a :
    (oomap_concat f a) = None -> rmap_product f (a :: d) = None.
  Proof.
    intros.
    unfold rmap_product, oflat_map in *.
    destruct (oomap_concat f a); [congruence|reflexivity].
  Qed.

  Lemma rmap_product_cons_inv f d a l :
    rmap_product f (a :: d) = Some l ->
    exists x, exists y,
        (oomap_concat f a) = Some x /\
        rmap_product f d = Some y /\
        x ++ y = l.
  Proof.
    intros.
    case_eq (rmap_product f d); intros;
    case_eq (oomap_concat f a); intros;
      unfold rmap_product in *;
      unfold oflat_map in *;
      rewrite H0 in H; simpl in ; clear H0.
    - rewrite H1 in H; simpl in H.
      inversion H; subst.
      exists l1; exists l0.
      split; [reflexivity|]; split; reflexivity.
    - rewrite H1 in H; simpl in H; congruence.
    - rewrite H1 in H; simpl in H; congruence.
    - rewrite H1 in H; simpl in H; congruence.
  Qed.

  Definition rproduct (d1 d2:list data) : option (list data) :=
    oflat_map (fun x => omap_concat x d2) d1.
  
  Lemma rproduct_cons (d1 d2:list data) a x y:
    rproduct d1 d2 = Some x ->
    (omap_concat a d2) = Some y ->
    rproduct (a::d1) d2 = Some (y ++ x).
  Proof.
    intros.
    induction d2.
    - unfold rproduct in *; simpl in *.
      rewrite H; inversion H0; reflexivity.
    - unfold rproduct in *. simpl in *.
      rewrite H0.
      rewrite H in *; simpl in *; reflexivity.
  Qed.

  Definition rflatten (d:list data) : option (list data) :=
    oflat_map (fun x =>
                 match x with
                   | dcoll y => Some y
                   | _ => None end) d.

  Lemma rflatten_cons (l:list data) rest r' :
    rflatten rest = Some r' ->
    rflatten ((dcoll l) :: rest) = Some (l ++ r').
  Proof.
    intros.
    induction l; unfold rflatten in *; simpl; rewrite H; reflexivity.
  Qed.

  Lemma rflatten_app (l1 l2:list data) r1 r2 :
    rflatten l1 = Some r1 ->
    rflatten l2 = Some r2 ->
    rflatten (l1 ++ l2) = Some (r1 ++ r2).
  Proof.
    revert l2 r1 r2.
    induction l1; simpl in *; intros.
    - inversion H; subst. simpl. trivial.
    -  destruct a; simpl in *; inversion H.
       unfold rflatten in *.
       simpl in H2.
       apply some_lift in H2.
       destruct H2 as [? eqq ?]; subst.
       simpl.
       erewrite IHl1; eauto.
       simpl.
       rewrite ass_app.
       trivial.
  Qed.

  Lemma rflatten_map_dcoll_id coll :
    rflatten (map (fun d : data => dcoll (d::nil)) coll) = Some coll.
  Proof.
    induction coll.
    reflexivity.
    simpl.
    assert (a::coll = (a::nil)++coll) by reflexivity.
    rewrite H.
    apply rflatten_cons.
    assumption.
  Qed.

  Lemma rflatten_cons_none (d:data) rest :
    rflatten rest = None ->
    rflatten (d :: rest) = None.
  Proof.
    intros.
    destruct d; try reflexivity.
    unfold rflatten in *; unfold oflat_map in *; simpl in *.
    rewrite H. reflexivity.
  Qed.

  Lemma rflatten_app_none1 l1 l2 :
    rflatten l1 = None ->
    rflatten (l1 ++ l2) = None.
  Proof.
    revert l2.
    induction l1; simpl.
    - inversion 1.
    - intros.
      destruct a; simpl; try reflexivity.
      unfold rflatten in *.
      simpl in *.
      apply none_lift in H.
      rewrite IHl1; eauto.
  Qed.    

  Lemma rflatten_app_none2 l1 l2 :
    rflatten l2 = None ->
    rflatten (l1 ++ l2) = None.
  Proof.
    revert l2.
    induction l1; simpl.
    - trivial.
    - intros.
      destruct a; simpl; try reflexivity.
      unfold rflatten in *.
      simpl in *.
      apply lift_none.
      eauto.
  Qed.    
  
  Definition rif {A} (e:A -> option bool) (a:A) : option (list A) :=
    match (e a) with
      | None => None
      | Some b =>
        if b then Some (a::nil) else Some nil
    end.

  Definition lrflatten {A} : option (list (list A)) -> option (list A) :=
    lift lflatten.

  Definition orfilter {A} (f:A -> option bool) (ol:option (list A)) : option (list A) :=
    olift (lift_filter f) ol.
 
  Lemma filter_eq_flatten_if {A} (e:A -> option bool) (ol:option (list A)) :
    orfilter e ol = lrflatten (olift (rmap (rif e)) ol).
  Proof.
    destruct ol; try reflexivity.
    induction l.
    reflexivity.
    simpl.
    unfold rif in *.
    destruct (e a); try reflexivity.
    destruct b; simpl in *; rewrite IHl; clear IHl;
    generalize ((rmap
          (fun a0 : A =>
           match e a0 with
           | Some true => Some [a0]
           | Some false => Some []
           | None => None
           end) l)); intros;
    destruct o; reflexivity.
  Qed.

 Definition oand (x1 x2: option bool) : option bool :=
    match x1 with
      | None => None
      | Some b1 =>
        match x2 with
          | None => None
          | Some b2 => Some (andb b1 b2)
        end
    end.

  Lemma rmap_ext  {A B : Type} (f g : A -> option B) (l : list A) :
    (forall x, In x l -> f x = g x) ->
    rmap f l = rmap g l.
  Proof.
    induction l; simpl; trivial; intros.
    rewrite IHl by intuition.
    rewrite (H a) by intuition.
    trivial.
  Qed.

  Lemma oflat_map_ext {A B} (f g:A->option (list B)) l :
    (forall x, In x l -> f x = g x) ->
    oflat_map f l = oflat_map g l.
  Proof.
    induction l; simpl; trivial; intros.
    rewrite IHl by intuition.
    rewrite (H a) by intuition.
    trivial.
  Qed.

  Lemma oomap_concat_ext_weak f g a :
    (f a = g a) ->
    oomap_concat f a = oomap_concat g a.
  Proof.
    unfold oomap_concat.
    intros.
    rewrite H. trivial.
  Qed.
  
  Lemma rmap_product_ext  f g l :
    (forall x, In x l -> f x = g x) ->
    rmap_product f l = rmap_product g l.
  Proof.
    unfold rmap_product.
    intros.
    apply oflat_map_ext; intros.
    apply oomap_concat_ext_weak.
    auto.
  Qed.

  Lemma olift_ext {A B : Type} (f g : A -> option B) (x : option A) :
    (forall a, x = Some a -> f a = g a) ->
    olift f x = olift g x.
  Proof.
    destruct x; simpl; auto.
  Qed.

  Lemma lift_oncoll_ext {A : Type} (f g : list data -> option A) (d : data) :
    (forall a, d = dcoll a -> f a = g a) ->
    lift_oncoll f d = lift_oncoll g d.
  Proof.
    destruct d; simpl; auto.
  Qed.

  Lemma lift_filter_ext {A : Type} (f g : A -> option bool) (l : list A) : 
    (forall x, In x l -> f x = g x) ->
    lift_filter f l = lift_filter g l.
  Proof.
    induction l; simpl; trivial; intros.
    rewrite IHl by intuition.
    rewrite (H a) by intuition.
    trivial.
  Qed.

  Lemma rmap_map_fusion {A B C}
        (f:B->option C) (g:A -> B) (l:list A) :
    rmap f (map g l) = rmap (fun x => f (g x)) l.
  Proof.
    induction l; simpl; trivial.
    match_destr. rewrite IHl; trivial.
  Qed.

  Definition recconcat (r1 r2:list (string*data)) :=
    rec_concat_sort r1 r2.
  
  Definition map_concat (r2:list (string*data)) (d:list (list (string*data))) :=
    map (fun x => recconcat r2 x) d.

  Definition product (d1 d2:list (list (string*data))) :=
    (flat_map (fun x => map_concat x d2) d1).

  Definition ldeqt := (@Permutation (list (string*data))).

  Notation "b1 ⊖ b2" := (bminus b2 b1) (right associativity, at level 70) : rbag_scope.    (* ⊖ = \ominus *)
  
  Lemma lift_empty_dcoll l :
    olift rflatten (lift (fun t' : list data => dcoll nil :: t') l) = olift rflatten l.
  Proof.
    destruct l.
    simpl.
    unfold rflatten.
    simpl.
    apply lift_id.
    reflexivity.
  Qed.

  Lemma lift_cons_dcoll a l:
    olift rflatten
          (lift (fun t' : list data => dcoll [a] :: t') l) =
    lift (fun t' => a::t') (olift rflatten l).
  Proof.
    destruct l; simpl; try reflexivity.
  Qed.

  Lemma rflatten_through_match l1 l2:
     olift rflatten
     match lift dcoll (Some l1) with
     | Some x' =>
         lift (fun t' : list data => x' :: t') l2
     | None => None
     end =
   lift (fun t' : list data => l1 ++ t')
     (olift rflatten l2).
  Proof.
    unfold olift, lift.
    induction l2; [unfold rflatten|idtac]; reflexivity.
  Qed.

  Section Denotational.
    Inductive rec_concat_sem: data -> data -> data -> Prop :=
    | sem_rec_concat:
        forall r1 r2,
          rec_concat_sem (drec r1) (drec r2)
                         (drec (rec_concat_sort r1 r2)).

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

    (** Semantics of the [map_concat] operator. It takes a record [d]
     and a collection of record [c], and returns a new collection of
     records [c'] where [d] has been concatenated to all the records
     in [c]. *)

    Inductive map_concat_sem: data -> list data -> list data -> Prop :=
    | sem_map_concat_empty : forall d,
        map_concat_sem d nil nil                     (**r   [d χ⊕ {} ⇓ {}] *)
    | sem_map_concat_cons : forall d d1 d2 c1 c2,
        rec_concat_sem d d1 d2 ->                    (**r   [d ⊕ d₁ ⇓ d₂] *)
        map_concat_sem d c1 c2 ->                    (**r ∧ [d χ⊕ {c₁} ⇓ {c₂}] *)
        map_concat_sem d (d1::c1) (d2::c2).          (**r ⇒ [d χ⊕ {d₁::c₁} ⇓ {d₂::c₂}] *)
    
    (* [omap_concat] is correct and complete wrt. the [map_concat_sem]
       semantics. *)
      
    Lemma omap_concat_correct d c1 c2:
      omap_concat d c1 = Some c2 ->
      map_concat_sem d c1 c2.
    Proof.
      unfold omap_concat.
      revert c2.
      induction c1; simpl; intros.
      - inversion H; subst; econstructor.
      - case_eq (orecconcat d a); intros; rewrite H0 in *; [|congruence].
        rewrite orecconcat_correct_and_complete in H0.
        unfold lift in H.
        case_eq (rmap (fun x : data => orecconcat d x) c1); intros;
          rewrite H1 in *; clear H1; [|congruence].
        inversion H; subst; clear H.
        specialize (IHc1 l eq_refl).
        econstructor; eauto.
    Qed.
      
    Lemma omap_concat_complete d c1 c2:
      map_concat_sem d c1 c2 ->
      omap_concat d c1 = Some c2.
    Proof.
      unfold omap_concat.
      revert c2.
      induction c1; simpl; intros.
      - inversion H; reflexivity.
      - inversion H; subst; simpl in *.
        rewrite <- orecconcat_correct_and_complete in H3.
        rewrite H3; simpl.
        unfold lift.
        rewrite (IHc1 c3 H5); reflexivity.
    Qed.
      
    Lemma omap_concat_correct_and_complete d c1 c2:
      omap_concat d c1 = Some c2 <->
      map_concat_sem d c1 c2.
    Proof.
      split.
      apply omap_concat_correct.
      apply omap_concat_complete.
    Qed.

    (** Semantics of the [product] operator. It takes two collections
     of records [c₁] and [c₂] and returns the Cartesian product. *)

    Inductive product_sem: list data -> list data -> list data -> Prop :=
    | sem_product_empty : forall c,
        product_sem nil c nil                   (**r   [{c} × {} ⇓ {}] *)
    | sem_product_cons : forall d1 c1 c2 c3 c4,
        map_concat_sem d1 c2 c3 ->              (**r ∧ [d₁ χ⊕ {c₂} ⇓ {c₃}] *)
        product_sem c1 c2 c4 ->                 (**r ∧ [{c₁} × {c₂} ⇓ {c₄}] *)
        product_sem (d1::c1) c2 (c3 ++ c4).     (**r ⇒ [{d₁::c₁} × {c₂} ⇓ {c₃}∪{c₄}] *)

    (* [rproduct] is correct and complete wrt. the [product_sem]
     semantics. *)
      
    Lemma rproduct_correct c1 c2 c3:
      rproduct c1 c2 = Some c3 ->
      product_sem c1 c2 c3.
    Proof.
      unfold rproduct.
      revert c2 c3.
      induction c1; simpl; intros.
      - inversion H; econstructor.
      - case_eq (omap_concat a c2); intros; rewrite H0 in *; [|congruence].
        unfold lift in H.
        case_eq (oflat_map (fun x : data => omap_concat x c2) c1);
          intros; rewrite H1 in *; [|congruence].
        inversion H; subst; clear H.
        specialize (IHc1 c2 l0 H1).
        econstructor;[|assumption].
        rewrite omap_concat_correct_and_complete in H0;assumption.
    Qed.

    Lemma rproduct_complete c1 c2 c3:
      product_sem c1 c2 c3 ->
      rproduct c1 c2 = Some c3.
    Proof.
      unfold rproduct.
      revert c2 c3.
      induction c1; simpl; intros.
      - inversion H; subst; reflexivity.
      - inversion H; subst.
        rewrite <- omap_concat_correct_and_complete in H2.
        rewrite H2.
        unfold lift; rewrite (IHc1 c2 c6 H5).
        reflexivity.
    Qed.

    Lemma rproduct_correct_and_complete c1 c2 c3:
      rproduct c1 c2 = Some c3 <->
      product_sem c1 c2 c3.
    Proof.
      split.
      apply rproduct_correct.
      apply rproduct_complete.
    Qed.

  End Denotational.

End RRelation.

Section Misc.
  Lemma in_rec_sort_insert {A} `{EqDec A eq} (x:string * A) (s:string) (a:A) l:
    In x (insertion_sort_insert rec_field_lt_dec (s, a) l) ->
    x = (s, a) \/ In x l.
  Proof.
    revert x a. induction l; simpl; [intuition | ].
    intros x a0.
    destruct a; simpl in *.
    destruct (StringOrder.lt_dec s s0); simpl; intros; trivial.
    - elim H0; clear H0; intros; [left|]; auto.
    - destruct (StringOrder.lt_dec s0 s); simpl; intros; intuition.
      simpl in H0.
      elim H0; clear H0; intros.
      + intuition.
      + destruct (IHl _ _ H0); intuition.
  Qed.

End Misc.



Require Import Permutation.

Section MergeBindings.

  (* Merge record stuff *)

  Definition merge_bindings {A} `{EqDec A eq} (l₁ l₂:list (string * A)) : option (list (string * A)) :=
    if compatible l₁ l₂
    then Some (rec_concat_sort l₁ l₂)
    else None.

  Lemma merge_bindings_nil_r {A} `{EqDec A eq} l : merge_bindings l nil = Some (rec_sort l).
  Proof.
    unfold merge_bindings.
    simpl.
    rewrite compatible_nil_r.
    unfold rec_concat_sort.
    rewrite app_nil_r.
    trivial.
  Qed.

  Lemma merge_bindings_single_nin {A} `{EqDec A eq} b x d :
    ~ In x (domain b) ->
    merge_bindings b ((x,d)::nil) =
    Some (rec_concat_sort b ((x,d)::nil)).
  Proof.
    intro nin.
    unfold merge_bindings.
    rewrite compatible_single_nin; auto.
  Qed.

  Lemma merge_bindings_sorted {A} `{EqDec A eq} {g g1 g2} :
    Some g = merge_bindings g1 g2 ->
    is_list_sorted ODT_lt_dec (@domain string A g) = true.
  Proof.
    unfold merge_bindings. intros.
    destruct (compatible g1 g2); try discriminate.
    inversion H0; subst.
    unfold rec_concat_sort, rec_concat_sort in *.
    eauto.
  Qed.

  Lemma edot_merge_bindings {A} `{EqDec A eq} (l1 l2:list (string*A)) (s:string) (x:A) :
    merge_bindings l1 [(s, x)] = Some l2 ->
    edot l2 s = Some x.
  Proof.
    intros.
    unfold merge_bindings in *.
    case_eq (compatible l1 [(s, x)]); intros; rewrite H1 in *; try congruence.
    inversion H0; clear H0.
    unfold edot.
    unfold rec_concat_sort in *.
    rewrite (@assoc_lookupr_drec_sort string ODT_string) in *.
    rewrite (@assoc_lookupr_app).
    simpl.
    destruct (string_eqdec s s); [reflexivity|congruence].
  Qed.

  Lemma merge_bindings_nodup {A} `{EqDec A eq} (l l0 l1:list (string*A)):
    merge_bindings l l0 = Some l1 -> NoDup (domain l1).
  Proof.
    intros.
    unfold merge_bindings in *.
    destruct (compatible l l0); try congruence.
    inversion H0.
    apply is_list_sorted_NoDup_strlt.
    apply (rec_concat_sort_sorted l l0).
    reflexivity.
  Qed.

  Lemma merge_bindings_compatible {A} `{EqDec A eq} (l l0 l1:list (string*A)):
    merge_bindings l l0 = Some l1 -> compatible l l0 = true.
  Proof.
    intros.
    unfold merge_bindings in H0.
    destruct (compatible l l0); congruence.
  Qed.

  Lemma sorted_cons_is_compatible {A} `{EqDec A eq} (l:list (string*A)) (a:string*A):
    is_list_sorted ODT_lt_dec (domain (a :: l)) = true ->
    compatible_with (fst a) (snd a) l = true.
  Proof.
    intros.
    assert (NoDup (domain (a :: l)))
      by (apply is_list_sorted_NoDup_strlt; assumption).
    unfold compatible_with.
    destruct a; simpl.
    inversion H1. subst.
    assert (assoc_lookupr equiv_dec l s = None) by
        (apply assoc_lookupr_nin_none; assumption).
    rewrite H2.
    reflexivity.
  Qed.

  Lemma compatible_self {A} `{EqDec A eq} (l:list (string*A)):
    is_list_sorted ODT_lt_dec (domain l) = true ->
    compatible l l = true.
  Proof.
    intros.
    induction l; try reflexivity.
    assert (is_list_sorted ODT_lt_dec (domain l) = true)
      by (apply (@rec_sorted_skip_first string ODT_string _ l a); assumption).
    assert (NoDup (domain (a::l)))
      by (apply is_list_sorted_NoDup_strlt; assumption).
    inversion H2. subst.
    specialize (IHl H1).
    simpl. rewrite andb_true_inversion.
    destruct a; simpl.
    unfold compatible_with; simpl.
    assert (assoc_lookupr equiv_dec l s = None) by
        (apply assoc_lookupr_nin_none; assumption).
    rewrite H3.
    destruct (equiv_dec s s); try congruence.
    destruct (equiv_dec a a); try congruence.
    split; try reflexivity.
    apply compatible_cons_r; try assumption.
    simpl.
    unfold compatible_with.
    assert (assoc_lookupr equiv_dec l s = None) by
        (apply assoc_lookupr_nin_none; assumption).
    rewrite H4; reflexivity.
  Qed.

  Lemma merge_self_sorted {A} `{EqDec A eq} (l:list (string*A)):
    is_list_sorted ODT_lt_dec (domain l) = true ->
    merge_bindings l l = Some l.
  Proof.
    intros.
    unfold merge_bindings.
    rewrite compatible_self; try assumption.
    f_equal.
    apply rec_concat_sort_self; assumption.
  Qed.

  Lemma merge_self_sorted_r {A} `{EqDec A eq} (l:list (string*A)):
    is_list_sorted ODT_lt_dec (domain l) = true ->
    merge_bindings l (rec_sort l) = Some (rec_sort l).
  Proof.
    intros.
    rewrite rec_sorted_id; try assumption.
    apply merge_self_sorted; assumption.
  Qed.

  Lemma same_domain_merge_bindings_eq
        {A} `{EqDec A eq} (l₁ l₂ l₃:list (string*A)) :
    NoDup (domain l₁) ->
    domain l₁ = domain l₂ ->
    merge_bindings l₁ l₂ = Some l₃ ->
    l₁ = l₂.
  Proof.
    unfold merge_bindings.
    match_case; intros compat nd eqd eqq.
    invcs eqq.
    apply (same_domain_compatible _ _ nd eqd compat).
  Qed.

  Definition compatible {A:Type} `{x:EqDec A eq} := @compatible string A _ _ _ _.
  
  Lemma merge_returns_compatible {A} `{equiv:EqDec A eq} (l1 l2 l3:list (string*A)):
    is_list_sorted ODT_lt_dec (domain l1) = true ->
    is_list_sorted ODT_lt_dec (domain l2) = true ->
    compatible l1 l2 = true ->
    rec_concat_sort l1 l2 = l3 ->
    compatible l1 l3 = true.
  Proof.
    intros.
    assert (NoDup (domain l1)) by (apply is_list_sorted_NoDup_strlt; assumption).
    assert (NoDup (domain l2)) by (apply is_list_sorted_NoDup_strlt; assumption).
    unfold merge_bindings in H2.
    unfold compatible, Compat.compatible in *.
    rewrite forallb_forall in H1.
    rewrite forallb_forall; intros.
    destruct x; simpl in *.
    specialize (H1 (s,a) H5).
    simpl in *.
    rewrite <- H2.
    unfold compatible_with in *.
    unfold rec_concat_sort.
    rewrite (@assoc_lookupr_drec_sort string ODT_string).
    simpl in *; unfold equiv_dec, string_eqdec in *.
    rewrite (@assoc_lookupr_app string).
    case_eq (assoc_lookupr string_dec l2 s); intros.
    assert ((@assoc_lookupr string A
                            (@Equivalence.equiv string (@eq string)
                                                (@eq_equivalence string))
                            (@complement string
                                         (@Equivalence.equiv string (@eq string)
                                                             (@eq_equivalence string))) string_dec l2 s ) =
            (@assoc_lookupr string A (@eq string)
                            (fun s1 s2 : string => not (@eq string s1 s2)) string_dec l2 s)) by reflexivity.
    rewrite H7 in *.
    rewrite H6 in H1.
    - assumption.
    - assert (assoc_lookupr string_dec l1 s = Some a).
      apply in_assoc_lookupr_nodup; assumption.
      unfold string_eqdec.
      rewrite H7.
      destruct (equiv a a); congruence.
  Qed.
  
  Lemma merge_idem {A} `{EqDec A eq} (l l0 l1:list (string*A)):
    is_list_sorted ODT_lt_dec (domain l) = true ->
    is_list_sorted ODT_lt_dec (domain l0) = true ->
    merge_bindings l l0 = Some l1 ->
    merge_bindings l l1 = Some l1.
  Proof.
    intros.
    unfold merge_bindings in *.
    case_eq (compatible l l0); intros;
    unfold compatible in *; rewrite H3 in H2; try congruence.
    inversion H2; clear H2.
    assert (compatible l (rec_concat_sort l l0) = true)
      by (apply (merge_returns_compatible l l0 (rec_concat_sort l l0) H0 H1 H3); reflexivity).
    unfold compatible in *. rewrite H2.
    rewrite rec_concat_sort_idem; try assumption; reflexivity.
  Qed.

  (* merge_idem isn't true unless l is without duplicates! Here is a
     counter example.
   Open Scope string.
   Definition tup1 := ("a",1) :: ("b",2) :: ("a", 3) :: nil.
   Definition tup2 := ("c",2) :: nil.
   Eval compute in (merge_bindings tup1 tup2).
   Definition tup3 := [("a", 3); ("b", 2); ("c", 2)].
   Eval compute in (compatible tup1 tup3).
   *)

End MergeBindings.

Section RRemove.
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

End RRemove.

Section RProject.
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

End RProject.

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
  
  Context {fdata:foreign_data}.

  Lemma rmap_with_rproject sl l :
    (rmap
       (fun d1 : data =>
          match d1 with
          | dunit => None
          | dnat _ => None
          | dbool _ => None
          | dstring _ => None
          | dcoll _ => None
          | drec r => Some (drec (rproject r sl))
          | dleft _ => None
          | dright _ => None
          | dbrand _ _ => None
          | dforeign _ => None
          end) l) =
    (rmap
       (fun d1 : data =>
          olift
            (fun d0 : data =>
               match d0 with
               | dunit => None
               | dnat _ => None
               | dbool _ => None
               | dstring _ => None
               | dcoll _ => None
               | drec r => Some (drec (rproject r sl))
               | dleft _ => None
               | dright _ => None
               | dbrand _ _ => None
               | dforeign _ => None
               end) (Some d1)) l).
  Proof.
    apply rmap_ext; intros.
    reflexivity.
  Qed.
    
End SRProject.

Hint Resolve @merge_bindings_sorted.
Hint Rewrite @rondcoll2_dcoll : alg.
Hint Rewrite @rondcoll_dcoll : alg.
Hint Rewrite @ondcoll_dcoll : alg.
Hint Rewrite @lift_oncoll_dcoll : alg.
Hint Rewrite @olift_on_lift_dcoll : alg.
Hint Rewrite @olift_lift_dcoll : alg.
Hint Rewrite @rmap_id : alg.
Hint Rewrite @rmap_map : alg.
Hint Rewrite @lift_dcoll_cons_rmap : alg.
Hint Rewrite @rflatten_map_dcoll_id : alg.

Notation "X ≅ Y" := (ldeq X Y) (at level 70) : rbag_scope.                             (* ≅ = \cong *)
Notation "b1 ⊎ b2" := (bunion b2 b1) (right associativity, at level 70) : rbag_scope.    (* ⊎ = \uplus *)
Notation "b1 ⊖ b2" := (bminus b2 b1) (right associativity, at level 70) : rbag_scope.    (* ⊖ = \ominus *)
Notation "b1 × b2" := (rproduct b1 b2) (right associativity, at level 70) : rbag_scope.   (* × = \times *)
Notation "b1 min-b b2" := (bmin b1 b2) (right associativity, at level 70) : rbag_scope.
Notation "b1 max-b b2" := (bmax b1 b2) (right associativity, at level 70) : rbag_scope.
Notation "distinct-b b1" := (bdistinct b1) (right associativity, at level 70) : rbag_scope.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
