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
Require Import RecOperators.

Section Iterators.

  Context {fdata:foreign_data}.

  Section MapUtils.
    Lemma lift_map_data_exists {A} (f: A -> option data) dl x :
      match lift_map f dl with
      | Some a' => Some (dcoll a')
      | None => None
      end = Some x ->
      exists x1, lift_map f dl = Some x1 /\ (dcoll x1) = x.
    Proof.
      elim (lift_map f dl); intros.
      - exists a; split; [|inversion H]; reflexivity.
      - congruence.
    Qed.

    Lemma lift_map_with_rproject sl l :
      (lift_map
         (fun d1 : data =>
            match d1 with
            | dunit => None
            | dnat _ => None
            | dfloat _ => None
            | dbool _ => None
            | dstring _ => None
            | dcoll _ => None
            | drec r => Some (drec (rproject r sl))
            | dleft _ => None
            | dright _ => None
            | dbrand _ _ => None
            | dforeign _ => None
            end) l) =
      (lift_map
         (fun d1 : data =>
            olift
              (fun d0 : data =>
                 match d0 with
                 | dunit => None
                 | dnat _ => None
                 | dfloat _ => None
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
      apply lift_map_ext; intros.
      reflexivity.
    Qed.
  End MapUtils.

  Section MapConcatUtils.
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
    
    Definition omap_concat (a:data) (d1:list data) : option (list data) :=
      lift_map (fun x => orecconcat a x) d1.

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
        case_eq (lift_map (fun x : data => orecconcat d x) c1); intros;
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

  End MapConcatUtils.

  Section MapProductUtils.
    (** Auxiliary function used in the definition of lifted map-product *)
    Definition oncoll_map_concat
               (f:data -> option data)
               (a:data) :=
      match f a with
      | Some (dcoll y) => omap_concat a y
      | _ => None
      end.

    Lemma oncoll_map_concat_ext_weak f g a :
      (f a = g a) ->
      oncoll_map_concat f a = oncoll_map_concat g a.
    Proof.
      unfold oncoll_map_concat.
      intros.
      rewrite H. trivial.
    Qed.
  
    Definition omap_product (f:data -> option data) (d:list data) : option (list data) :=
      lift_flat_map (oncoll_map_concat f) d.

    Lemma omap_product_cons f d a x y :
      omap_product f d = Some x ->
      (oncoll_map_concat f a) = Some y ->
      omap_product f (a :: d) = Some (y ++ x).
    Proof.
      intros.
      induction d.
      - unfold omap_product in *; simpl in *.
        rewrite H0; inversion H; reflexivity.
      - unfold omap_product in *.
        simpl in *.
        revert H; elim (oncoll_map_concat f a0); intros; simpl in *; try congruence.
        rewrite H0 in *; simpl in *.
        rewrite H.
        reflexivity.
    Qed.

    Lemma omap_product_cons_none f d a :
      omap_product f d = None -> omap_product f ((drec a) :: d) = None.
    Proof.
      intros.
      unfold omap_product, lift_flat_map in *.
      destruct (oncoll_map_concat f (drec a)).
      - revert H. elim (lift_flat_map
                          (fun x : data =>
                             oncoll_map_concat f x) d);
                    intros; simpl in *; rewrite H; reflexivity.
      - reflexivity.
    Qed.

    Lemma omap_product_cons_none_first f d a :
      (oncoll_map_concat f a) = None -> omap_product f (a :: d) = None.
    Proof.
      intros.
      unfold omap_product, lift_flat_map in *.
      destruct (oncoll_map_concat f a); [congruence|reflexivity].
    Qed.

    Lemma omap_product_cons_inv f d a l :
      omap_product f (a :: d) = Some l ->
      exists x, exists y,
          (oncoll_map_concat f a) = Some x /\
          omap_product f d = Some y /\
          x ++ y = l.
    Proof.
      intros.
      case_eq (omap_product f d); intros;
        case_eq (oncoll_map_concat f a); intros;
          unfold omap_product in *;
          unfold lift_flat_map in *;
          rewrite H0 in H; simpl in ; clear H0.
      - rewrite H1 in H; simpl in H.
        inversion H; subst.
        exists l1; exists l0.
        split; [reflexivity|]; split; reflexivity.
      - rewrite H1 in H; simpl in H; congruence.
      - rewrite H1 in H; simpl in H; congruence.
      - rewrite H1 in H; simpl in H; congruence.
    Qed.

    Lemma omap_product_ext  f g l :
      (forall x, In x l -> f x = g x) ->
      omap_product f l = omap_product g l.
    Proof.
      unfold omap_product.
      intros.
      apply lift_flat_map_ext; intros.
      apply oncoll_map_concat_ext_weak.
      auto.
    Qed.

  End MapProductUtils.

  Section ProductUtils.
    (** Semantics of the [product] operator. It takes two collections
     of records [c₁] and [c₂] and returns the Cartesian product. *)

    Inductive product_sem: list data -> list data -> list data -> Prop :=
    | sem_product_empty : forall c,
        product_sem nil c nil                   (**r   [{c} × {} ⇓ {}] *)
    | sem_product_cons : forall d1 c1 c2 c3 c4,
        map_concat_sem d1 c2 c3 ->              (**r ∧ [d₁ χ⊕ {c₂} ⇓ {c₃}] *)
        product_sem c1 c2 c4 ->                 (**r ∧ [{c₁} × {c₂} ⇓ {c₄}] *)
        product_sem (d1::c1) c2 (c3 ++ c4).     (**r ⇒ [{d₁::c₁} × {c₂} ⇓ {c₃}∪{c₄}] *)

    Definition oproduct (d1 d2:list data) : option (list data) :=
      lift_flat_map (fun x => omap_concat x d2) d1.
  
    Lemma oproduct_cons (d1 d2:list data) a x y:
      oproduct d1 d2 = Some x ->
      (omap_concat a d2) = Some y ->
      oproduct (a::d1) d2 = Some (y ++ x).
    Proof.
      intros.
      induction d2.
      - unfold oproduct in *; simpl in *.
        rewrite H; inversion H0; reflexivity.
      - unfold oproduct in *. simpl in *.
        rewrite H0.
        rewrite H in *; simpl in *; reflexivity.
    Qed.

    (* [oproduct] is correct and complete wrt. the [product_sem]
    semantics. *)
      
    Lemma oproduct_correct c1 c2 c3:
      oproduct c1 c2 = Some c3 ->
      product_sem c1 c2 c3.
    Proof.
      unfold oproduct.
      revert c2 c3.
      induction c1; simpl; intros.
      - inversion H; econstructor.
      - case_eq (omap_concat a c2); intros; rewrite H0 in *; [|congruence].
        unfold lift in H.
        case_eq (lift_flat_map (fun x : data => omap_concat x c2) c1);
          intros; rewrite H1 in *; [|congruence].
        inversion H; subst; clear H.
        specialize (IHc1 c2 l0 H1).
        econstructor;[|assumption].
        rewrite omap_concat_correct_and_complete in H0;assumption.
    Qed.

    Lemma oproduct_complete c1 c2 c3:
      product_sem c1 c2 c3 ->
      oproduct c1 c2 = Some c3.
    Proof.
      unfold oproduct.
      revert c2 c3.
      induction c1; simpl; intros.
      - inversion H; subst; reflexivity.
      - inversion H; subst.
        rewrite <- omap_concat_correct_and_complete in H2.
        rewrite H2.
        unfold lift; rewrite (IHc1 c2 c6 H5).
        reflexivity.
    Qed.

    Lemma oproduct_correct_and_complete c1 c2 c3:
      oproduct c1 c2 = Some c3 <->
      product_sem c1 c2 c3.
    Proof.
      split.
      apply oproduct_correct.
      apply oproduct_complete.
    Qed.

  End ProductUtils.

  Section FlattenUtils.
    Definition oflatten (d:list data) : option (list data) :=
      lift_flat_map (fun x =>
                   match x with
                   | dcoll y => Some y
                   | _ => None end) d.

    Lemma oflatten_cons (l:list data) rest r' :
      oflatten rest = Some r' ->
      oflatten ((dcoll l) :: rest) = Some (l ++ r').
    Proof.
      intros.
      induction l; unfold oflatten in *; simpl; rewrite H; reflexivity.
    Qed.

    Lemma oflatten_app (l1 l2:list data) r1 r2 :
      oflatten l1 = Some r1 ->
      oflatten l2 = Some r2 ->
      oflatten (l1 ++ l2) = Some (r1 ++ r2).
    Proof.
      revert l2 r1 r2.
      induction l1; simpl in *; intros.
      - inversion H; subst. simpl. trivial.
      -  destruct a; simpl in *; inversion H.
         unfold oflatten in *.
         simpl in H2.
         apply some_lift in H2.
         destruct H2 as [? eqq ?]; subst.
         simpl.
         erewrite IHl1; eauto.
         simpl.
         rewrite ass_app.
         trivial.
    Qed.

    Lemma oflatten_map_dcoll_id coll :
      oflatten (map (fun d : data => dcoll (d::nil)) coll) = Some coll.
    Proof.
      induction coll.
      reflexivity.
      simpl.
      assert (a::coll = (a::nil)++coll) by reflexivity.
      rewrite H.
      apply oflatten_cons.
      assumption.
    Qed.

    Lemma oflatten_cons_none (d:data) rest :
      oflatten rest = None ->
      oflatten (d :: rest) = None.
    Proof.
      intros.
      destruct d; try reflexivity.
      unfold oflatten in *; unfold lift_flat_map in *; simpl in *.
      rewrite H. reflexivity.
    Qed.

    Lemma oflatten_app_none1 l1 l2 :
      oflatten l1 = None ->
      oflatten (l1 ++ l2) = None.
    Proof.
      revert l2.
      induction l1; simpl.
      - inversion 1.
      - intros.
        destruct a; simpl; try reflexivity.
        unfold oflatten in *.
        simpl in *.
        apply none_lift in H.
        rewrite IHl1; eauto.
    Qed.

    Lemma oflatten_app_none2 l1 l2 :
      oflatten l2 = None ->
      oflatten (l1 ++ l2) = None.
    Proof.
      revert l2.
      induction l1; simpl.
      - trivial.
      - intros.
        destruct a; simpl; try reflexivity.
        unfold oflatten in *.
        simpl in *.
        apply lift_none.
        eauto.
    Qed.

    Lemma oflatten_lift_empty_dcoll l :
      olift oflatten (lift (fun t' : list data => dcoll nil :: t') l) = olift oflatten l.
    Proof.
      destruct l.
      simpl.
      unfold oflatten.
      simpl.
      apply lift_id.
      reflexivity.
    Qed.

    Lemma oflatten_lift_cons_dcoll a l:
      olift oflatten
            (lift (fun t' : list data => dcoll [a] :: t') l) =
      lift (fun t' => a::t') (olift oflatten l).
    Proof.
      destruct l; simpl; try reflexivity.
    Qed.

    Lemma oflatten_through_match l1 l2:
      olift oflatten
            match lift dcoll (Some l1) with
            | Some x' =>
              lift (fun t' : list data => x' :: t') l2
            | None => None
            end =
      lift (fun t' : list data => l1 ++ t')
           (olift oflatten l2).
    Proof.
      unfold olift, lift.
      induction l2; [unfold oflatten|idtac]; reflexivity.
    Qed.
    
  End FlattenUtils.

End Iterators.

Hint Rewrite @oflatten_map_dcoll_id : alg.

