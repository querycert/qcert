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
Require Import Compare_dec.
Require Import Program.
Require Import Eqdep_dec.
Require Import Bool.
Require Import EquivDec.
Require Import Utils.
Require Import Types.
Require Import ForeignData.
Require Import CommonData.
Require Import Operators.
Require Import TData.
Require Import ForeignDataTyping.

Section TUtil.
  (* Lemma/definitions over types involved in the inference *)
  
  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {m:brand_model}.

  (* Useful function *)

  Definition tdot {A} (l:list (string * A)) (a:string) : option A := edot l a.

  (* Type deconstructors *)
  
  Definition tuneither (τ:rtype) : option (rtype * rtype).
  Proof.
    destruct τ.
    destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - refine (Some ((exist _ x1 _),(exist _ x2 _))).
      + simpl in e; rewrite andb_true_iff in e; tauto.
      + simpl in e; rewrite andb_true_iff in e; tauto.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Definition tuncoll (τ:rtype) : option rtype.
  Proof.
    destruct τ.
    destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact (Some (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e)). 
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Lemma tuncoll_correct (τ τ':rtype) :
    tuncoll τ = Some τ' ->
    τ = Coll τ'.
  Proof.
    destruct τ using rtype_rect; try discriminate.
    inversion 1; subst.
    reflexivity.
  Qed.

  Definition tsingleton (τ:rtype) : option rtype.
  Proof.
    destruct τ.
    destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact (Some (Option (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e))). 
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Lemma tsingleton_correct (τ τ':rtype) :
    tsingleton τ = Some (Option τ') ->
    τ = Coll τ'.
  Proof.
    destruct τ using rtype_rect; try discriminate.
    inversion 1; subst.
    rtype_equalizer; subst.
    reflexivity.
  Qed.

  Definition tunrec (τ: rtype) : option (record_kind * (list (string * rtype))).
  Proof.
    destruct τ; destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - generalize (from_Rec₀ srl e); intros.
      destruct H.
      exact (Some (k,x)).
    - exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Lemma tunrec_correct k (τ:rtype) {l} :
    tunrec τ = Some (k,l) ->
    {pf | τ =  Rec k l pf}.
  Proof.
    destruct τ using rtype_rect; try discriminate.
    inversion 1; subst.
    match goal with
    | [H:context
           [match ?p with
            | _ => _
            end] |- _] => destruct p
    end.
    inversion H2; subst; clear H2.
    destruct e as [? [??]].
    rtype_equalizer; subst.
    eauto.
  Qed.

  Definition trecConcat (τ₁ τ₂: rtype) : option rtype.
  Proof.
    destruct τ₁; destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - destruct τ₂; destruct x.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + generalize (from_Rec₀ srl e); intros.
        generalize (from_Rec₀ srl0 e0); intros.
        destruct H; destruct H0.
        destruct k; destruct k0; simpl.
        * exact None. (* Open record *)
        * exact None. (* Open record *)
        * exact None. (* Open record *)
        * generalize (rec_concat_sort x x0); intros.
          exact (RecMaybe Closed H).
      + exact None.
      + exact None.
      + exact None.
      + exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Definition trecConcatRight (τ₁ τ₂: rtype) : option rtype.
  Proof.
    destruct τ₁; destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - destruct τ₂; destruct x.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + generalize (from_Rec₀ srl e); intros.
        generalize (from_Rec₀ srl0 e0); intros.
        destruct H; destruct H0.
        destruct k; destruct k0; simpl.
        * exact None. (* Both open record *)
        * generalize (rec_concat_sort x x0); intros. (* Left open record *)
          exact (RecMaybe Open H).
        * exact None. (* Right open record *)
        * generalize (rec_concat_sort x x0); intros.
          exact (RecMaybe Closed H).
      + exact None.
      + exact None.
      + exact None.
      + exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Definition tmergeConcat (τ₁ τ₂: rtype) : option rtype.
  Proof.
    destruct τ₁; destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - destruct τ₂; destruct x.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
      + generalize (from_Rec₀ srl e); intros.
        generalize (from_Rec₀ srl0 e0); intros.
        destruct H; destruct H0.
        generalize (merge_bindings x x0); intros.
        destruct H as [rSome|].
        destruct k; destruct k0; simpl in *.
        * exact (RecMaybe Open rSome).
        * exact None.
        * exact None.
        * exact (RecMaybe Closed rSome).
        * exact None.
      + exact None.
      + exact None.
      + exact None.
      + exact None.
    - exact None. 
    - exact None. 
    - exact None. 
    - exact None. 
  Defined.

  Definition tunrecdot (s:string) (τ:rtype) : option rtype.
  Proof.
    generalize (tunrec τ); intros.
    case_eq H; intros.
    - destruct p; simpl in *.
      exact (tdot l s).
    - exact None.
  Defined.

  Definition tunrecremove (s:string) (τ:rtype) : option rtype.
  Proof.
    generalize (tunrec τ); intros.
    case_eq H; intros.
    - destruct p; simpl in *.
      exact (RecMaybe r (rremove l s)).
    - exact None.
  Defined.

  Definition tunrecproject (sl:list string) (τ:rtype) : option rtype.
  Proof.
    generalize (tunrec τ); intros.
    case_eq H; intros.
    - destruct p; simpl in *.
      destruct (sublist_dec sl (domain l)).
      + exact (RecMaybe Closed (rproject l sl)). (* This is always a closed record *)
      + exact None. (* It is only well typed when sl is a sublist of domain l *)
    - exact None.
  Defined.

  (* Type inference for binary operators *)
  
  Definition recConcat (τ₁ τ₂: rtype) : option rtype.
  Proof.
    generalize (tunrec τ₁); intros.
    case_eq H; intros.
    - generalize (tunrec τ₂); intros.
      case_eq H1; intros.
      destruct p; destruct p0; simpl in *.
      + generalize (rec_concat_sort l l0); intros.
        destruct r; destruct r0; simpl in *.
        * exact None.
        * exact None.
        * exact None.
        * exact (RecMaybe Closed H3).
      + exact None.
    - exact None.
  Defined.
  
  Definition mergeConcat (τ₁ τ₂: rtype) : option rtype.
  Proof.
    generalize (tunrec τ₁); generalize (tunrec τ₂); intros.
    case_eq H; case_eq H0; intros.
    destruct p; destruct p0; simpl in *.
    generalize (merge_bindings l l0); intros.
    - destruct H3 as [rSome|].
      destruct r; destruct r0; simpl in *.
      * exact (RecMaybe Open rSome).
      * exact None.
      * exact None.
      * exact (RecMaybe Closed rSome).
      * exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

  Lemma RecMaybe_rec_concat_sort k l1 l2 :
    RecMaybe k (rec_concat_sort l1 l2) = Some (Rec k (rec_concat_sort l1 l2) (drec_concat_sort_sorted l1 l2)).
  Proof.
    apply (RecMaybe_pf_some _).
  Qed.

  Lemma Bottom_proj : Bottom₀ = ` Bottom.
  Proof.
    reflexivity.
  Qed.

  Lemma Top_proj : Top₀ = ` Top.
  Proof.
    reflexivity.
  Qed.

  Lemma Unit_proj : Unit₀ = ` Unit.
  Proof.
    reflexivity.
  Qed.

  Lemma Nat_proj : Nat₀ = ` Nat.
  Proof.
    reflexivity.
  Qed.

  Lemma Float_proj : Float₀ = ` Float.
  Proof.
    reflexivity.
  Qed.

  Lemma Bool_proj : Bool₀ = ` Bool.
  Proof.
    reflexivity.
  Qed.

  Lemma String_proj : String₀ = ` String.
  Proof.
    reflexivity.
  Qed.

  Lemma Brand_canon {b} {τ₁:rtype} :` τ₁ = Brand₀ b -> τ₁ = Brand b.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply brand_ext.
  Qed.

  Lemma Bottom_canon {τ₁:rtype} :` τ₁ = Bottom₀ -> τ₁ = Bottom.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma Top_canon {τ₁:rtype} :` τ₁ = Top₀ -> τ₁ = Top.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma Unit_canon {τ₁:rtype} :` τ₁ = Unit₀ -> τ₁ = Unit.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma Nat_canon {τ₁:rtype} :` τ₁ = Nat₀ -> τ₁ = Nat.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma Float_canon {τ₁:rtype} :` τ₁ = Float₀ -> τ₁ = Float.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma Bool_canon {τ₁:rtype} :` τ₁ = Bool₀ -> τ₁ = Bool.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma String_canon {τ₁:rtype} :` τ₁ = String₀ -> τ₁ = String.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Lemma Coll_canon {τ₁ τ₀:rtype} :` τ₁ = Coll₀ (` τ₀) -> τ₁ = Coll τ₀.
  Proof.
    destruct τ₁; simpl; intros; subst.
    apply rtype_ext.
  Qed.

  Section lift_map.
    Context {fdtyping:foreign_data_typing}.

    Lemma omap_product_empty_right τ pf l:
      Forall (fun d : data => d ▹ Rec Closed τ pf) l ->
      (omap_product (fun _ : data => Some (dcoll (drec nil :: nil))) l) = Some l.
    Proof.
      intros.
      induction l; simpl; unfold omap_product in *; simpl.
      - reflexivity.
      - inversion H; clear H; subst.
        specialize (IHl H3); clear H3.
        rewrite IHl.
        inversion H2.
        dtype_inverter. subst.
        unfold rec_concat_sort.
        rewrite app_nil_r.
        assert (rec_sort dl = dl).
        + clear a e.
          rewrite sort_sorted_is_id.
          reflexivity.
          rewrite (same_domain_same_sorted rl dl).
          reflexivity.
          clear pf' H0 H2 H4 H1 rl_sub IHl pf.
          assert (domain dl = domain rl).
          apply (sorted_forall_same_domain); assumption.
          auto.
          assumption.
        + rewrite H.
          reflexivity.
    Qed.
    
    Lemma oproduct_empty_right τ pf l:
      Forall (fun d : data => d ▹ Rec Closed τ pf) l ->
      (oproduct l (drec nil :: nil)) = Some l.
    Proof.
      intros.
      induction l; simpl; unfold omap_product in *; simpl.
      - reflexivity.
      - inversion H; clear H; subst.
        specialize (IHl H3); clear H3.
        unfold oproduct in *; simpl in *; rewrite IHl.
        inversion H2.
        dtype_inverter. subst.
        unfold rec_concat_sort.
        rewrite app_nil_r.
        assert (rec_sort dl = dl).
        + clear a e.
          rewrite sort_sorted_is_id.
          reflexivity.
          rewrite (same_domain_same_sorted rl dl).
          reflexivity.
          clear pf' H0 H2 H4 H1 rl_sub IHl pf.
          assert (domain dl = domain rl).
          apply (sorted_forall_same_domain); assumption.
          auto.
          assumption.
        + rewrite H.
          reflexivity.
    Qed.
    
    Lemma omap_product_empty_left τ pf l:
      Forall (fun d : data => d ▹ Rec Closed τ pf) l ->
      (omap_product (fun _ : data => Some (dcoll l)) (drec nil::nil)) = Some l.
    Proof.
      intros.
      induction l; simpl; unfold omap_product in *; simpl.
      - reflexivity.
      - inversion H; clear H; subst.
        specialize (IHl H3); clear H3.
        unfold lift_flat_map in IHl.
        unfold oncoll_map_concat in *.
        unfold omap_concat in *.
        simpl in *.
        inversion H2.
        dtype_inverter. subst.
        unfold rec_concat_sort in *.
        rewrite app_nil_l in *.
        assert (rec_sort dl = dl).
        + clear a e.
          rewrite sort_sorted_is_id.
          reflexivity.
          rewrite (same_domain_same_sorted rl dl).
          reflexivity.
          clear pf' H0 H2 H4 H1 rl_sub IHl pf.
          assert (domain dl = domain rl).
          apply (sorted_forall_same_domain); assumption.
          auto.
          assumption.
        + destruct (lift_map
                      (fun x : data =>
                         match x with
                         | dunit => None
                         | dnat _ => None
                         | dfloat _ => None
                         | dbool _ => None
                         | dstring _ => None
                         | dcoll _ => None
                         | drec r1 => Some (drec (rec_sort (nil ++ r1)))
                         | dleft _ => None
                         | dright _ => None
                         | dbrand _ _ => None
                         | dforeign _ => None
                         end) l); simpl in *; congruence.
    Qed.
    
    Lemma oproduct_empty_left τ pf l:
      Forall (fun d : data => d ▹ Rec Closed τ pf) l ->
      (oproduct (drec nil::nil) l) = Some l.
    Proof.
      intros.
      induction l; simpl; unfold omap_product in *; simpl.
      - reflexivity.
      - inversion H; clear H; subst.
        specialize (IHl H3); clear H3.
        simpl in *.
        unfold oproduct in *; simpl in *.
        unfold omap_concat in *.
        simpl in *.
        inversion H2.
        dtype_inverter. subst.
        unfold rec_concat_sort in *.
        rewrite app_nil_l in *.
        assert (rec_sort dl = dl).
        + clear a e.
          rewrite sort_sorted_is_id.
          reflexivity.
          rewrite (same_domain_same_sorted rl dl).
          reflexivity.
          clear pf' H0 H2 H4 H1 rl_sub IHl pf.
          assert (domain dl = domain rl).
          apply (sorted_forall_same_domain); assumption.
          auto.
          assumption.
        + destruct (lift_map
                      (fun x : data =>
                         match x with
                         | dunit => None
                         | dnat _ => None
                         | dfloat _ => None
                         | dbool _ => None
                         | dstring _ => None
                         | dcoll _ => None
                         | drec r1 => Some (drec (rec_sort (nil ++ r1)))
                         | dleft _ => None
                         | dright _ => None
                         | dbrand _ _ => None
                         | dforeign _ => None
                         end) l); simpl in *; congruence.
    Qed.
    
  End lift_map.

  Section bagops.
    Context {fdtyping:foreign_data_typing}.

    Lemma forall_typed_bunion {τ} d1 d2:
      Forall (fun d : data => data_type d τ) d1 ->
      Forall (fun d : data => data_type d τ) d2 ->
      Forall (fun d : data => data_type d τ) (bunion d1 d2).
    Proof.
      intros; rewrite Forall_forall in *.
      induction d1.
      simpl in *; intros.
      apply H0; assumption.
      simpl in *; intros.
      elim H1; intros; clear H1.
      apply (H x).
      left; assumption.
      assert (forall x : data, In x d1 -> data_type x τ).
      intros.
      apply (H x0).
      right; assumption.
      apply IHd1; assumption.
    Qed.

    Lemma bminus_in_remove (x a:data) (d1 d2:list data) :
      In x (bminus d1 (remove_one a d2)) -> In x (bminus d1 d2).
    Proof.
      revert d2.
      induction d1; simpl; intros.
      - induction d2; simpl in *.
        assumption.
        revert H.
        elim (EquivDec.equiv_dec a a0); unfold EquivDec.equiv_dec; intros.
        rewrite <- a1.
        right; assumption.
        simpl in H.
        elim H; intros; clear H.
        left; assumption.
        right; apply (IHd2 H0).
      - specialize (IHd1 (remove_one a0 d2)).
        apply IHd1.
        rewrite remove_one_comm; assumption.
    Qed.      
    
    Lemma forall_typed_bminus {τ} d1 d2:
      Forall (fun d : data => data_type d τ) d1 ->
      Forall (fun d : data => data_type d τ) d2 ->
      Forall (fun d : data => data_type d τ) (bminus d1 d2).
    Proof.
      intros; rewrite Forall_forall in *.
      induction d1.
      simpl in *; intros.
      apply H0; assumption.
      simpl in *; intros.
      assert (forall x : data, In x d1 -> data_type x τ).
      intros.
      apply (H x0).
      right; assumption.
      assert (In x (bminus d1 d2))
        by (apply bminus_in_remove with (a:=a); assumption).
      apply IHd1; assumption.
    Qed.

    Lemma forall_typed_bmin {τ} d1 d2:
      Forall (fun d : data => data_type d τ) d1 ->
      Forall (fun d : data => data_type d τ) d2 ->
      Forall (fun d : data => data_type d τ) (bmin d1 d2).
    Proof.
      intros.
      unfold bmin.
      assert (Forall (fun d : data => data_type d τ) (bminus d2 d1)).
      apply forall_typed_bminus; assumption.
      apply forall_typed_bminus; assumption.
    Qed.

    Lemma forall_typed_bmax {τ} d1 d2:
      Forall (fun d : data => data_type d τ) d1 ->
      Forall (fun d : data => data_type d τ) d2 ->
      Forall (fun d : data => data_type d τ) (bmax d1 d2).
    Proof.
      intros.
      unfold bmax.
      assert (Forall (fun d : data => data_type d τ) (bminus d1 d2)).
      apply forall_typed_bminus; assumption.
      apply forall_typed_bunion; assumption.
    Qed.

    Lemma rec_concat_with_drec_concat_well_typed  dl dl0 τ₁ τ₂:
      is_list_sorted ODT_lt_dec (domain τ₁) = true ->
      is_list_sorted ODT_lt_dec (domain τ₂) = true ->
      is_list_sorted ODT_lt_dec (domain (rec_concat_sort τ₁ τ₂)) = true ->
      Forall2
        (fun (d : string * data) (r : string * rtype) =>
           fst d = fst r /\ data_type (snd d) (snd r)) dl τ₁ ->
      Forall2
        (fun (d : string * data) (r : string * rtype) =>
           fst d = fst r /\ data_type (snd d) (snd r)) dl0 τ₂ ->
      Forall2
        (fun (d : string * data) (r : string * rtype) =>
           fst d = fst r /\ data_type (snd d) (snd r)) (rec_sort (dl ++ dl0))
        (rec_concat_sort τ₁ τ₂).
    Proof.
      intros pf1 pf2 pf3 H H0.
      assert (domain dl = domain τ₁)
        by (apply (sorted_forall_same_domain); assumption).
      assert (domain dl0 = domain τ₂)
        by (apply (sorted_forall_same_domain); assumption).
      assert (rec_sort dl = dl)
        by (apply sort_sorted_is_id; rewrite H1; assumption).
      assert (rec_sort dl0 = dl0)
        by (apply sort_sorted_is_id; rewrite H2; assumption).
      assert (rec_sort τ₂ = τ₂)
        by (apply sort_sorted_is_id; assumption).
      assert (rec_sort τ₁ = τ₁)
        by (apply sort_sorted_is_id; assumption).
      unfold rec_concat_sort.
      induction H; simpl in *.
      rewrite H4; rewrite H5.
      assumption.
      assert (is_list_sorted ODT_lt_dec (domain l') = true).
      revert pf1.
      destruct l'.
      reflexivity.
      simpl.
      destruct (StringOrder.lt_dec (fst y) (fst p)); congruence.
      assert (is_list_sorted ODT_lt_dec
                             (domain (rec_sort (l' ++ τ₂))) = true)
        by (apply (@rec_sort_sorted string ODT_string) with (l1 := l' ++ τ₂); reflexivity).
      specialize (IHForall2 H8 H9).
      inversion H1.
      specialize (IHForall2 H12).
      assert (is_list_sorted ODT_lt_dec (domain l') = true).
      revert pf1.
      destruct l'; try reflexivity; simpl.
      destruct (StringOrder.lt_dec (fst y) (fst p)); congruence.
      assert (is_list_sorted ODT_lt_dec (domain l') = true)
        by (apply (@rec_sorted_skip_first string ODT_string _ l' y); assumption).
      assert (rec_sort l' = l')
        by (apply rec_sorted_id; assumption).
      assert (is_list_sorted ODT_lt_dec (domain l) = true)
        by (apply (sorted_forall_sorted l l'); assumption).
      assert (rec_sort l = l)
        by (apply rec_sorted_id; assumption).
      specialize (IHForall2 H16 H14).
      clear H4 H5 H12 H10 H13 H14 H15 H16.
      elim H; intros; clear H H4.
      clear pf1 pf2.
      assert (is_list_sorted
                ODT_lt_dec
                (domain
                   (insertion_sort_insert rec_field_lt_dec x (rec_sort (l ++ dl0)))) =
              true).
      apply (insert_and_foralls_mean_same_sort l dl0 l' τ₂ x y); assumption.
      apply Forall2_cons_sorted; assumption.
    Qed.

    Lemma concat_well_typed {τ₁ τ₂ τ₃} d1 d2 pf1 pf2 pf3:
      rec_concat_sort τ₁ τ₂ = τ₃ ->
      data_type d1 (Rec Closed τ₁ pf1) ->
      data_type d2 (Rec Closed τ₂ pf2) ->
      exists dl dl0 d3,
        d1 = drec dl /\
        d2 = drec dl0 /\
        ((rec_sort (dl ++ dl0)) = d3) /\
        data_type (drec d3) (Rec Closed τ₃ pf3).
    Proof.
      intros.
      destruct (data_type_Rec_inv H0); subst.
      destruct (data_type_Rec_inv H1); subst.
      apply dtrec_closed_inv in H0.
      apply dtrec_closed_inv in H1.
      do 3 eexists; do 3 (split; try reflexivity).
      apply dtrec_full.
      apply rec_concat_with_drec_concat_well_typed; assumption.
    Qed. 

    Lemma forall_typed_bdistinct {τ} d1:
      Forall (fun d : data => data_type d τ) d1 ->
      Forall (fun d : data => data_type d τ) (bdistinct d1).
    Proof.
      intros; rewrite Forall_forall in *.
      intros.
      induction d1.
      simpl in *.
      contradiction.
      simpl in *.
      assert (forall x : data, In x d1 -> data_type x τ)
        by (apply (forall_in_weaken (fun x => a = x)); assumption).
      destruct (mult (bdistinct d1) a).
      elim H0; intros; clear H0.
      rewrite <- H2 in *.
      apply (H a).
      left; reflexivity.
      specialize (IHd1 H1 H2); assumption.
      specialize (IHd1 H1 H0); assumption.
    Qed.


    Lemma rremove_well_typed τ s dl:
      Forall2
        (fun (d : string * data) (r : string * rtype) =>
           fst d = fst r /\ data_type (snd d) (snd r)) dl τ ->
      Forall2
        (fun (d : string * data) (r : string * rtype) =>
           fst d = fst r /\ data_type (snd d) (snd r)) (rremove dl s)
        (rremove τ s).
    Proof.
      intros F2.
      induction F2; simpl; trivial.
      destruct H; simpl in *.
      rewrite H.
      match_destr.
      auto.
    Qed.

    Lemma rproject_well_typed τ rl s dl:
      Forall2
        (fun (d : string * data) (r : string * rtype) =>
           fst d = fst r /\ data_type (snd d) (snd r)) dl rl ->
      sublist s (domain τ) ->
      sublist τ rl ->
      is_list_sorted ODT_lt_dec (domain τ) = true ->
      is_list_sorted ODT_lt_dec (domain rl) = true ->
      Forall2
        (fun (d : string * data) (r : string * rtype) =>
           fst d = fst r /\ data_type (snd d) (snd r)) (rproject dl s)
        (rproject τ s).
    Proof.
      intros.
      assert (sublist s (domain rl)) by
          (apply (sublist_trans s (domain τ) (domain rl)); try assumption;
           apply sublist_domain; assumption).
      assert (NoDup (domain rl))
        by (apply is_list_sorted_NoDup_strlt; assumption).
      rewrite (rproject_sublist τ rl s H2 H3); try assumption.
      clear H0 H1 H4 H2.
      induction H.
      - apply Forall2_nil.
      - inversion H5; subst.
        assert (is_list_sorted ODT_lt_dec (domain l') = true)
          by (apply (@rec_sorted_skip_first string ODT_string _ l' y); assumption).
        specialize (IHForall2 H1 H6).
        elim H; intros.
        simpl; rewrite H2.
        destruct (in_dec string_dec (fst y) s).
        apply Forall2_cons; try assumption; split; assumption.
        assumption.
    Qed.
    
  End bagops.
End TUtil.

