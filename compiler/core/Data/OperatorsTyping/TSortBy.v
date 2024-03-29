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

Require Import String.
Require Import List.
Require Import ZArith.
Require Import Compare_dec.
Require Import Utils.
Require Import Types.
Require Import DataModel.
Require Import ForeignData.
Require Import ForeignOperators.
Require Import ForeignDataTyping.
Require Import Operators.
Require Import TData.
Require Import Program.

Section TSortBy.
  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Definition sortable_type (τ : rtype) : Prop :=
    τ = Nat \/ τ = String.

  Definition order_by_has_sortable_type
             (τr:list (string*rtype))
             (satts: list string) : Prop :=
    Forall (fun s =>
              forall τout, edot τr s = Some τout -> sortable_type τout)
           satts.

  Lemma sortable_type_dec (τ : rtype) : {sortable_type τ} + {~ sortable_type τ}.
  Proof.
    unfold sortable_type.
    destruct τ; destruct x; simpl; try solve [right; intuition discriminate].
    - left. left.
      apply Nat_canon.
    - left. right.
      apply String_canon.
  Defined.
  
  Definition order_by_has_sortable_type_dec
             (τr:list (string*rtype))
             (satts: list string) : {order_by_has_sortable_type τr satts} + {~order_by_has_sortable_type τr satts}.
  Proof.
    unfold order_by_has_sortable_type.
    apply Forall_dec_defined.
    intros.
    case_eq (edot τr x); intros.
    - destruct (sortable_type_dec r).
      + left; congruence.
      + right; auto.
    -  left; congruence.
  Defined.

  Lemma order_by_has_sortable_type_sdd {τ sl a k pf1} :
    sublist (map fst sl) (domain τ) ->
    order_by_has_sortable_type τ (map fst sl) ->
    (drec a) ▹ Rec k τ pf1 ->
    {x | fsortable_data_of_data a (map get_criteria sl) = Some x /\  (drec (snd x)) ▹ Rec k τ pf1}.
  Proof.
    unfold fsortable_data_of_data, order_by_has_sortable_type, fget_criterias.
    induction sl; simpl; intros sub sts dt.
    - eexists; split; try reflexivity; simpl; trivial.
    - cut_to IHsl; trivial.
      + destruct IHsl as [? [eqx dtx]].
        repeat (
            apply some_lift in eqx
            ; destruct eqx as [? eqx ?]; subst).
        rewrite eqx.
        destruct a0.
        simpl in *.
        assert (ins: In s (domain τ))
          by (apply (sublist_In sub); simpl; auto).
        unfold edot.
        destruct (in_dom_lookupr_strong a s  (@ODT_eqdec string ODT_string) ) as [x xl].
        { apply data_type_Rec_domain in dtx.
          apply (sublist_In dtx); simpl; auto.
        }
        unfold Equivalence.equiv.
        unfold RelationClasses.complement.
        unfold not in xl.
        simpl in *.
        rewrite xl.
        rewrite Forall_forall in sts.
        specialize (sts s).
        cut_to sts; simpl; [|tauto].
        destruct (in_dom_lookupr_strong τ s  (@ODT_eqdec string ODT_string) ) as [y yl]; trivial.
        specialize (sts _ yl).
        assert (dtxy: x ▹ y) by (eapply dtrec_edot_parts; eauto).
        unfold sortable_type in *.
        destruct x; simpl
        ; try solve [cut False; [tauto|]; invcs dtxy; simpl in sts
                     ; intuition discriminate | eauto 3].
      + eapply sublist_skip_l; eauto.
      + invcs sts; trivial.
  Qed.

  Lemma in_sort_sortable_snd
        (l0:list sortable_data) (l1:list sdata) (l2:list (string * data))
        (x0:list (list (string * data))) :
    map snd (sort_sortable_coll l0) = x0 ->
    In (l1, l2) l0 ->
    In l2 x0.
  Proof.
    intros.
    rewrite <- (@in_sort_sortable _ (l1, l2) l0) in H0.
    revert H H0.
    generalize (sort_sortable_coll l0); intros.
    rewrite <- H.
    assert (l2 = snd (l1, l2)) by reflexivity.
    rewrite H1.
    apply in_map.
    apply H0.
  Qed.
    
  Lemma order_by_well_typed
        (d1:data) (sl:list (string * SortDesc))
        {k τ} {pf1 pf2} :
    d1 ▹ Coll (Rec k τ pf1) ->
    sublist (map fst sl) (domain τ) ->
    order_by_has_sortable_type τ (map fst sl) ->
    exists x, data_sort (map get_criteria sl) d1 = Some x /\ x ▹ Coll (Rec k τ pf2).
  Proof.
    intros dt.
    dtype_inverter.
    apply Col_inv in dt.
    (*    revert τ pf1 pf2 dt. *)
    revert dt.
    induction d1; simpl
    ; intros dt sub ob. (* τ pf1 pf2 dt sub ob. *)
    - eexists; split; try reflexivity.
      repeat constructor.
    - invcs dt.
      dtype_inverter.
      specialize (IHd1 H2 sub ob).
      destruct IHd1 as [x [eqx dtx]].
      repeat (
          apply some_lift in eqx
          ; destruct eqx as [? eqx ?]; subst).
      unfold fsortable_coll_of_coll in *.
      simpl.
      destruct (order_by_has_sortable_type_sdd sub ob H1)
        as [sd [sdeq sdt]].
      unfold data_sort.
      unfold lift, olift in *.
      unfold lift in *.
      simpl in *.
      case_eq (lift_map (fun d : data => match d with
                                        | drec r => Some r
                                        | _ => None
                                         end) d1); intros;
      rewrite H in *; simpl in *; try congruence; clear H.
      unfold table_sort in *.
      unfold fsortable_coll_of_coll in *.
      simpl.
      rewrite sdeq.
      case_eq (lift_map
                 (fun d : list (string * data) => fsortable_data_of_data d (map get_criteria sl)) l); intros; rewrite H in eqx; simpl in *; try congruence; clear H; simpl.
      inversion eqx.
      eexists; split; try reflexivity.
      apply Col_inv in dtx.
      constructor.
      unfold coll_of_sortable_coll in *.
      rewrite Forall_map in dtx |- *.
      rewrite Forall_forall in dtx.
      rewrite Forall_map.
      assert (@insertion_sort_insert (prod (list sdata) (list (prod string (@data fdata))))
       (@dict_field_le (list (prod string (@data fdata))))
       (@dict_field_le_dec (list (prod string (@data fdata)))) sd
       (@sort_sortable_coll (list (prod string (@data fdata))) l0) = insertion_sort dict_field_le_dec (sd::l0)) by reflexivity.
      rewrite H.
      apply Forall_insertion_sort.
      constructor.
      + revert sdt.
        clear.
        destruct (is_list_sorted_ext StringOrder.lt_dec _ pf1 pf2); trivial.
      + rewrite Forall_forall; intros x inx.
        apply dtx.
        destruct x; simpl in*.
        apply (in_sort_sortable_snd l0 l1 l2); assumption.
  Qed.

End TSortBy.
