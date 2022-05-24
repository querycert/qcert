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
Require Import Compare_dec.
Require Import Lia.
Require Import String.
Require Import List.
Require Import ZArith.
Require Import Utils.
Require Import ForeignData.
Require Import Data.
Require Import DataNorm.

(* For data *)
Section SortBy.
  Context {fdata:foreign_data}.

  Definition sdata_of_data (d:data) : option sdata :=
    match d with
    | dnat n => Some (sdnat n)
    | dstring s => Some (sdstring s)
    | _ => None
    end.
  
  Definition get_criteria (sc:SortCriteria) (r:list (string * data)) : option sdata :=
    let (att,sk) := sc in (* XXX IGNORES sort kind (asc|desc) XXX *)
    match edot r att with
    | Some d => sdata_of_data d
    | None => None
    end.

  Definition table_of_data (d:data) : option (list (list (string * data))):=
    match d with
    | dcoll coll =>
      lift_map (fun d =>
                  match d with
                  | drec r => Some r
                  | _ => None
                  end) coll
    | _ => None
    end.

  Definition data_of_table (t: list (list (string * data))) : data :=
    dcoll (map drec t).
  
  Definition data_sort
             (scl:list (list (string * data) -> option sdata))
             (d:data) : option data :=
    lift data_of_table (olift (table_sort scl) (table_of_data d)).

End SortBy.

Section SortByProps.
  Context {fdata:foreign_data}.

  Lemma sortable_data_normalized h a sc sd :
    data_normalized h a ->
    fsortable_data_of_data a sc = Some sd ->
    data_normalized h (snd sd).
  Proof.
    unfold fsortable_data_of_data; intros dn eqs.
    apply some_lift in eqs.
    destruct eqs as [? eqs ?]; subst.
    simpl; trivial.
  Qed.

  Lemma fsortable_data_of_data_snd_inv {A:Set} (l0: list (string * A))
        (s:list (list (string * A) -> option sdata)) (s0:sortable_data) :
    fsortable_data_of_data l0 s = Some s0 ->
    l0 = snd s0.
  Proof.
    intros.
    destruct s0; simpl in *.
    unfold fsortable_data_of_data in H.
    unfold lift in H.
    destruct (fget_criterias l0 s); try discriminate.
    inversion H.
    reflexivity.
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
    simpl in eqs.
    unfold table_sort in eqs.
    revert x eqs H0.
    induction l; simpl; intros x eqs dn d ind.
    - invcs eqs.
      simpl in *; tauto.
    - destruct a; simpl in *; try discriminate.
      case_eq (lift_map (fun d : data => match d with
                                        | drec r => Some r
                                        | _ => None
                                        end) l);
        [intros ? eqq1 | intros eqq1]; rewrite eqq1 in eqs
        ; rewrite eqq1 in IHl
        ; try discriminate; simpl in *.
      unfold fsortable_coll_of_coll in *; simpl in eqs.
      unfold lift in eqs.
      case_eq (fsortable_data_of_data l0 s)
      ; [intros ? eqq2 | intros eqq2]; rewrite eqq2 in eqs
      ; try discriminate.
      case_eq (lift_map (fun d : list (string * data) => fsortable_data_of_data d s) l1)
      ; [intros ? eqq3 | intros eqq3]; rewrite eqq3 in eqs
      ; rewrite eqq3 in IHl
      ; try discriminate.
      assert (x = coll_of_sortable_coll (sort_sortable_coll (s0 :: l2)))
        by (inversion eqs; reflexivity).
      rewrite H in *; clear H.
      unfold coll_of_sortable_coll in ind.
      rewrite map_map in ind.
      rewrite in_map_iff in ind.
      elim ind; intros; clear ind.
      elim H; intros; clear H.
      rewrite <- H0 in *; clear H0.
      unfold sort_sortable_coll, dict_sort in H1.
      inversion eqs; clear eqs.
      assert (In x0 (s0 :: l2)) by apply (in_insertion_sort _ H1); clear H1;
        simpl in H.
      elim H; intros; simpl in *; clear H.
      + subst.
        apply dn.
        left.
        unfold fsortable_data_of_data in eqq2.
        unfold fget_criterias in eqq2.
        unfold lift in eqq2.
        case_eq (lift_map (fun f : list (string * data) -> option sdata => f l0) s);
          intros; rewrite H in *; simpl; try congruence.
        inversion eqq2; reflexivity.
      + eapply IHl.
        reflexivity.
        * intros.
          apply (dn x1).
          right; assumption.
        * rewrite in_map_iff.
          exists (snd x0).
          split; [reflexivity|].
          rewrite in_csc_ssc.
          unfold coll_of_sortable_coll.
          rewrite in_map_iff.
          exists x0.
          split; [reflexivity|assumption].
  Qed.

End SortByProps.
