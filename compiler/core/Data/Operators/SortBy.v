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

Section SortBy.
  Context {fdata:foreign_data}.
  
  (* Eval vm_compute in (sort_sortable_coll scoll1). *)
  
  Definition get_criteria (d:data) (sc:SortCriteria) : option sdata :=
    let (att,sk) := sc in (* XXX IGNORES sort kind (asc|desc) XXX *)
    match d with
    | drec r =>
      match edot r att with
      | Some (dnat n) => Some (sdnat n)
      | Some (dstring s) => Some (sdstring s)
      | Some _ => None
      | None => None
      end
    | _ => None
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
      (("John",23,1008,"ACME")
         :: ("Jane",24,1009,"AIGO")
         :: ("Jill",25,1010,"ACME")
         :: ("Jack",27,1010,"CMUD")
         :: nil)%string.

  (*
  Eval vm_compute in persons.
  Eval vm_compute in (data_sort (("name"%string,Ascending)::nil) persons).
  Eval vm_compute in (data_sort (("zip"%string,Ascending)::("name"%string,Ascending)::nil) persons).
  *)

End SortBy.

Section SortByProps.
  Context {fdata:foreign_data}.

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

End SortByProps.

