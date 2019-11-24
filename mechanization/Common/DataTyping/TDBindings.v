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
Require Import Sumbool.
Require Import Arith.
Require Import Bool.
Require Import Morphisms.
Require Import Basics.
Require Import BrandRelation.
Require Import Utils.
Require Import Types.
Require Import ForeignData.
Require Import CommonData.
Require Import ForeignDataTyping.
Require Import TDData.
Require Import TBindings.
Require Import EquivDec.

Section TDBindings.
  Context {fdata:foreign_data}.
  Context {ftype:foreign_type}.
  Context {fdtyping:foreign_data_typing}.
  Context {m:brand_model}.

  Definition tdbindings := list (string*drtype).

  Definition dbindings_type (b:list (string*ddata)) (t:tdbindings)
    := Forall2 (fun xy1 xy2 =>
                      (fst xy1) = (fst xy2)
                  /\ ddata_type (snd xy1) (snd xy2)) b t.

  Hint Resolve ddata_dtype_normalized.
  Lemma dbindings_type_Forall_normalized c τc :
    dbindings_type c τc ->
    Forall
      (fun d : string * ddata => ddata_normalized brand_relation_brands (snd d))
      c.
  Proof.
    induction 1; trivial.
    intuition.
    constructor.
    - destruct x; destruct y; simpl in *; subst.
      apply (ddata_dtype_normalized _ _ H2).
    - auto.
  Qed.

  Definition tdbindings_sub : tdbindings -> tdbindings -> Prop
      := Forall2
         (fun (xy1 : string * drtype) (xy2 : string * drtype) =>
            fst xy1 = fst xy2 /\ drtype_sub (snd xy1) (snd xy2)).

  Global Instance eq_and_drtype_pre : PreOrder 
                                        (fun xy1 xy2 : string * drtype => fst xy1 = fst xy2 /\ drtype_sub (snd xy1) (snd xy2)).
  Proof.
    constructor; red.
    - intuition; reflexivity.
    - intuition; etransitivity; eauto.
  Qed.
    
  Global Instance tdbindings_sub_pre : PreOrder tdbindings_sub.
  Proof.
    unfold tdbindings_sub.
    apply Forall2_pre.
    apply eq_and_drtype_pre.
  Qed.

  Global Instance tdbindings_sub_part : PartialOrder eq tdbindings_sub.
  Proof.
    unfold tdbindings_sub.
    eapply Forall2_part_eq.
    intros sdτ₁ sdτ₂.
    unfold flip.
    split; intros H.
    - repeat red; simpl; subst; intuition.
    - repeat red in H; intuition.
      destruct sdτ₁; destruct sdτ₂
      ; simpl in * .
      f_equal; trivial.
      apply antisymmetry; auto.
  Qed.

  Global Instance tdbindings_type_sub :
    Proper (eq ==> tdbindings_sub ==> impl) dbindings_type.
  Proof.
    unfold Proper, respectful, impl
    ; intros d d' ? dτ₁ dτ₂ sub typ
    ; subst d'.
    unfold tdbindings_sub, dbindings_type in *.
    eapply Forall2_trans_relations_weak; eauto.
    simpl.
    destruct a; destruct b; destruct c; simpl; intuition; subst; trivial.
    rewrite H3 in H2.
    trivial.
  Qed.

  Section unlocalize.
    Definition unlocalize_tdbindings (binds:tdbindings) : tbindings :=
      map (fun xy => ((fst xy), unlocalize_drtype (snd xy))) binds.
  End unlocalize.
  
  Section vdbindings.
    Definition dt_to_v (bind:string * drtype) : string * dlocalization :=
      match snd bind with
      | Tlocal _ => (fst bind, Vlocal)
      | Tdistr _ => (fst bind, Vdistr)
      end.

    Definition vdbindings_of_tdbindings (binds:tdbindings) : vdbindings :=
      map dt_to_v binds.

    Definition v_and_t_to_dt (v:dlocalization) (t:rtype) : drtype :=
      match v with
      | Vlocal => Tlocal t
      | Vdistr => Tdistr t
      end.

  End vdbindings.

End TDBindings.

Hint Resolve dbindings_type_Forall_normalized.

