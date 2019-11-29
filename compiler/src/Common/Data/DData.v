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
Require Import ZArith.
Require Import Bool.
Require Import EquivDec.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignData.
Require Import Data.

Section DData.
  (** Localized Data is:
     - Dlocal - single, non-distributed value
     - Ddistr - distributed collection of values
   *)

  Unset Elimination Schemes.

  Context {fdata:foreign_data}.

  Inductive ddata :=
  | Dlocal : data -> ddata
  | Ddistr : list data -> ddata.

  Lemma ddata_eq_dec : EqDec ddata eq.
  Proof.
    repeat red.
    intros. destruct x; destruct y.
    - destruct (data_eq_dec d d0).
      + left; rewrite e; reflexivity.
      + right; congruence.
    - right; congruence.
    - right; congruence.
    - revert l0; induction l; destruct l0.
      + left; reflexivity.
      + right; congruence.
      + right; congruence.
      + destruct (data_eq_dec a d).
        rewrite e.
        destruct (IHl l0).
        inversion e0.
        left; reflexivity.
        right; congruence.
        right; congruence.
  Defined.
    
  Definition checkLocal (ld:ddata) : option data :=
    match ld with
    | Dlocal d => Some d
    | Ddistr _ => None
    end.

  Definition checkDistrAndCollect (ld:ddata) : option data :=
    match ld with
    | Dlocal _ => None
    | Ddistr coll => Some (dcoll coll)
    end.
  
  Definition unlocalize_data (dd:ddata) :=
    match dd with
    | Ddistr coll => dcoll coll
    | Dlocal d => d
    end.

  Lemma unlocalize_distributed_id (l:list data) :
    unlocalize_data (Ddistr l) = dcoll l.
  Proof.
    reflexivity.
  Qed.

  Definition dbindings := list (string*ddata).

  (* Localized variable annotations *)
  
  (* Java equivalent: NnrcToNrcmr.localization (an enum) *)
  Inductive dlocalization :=
  | Vlocal : dlocalization
  | Vdistr : dlocalization.

  Definition vdbindings := list (string*dlocalization).

  Lemma dlocalization_eq_dec : EqDec dlocalization eq.
  Proof.
    repeat red.
    intros. destruct x; destruct y.
    - left; reflexivity.
    - right; congruence.
    - right; congruence.
    - left; reflexivity.
  Defined.
  
End DData.

