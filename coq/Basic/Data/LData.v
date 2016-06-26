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

Section LData.
  Require Import String.
  Require Import List.
  Require Import Sumbool.
  Require Import ZArith.
  Require Import Bool.

  Require Import Utils.
  Require Import BrandRelation.
  Require Import ForeignData.
  Require Import RData.

  (** Localized Data is:
     - Dscalar - single, non-distributed value
     - Ddistributed - distributed collection of values
   *)

  Unset Elimination Schemes.

  Context {fdata:foreign_data}.

  (* Java equivalent: NnrcToNrcmr.localization (an enum) *)
  Inductive localization :=
  | Vscalar : localization
  | Vdistributed : localization.

  Require Import EquivDec.
  Lemma localization_eq_dec : EqDec localization eq.
  Proof.
    repeat red.
    intros. destruct x; destruct y.
    - left; reflexivity.
    - right; congruence.
    - right; congruence.
    - left; reflexivity.
  Defined.
  
  Inductive localized_data :=
  | Dscalar : data -> localized_data
  | Ddistributed : list data -> localized_data.

  Lemma localized_data_eq_dec : EqDec localized_data eq.
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
    
  Definition unlocalize_data (ld:localized_data) :=
    match ld with
    | Ddistributed coll => dcoll coll
    | Dscalar d => d
    end.

  Lemma unlocalize_distributed_id (l:list data) :
    unlocalize_data (Ddistributed l) = dcoll l.
  Proof.
    reflexivity.
  Qed.

  
End LData.


(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)

