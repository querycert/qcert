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
Require Import Sorting.
Require Import Eqdep_dec.
Require Import Bool.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignType.          
Require Import RType.

Section DType.

  Context {ftype:foreign_type}.
  Context {br:brand_relation}.

  (* Note: Tdistr τ is a distributed *collection* of elements with type τ *)
  Inductive drtype : Set :=
  | Tlocal : rtype -> drtype
  | Tdistr : rtype -> drtype.
  
  (* Equality is decidable for rtype₀ *)
  Global Instance drtype_eqdec : EqDec drtype eq.
  Proof.
    red; intros.
    destruct x; destruct y.
    - destruct (r == r0); unfold equiv, complement in *; subst.
      * left; reflexivity.
      * right; congruence.
    - right; congruence.
    - right; congruence.
    - destruct (r == r0); unfold equiv, complement in *; subst.
      * left; reflexivity.
      * right; congruence.
  Defined.

  Section unlocalize.
    Definition unlocalize_drtype (dt:drtype) : rtype :=
      match dt with
      | Tlocal t => t
      | Tdistr t => Coll t
      end.

  End unlocalize.

End DType.

