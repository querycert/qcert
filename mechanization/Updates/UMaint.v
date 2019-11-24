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

Require Import RUtil.
Require Import RData.
Require Import RRelation.
Require Import RAlg.
Require Import UPropag.
Require Import UDelta.

Require Import Program.

Section UMaint.
  Fixpoint main (op:alg) (δ:Δ) : Δ :=
    match δ with
      | Δid => Δid
      | Δconst : data -> Δ
      | Δcoll : Δ -> Δ
      | Δbinop : binOp -> data -> Δ
      | Δunop : unaryOp -> Δ
      | Δmap : Δ -> Δ
      | Δselect : alg -> Δ
      | Δrec : list (string*Δ) -> Δ
      | Δcompose : Δ -> Δ -> Δ
  .

    match op with
        

(* Eventual lemma: Q @ (update Δ₀ d) = update (maint Q Δ₀ d) (Q @ d) *)

(* Eventual lemma: Q @ (update Δ₀ d) = update ((maint Q Δ₀)@d) (Q @ d) *)

(* Eventual lemma: Q @ (Δ₀[@d]) = (maint d Δ₀)[@(Q @ d)] *)


End UMaint.

