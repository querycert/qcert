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

Require Import RUtil RType RData.
Require Import RAlg.
Require Import TData TOps TAlg.

Require Import UDelta.

Require Import Program.

Section UTDelta.
  Inductive delta_type : Δ -> rtype -> Prop :=
  | Δtid {τ} :
      delta_type Δid τ
  | Δtconst {τ} c :
      data_type c τ -> delta_type (Δconst c) τ
  | Δtcoll {τ} Δ₁ :
      delta_type Δ₁ (Coll τ) -> delta_type (Δcoll Δ₁) (Coll (Coll τ))
  | Δtbinop {τ} b d1 :
      binOp_type b τ τ τ ->
      data_type d1 τ ->
      delta_type (Δbinop b d1) τ
  | Δtunop {τ} u :
      unaryOp_type u τ τ -> delta_type (Δunop u) τ
  | Δtmap {τ} Δ₁ :
      delta_type Δ₁ τ -> delta_type (Δmap Δ₁) (Coll τ)
  | Δtselect {τ} op1 :
      alg_type op1 τ Bool -> delta_type (Δselect op1) (Coll τ)
  | Δtrec {τr} Δrl pf :
      delta_rec_type Δrl τr -> delta_type (Δrec Δrl) (Rec τr pf)
  | Δtcompose {τ} Δ₁ Δ₂ :
    delta_type Δ₁ τ -> delta_type Δ₂ τ -> delta_type (Δcompose Δ₁ Δ₂) τ
  with delta_rec_type : list (string*Δ) -> list (string*rtype) -> Prop :=
  | Δtrnil :
      delta_rec_type nil nil
  | Δtrcons s τ Δ τrl1 rl1 :
      delta_type Δ τ ->
      delta_rec_type rl1 τrl1 ->
      delta_rec_type ((s,Δ) :: rl1) ((s,τ) :: τrl1).

End UTDelta.

