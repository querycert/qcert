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

(* This includes some rewrites/simplification rules for the Nested relational calculus *)

Require Import String.
Require Import List.
Require Import ListSet.
Require Import Arith.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import Decidable.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import CommonRuntime.
Require Import NNRSimpRuntime.

Section NNRSimpRewrite.
  Local Open Scope nnrs_imp.

  Context {fruntime:foreign_runtime}.

  Lemma distinct_nil_eq :
    NNRSimpUnop OpDistinct (‵{||}) ≡ᵉ ‵{||}.
  Proof.
    red; simpl; trivial.
  Qed.
  
  Lemma for_nil_eq x e2 :
    (NNRSimpFor x ‵{||} e2) ≡ˢ NNRSimpSkip.
  Proof.
    red; simpl; trivial.
  Qed.

End NNRSimpRewrite.

