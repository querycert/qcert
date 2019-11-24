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

Require Import Omega.
Require Import CommonRuntime.
Require Import NRA.

Section NRASize.
  Context {fruntime:foreign_runtime}.

  Fixpoint nra_size (a:nra) : nat :=
    match a with
    | NRAGetConstant s => 1
    | NRAID => 1
    | NRAConst d => 1
    | NRABinop op a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | NRAUnop op a₁ => S (nra_size a₁)
    | NRAMap a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | NRAMapProduct a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | NRAProduct a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | NRASelect a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | NRADefault a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | NRAEither a₁ a₂=> S (nra_size a₁ + nra_size a₂)
    | NRAEitherConcat a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | NRAApp a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    end.

  Lemma nra_size_nzero (a:nra) : nra_size a <> 0.
  Proof.
    induction a; simpl; omega.
  Qed.

  Fixpoint nra_depth (a:nra) : nat :=
    (* Better to start at zero, level one is at least one nested plan *)
    match a with
    | NRAGetConstant s => 0
    | NRAID => 0
    | NRAConst d => 0
    | NRABinop op a₁ a₂ => max (nra_depth a₁) (nra_depth a₂)
    | NRAUnop op a₁ => nra_depth a₁
    | NRAMap a₁ a₂ => max (S (nra_depth a₁)) (nra_depth a₂)
    | NRAMapProduct a₁ a₂ => max (S (nra_depth a₁)) (nra_depth a₂)
    | NRAProduct a₁ a₂ => max (nra_depth a₁) (nra_depth a₂)
    | NRASelect a₁ a₂ => max (S (nra_depth a₁)) (nra_depth a₂)
    | NRADefault a₁ a₂ => max (nra_depth a₁) (nra_depth a₂)
    | NRAEither a₁ a₂=> max (nra_depth a₁) (nra_depth a₂)
    | NRAEitherConcat a₁ a₂ => max (nra_depth a₁) (nra_depth a₂)
    | NRAApp a₁ a₂ => max (nra_depth a₁) (nra_depth a₂)
    end.

End NRASize.

