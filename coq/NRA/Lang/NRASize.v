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

Section NRASize.
  Require Import Omega.
  Require Import BasicRuntime NRA.

  Context {fruntime:foreign_runtime}.

  Fixpoint nra_size (a:nra) : nat :=
    match a with
    | AID => 1
    | AConst d => 1
    | ABinop op a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | AUnop op a₁ => S (nra_size a₁)
    | AMap a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | AMapConcat a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | AProduct a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | ASelect a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | ADefault a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | AEither a₁ a₂=> S (nra_size a₁ + nra_size a₂)
    | AEitherConcat a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | AApp a₁ a₂ => S (nra_size a₁ + nra_size a₂)
    | AGetConstant s => 1
    end.

  Lemma nra_size_nzero (a:nra) : nra_size a <> 0.
  Proof.
    induction a; simpl; omega.
  Qed.

  Fixpoint nra_depth (a:nra) : nat :=
    (* Better to start at zero, level one is at least one nested plan *)
    match a with
    | AID => 0
    | AConst d => 0
    | ABinop op a₁ a₂ => max (nra_depth a₁) (nra_depth a₂)
    | AUnop op a₁ => nra_depth a₁
    | AMap a₁ a₂ => max (S (nra_depth a₁)) (nra_depth a₂)
    | AMapConcat a₁ a₂ => max (S (nra_depth a₁)) (nra_depth a₂)
    | AProduct a₁ a₂ => max (nra_depth a₁) (nra_depth a₂)
    | ASelect a₁ a₂ => max (S (nra_depth a₁)) (nra_depth a₂)
    | ADefault a₁ a₂ => max (nra_depth a₁) (nra_depth a₂)
    | AEither a₁ a₂=> max (nra_depth a₁) (nra_depth a₂)
    | AEitherConcat a₁ a₂ => max (nra_depth a₁) (nra_depth a₂)
    | AApp a₁ a₂ => max (nra_depth a₁) (nra_depth a₂)
    | AGetConstant s => 0
    end.

End NRASize.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
