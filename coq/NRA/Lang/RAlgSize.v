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

Section RAlgSize.
  Require Import Omega.
  Require Import BasicRuntime RAlg.

  Context {fruntime:foreign_runtime}.

  Fixpoint alg_size (a:alg) : nat :=
    match a with
    | AID => 1
    | AConst d => 1
    | ABinop op a₁ a₂ => S (alg_size a₁ + alg_size a₂)
    | AUnop op a₁ => S (alg_size a₁)
    | AMap a₁ a₂ => S (alg_size a₁ + alg_size a₂)
    | AMapConcat a₁ a₂ => S (alg_size a₁ + alg_size a₂)
    | AProduct a₁ a₂ => S (alg_size a₁ + alg_size a₂)
    | ASelect a₁ a₂ => S (alg_size a₁ + alg_size a₂)
    | ADefault a₁ a₂ => S (alg_size a₁ + alg_size a₂)
    | AEither a₁ a₂=> S (alg_size a₁ + alg_size a₂)
    | AEitherConcat a₁ a₂ => S (alg_size a₁ + alg_size a₂)
    | AApp a₁ a₂ => S (alg_size a₁ + alg_size a₂)
    end.

  Lemma alg_size_nzero (a:alg) : alg_size a <> 0.
  Proof.
    induction a; simpl; omega.
  Qed.

  Fixpoint alg_depth (a:alg) : nat :=
    (* Better to start at zero, level one is at least one nested plan *)
    match a with
    | AID => 0
    | AConst d => 0
    | ABinop op a₁ a₂ => max (alg_depth a₁) (alg_depth a₂)
    | AUnop op a₁ => alg_depth a₁
    | AMap a₁ a₂ => max (S (alg_depth a₁)) (alg_depth a₂)
    | AMapConcat a₁ a₂ => max (S (alg_depth a₁)) (alg_depth a₂)
    | AProduct a₁ a₂ => max (alg_depth a₁) (alg_depth a₂)
    | ASelect a₁ a₂ => max (S (alg_depth a₁)) (alg_depth a₂)
    | ADefault a₁ a₂ => max (alg_depth a₁) (alg_depth a₂)
    | AEither a₁ a₂=> max (alg_depth a₁) (alg_depth a₂)
    | AEitherConcat a₁ a₂ => max (alg_depth a₁) (alg_depth a₂)
    | AApp a₁ a₂ => max (alg_depth a₁) (alg_depth a₂)
    end.

End RAlgSize.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
