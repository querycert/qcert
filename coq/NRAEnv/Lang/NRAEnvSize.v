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

Section NRAEnvSize.
  Require Import Omega.
  Require Import BasicRuntime.
  Require Import NRAEnv.

  Context {fruntime:foreign_runtime}.

  (* Java equivalent: NraOptimizer.optim_size.nraenv_size *)
  Fixpoint nraenv_size (a:nraenv) : nat
    := match a with
         | NRAEnvID => 1
         | NRAEnvConst d => 1
         | NRAEnvBinop op a₁ a₂ => S (nraenv_size a₁ + nraenv_size a₂)
         | NRAEnvUnop op a₁ => S (nraenv_size a₁)
         | NRAEnvMap a₁ a₂ => S (nraenv_size a₁ + nraenv_size a₂)
         | NRAEnvMapConcat a₁ a₂ => S (nraenv_size a₁ + nraenv_size a₂)
         | NRAEnvProduct a₁ a₂ => S (nraenv_size a₁ + nraenv_size a₂)
         | NRAEnvSelect a₁ a₂ => S (nraenv_size a₁ + nraenv_size a₂)
         | NRAEnvDefault a₁ a₂ => S (nraenv_size a₁ + nraenv_size a₂)
         | NRAEnvEither a₁ a₂ => S (nraenv_size a₁ + nraenv_size a₂)
         | NRAEnvEitherConcat a₁ a₂ => S (nraenv_size a₁ + nraenv_size a₂)
         | NRAEnvApp a₁ a₂ => S (nraenv_size a₁ + nraenv_size a₂)
         | NRAEnvGetConstant _ => 1
         | NRAEnvEnv => 1
         | NRAEnvAppEnv a₁ a₂ => S (nraenv_size a₁ + nraenv_size a₂)
         | NRAEnvMapEnv a₁ => S (nraenv_size a₁)
         (* Those are additional operators *)
         | NRAEnvFlatMap a₁ a₂ => S (nraenv_size a₁ + nraenv_size a₂)
         | NRAEnvJoin a₁ a₂ a₃ => S (nraenv_size a₁ + nraenv_size a₂ + nraenv_size a₃)
         | NRAEnvProject _ a₁ => S (nraenv_size a₁)
         | NRAEnvGroupBy _ _ a₁ => S (nraenv_size a₁)
       end.

  Lemma nraenv_size_nzero (a:nraenv) : nraenv_size a <> 0.
  Proof.
    induction a; simpl; omega.
  Qed.
  
  Fixpoint nraenv_depth (a:nraenv) : nat :=
    (* Better to start at zero, level one is at least one nested plan *)
    match a with
    | NRAEnvID => 0
    | NRAEnvConst d => 0
    | NRAEnvBinop op a₁ a₂ => max (nraenv_depth a₁) (nraenv_depth a₂)
    | NRAEnvUnop op a₁ => nraenv_depth a₁
    | NRAEnvMap a₁ a₂ => max (S (nraenv_depth a₁)) (nraenv_depth a₂)
    | NRAEnvMapConcat a₁ a₂ => max (S (nraenv_depth a₁)) (nraenv_depth a₂)
    | NRAEnvProduct a₁ a₂ => max (nraenv_depth a₁) (nraenv_depth a₂)
    | NRAEnvSelect a₁ a₂ => max (S (nraenv_depth a₁)) (nraenv_depth a₂)
    | NRAEnvDefault a₁ a₂ => max (nraenv_depth a₁) (nraenv_depth a₂)
    | NRAEnvEither a₁ a₂=> max (nraenv_depth a₁) (nraenv_depth a₂)
    | NRAEnvEitherConcat a₁ a₂=> max (nraenv_depth a₁) (nraenv_depth a₂)
    | NRAEnvApp a₁ a₂ => max (nraenv_depth a₁) (nraenv_depth a₂)
    | NRAEnvGetConstant _ => 0
    | NRAEnvEnv => 0
    | NRAEnvAppEnv a₁ a₂ => max (nraenv_depth a₁) (nraenv_depth a₂)
    | NRAEnvMapEnv a₁ => (S (nraenv_depth a₁))
    (* Those are additional operators *)
    | NRAEnvFlatMap a₁ a₂ => max (S (nraenv_depth a₁)) (nraenv_depth a₂)
    | NRAEnvJoin a₁ a₂ a₃ => max (S (nraenv_depth a₁)) (max (nraenv_depth a₂) (nraenv_depth a₃))
    | NRAEnvProject _ a₁ => (nraenv_depth a₁)
    | NRAEnvGroupBy _ _ a₁ => (nraenv_depth a₁)
    end.

End NRAEnvSize.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
