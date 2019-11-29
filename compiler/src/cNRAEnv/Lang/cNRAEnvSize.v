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
Require Import cNRAEnv.

Section cNRAEnvSize.
  Context {fruntime:foreign_runtime}.

  (* Java equivalent: NraOptimizer.optim_size.cnraenv_size *)
  Fixpoint nraenv_core_size (a:nraenv_core) : nat :=
    match a with
    | cNRAEnvID => 1
    | cNRAEnvConst d => 1
    | cNRAEnvBinop op a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
    | cNRAEnvUnop op a₁ => S (nraenv_core_size a₁)
    | cNRAEnvMap a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
    | cNRAEnvMapProduct a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
    | cNRAEnvProduct a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
    | cNRAEnvSelect a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
    | cNRAEnvDefault a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
    | cNRAEnvEither a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
    | cNRAEnvEitherConcat a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
    | cNRAEnvApp a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
    | cNRAEnvGetConstant _ => 1
    | cNRAEnvEnv => 1
    | cNRAEnvAppEnv a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
    | cNRAEnvMapEnv a₁ => S (nraenv_core_size a₁)
    end.

  Lemma nraenv_core_size_nzero (a:nraenv_core) : nraenv_core_size a <> 0.
  Proof.
    induction a; simpl; omega.
  Qed.
  
  Fixpoint nraenv_core_depth (a:nraenv_core) : nat :=
    (* Better to start at zero, level one is at least one nested plan *)
    match a with
    | cNRAEnvID => 0
    | cNRAEnvConst d => 0
    | cNRAEnvBinop op a₁ a₂ => max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | cNRAEnvUnop op a₁ => nraenv_core_depth a₁
    | cNRAEnvMap a₁ a₂ => max (S (nraenv_core_depth a₁)) (nraenv_core_depth a₂)
    | cNRAEnvMapProduct a₁ a₂ => max (S (nraenv_core_depth a₁)) (nraenv_core_depth a₂)
    | cNRAEnvProduct a₁ a₂ => max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | cNRAEnvSelect a₁ a₂ => max (S (nraenv_core_depth a₁)) (nraenv_core_depth a₂)
    | cNRAEnvDefault a₁ a₂ => max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | cNRAEnvEither a₁ a₂=> max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | cNRAEnvEitherConcat a₁ a₂=> max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | cNRAEnvApp a₁ a₂ => max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | cNRAEnvGetConstant _ => 0
    | cNRAEnvEnv => 0
    | cNRAEnvAppEnv a₁ a₂ => max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | cNRAEnvMapEnv a₁ => (S (nraenv_core_depth a₁))
    end.

End cNRAEnvSize.

