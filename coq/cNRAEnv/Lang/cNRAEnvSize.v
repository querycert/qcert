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

Section cNRAEnvSize.
  Require Import Omega.
  Require Import CommonRuntime.
  Require Import cNRAEnv.

  Context {fruntime:foreign_runtime}.

  (* Java equivalent: NraOptimizer.optim_size.cnraenv_size *)
  Fixpoint nraenv_core_size (a:nraenv_core) : nat
    := match a with
         | ANID => 1
         | ANConst d => 1
         | ANBinop op a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
         | ANUnop op a₁ => S (nraenv_core_size a₁)
         | ANMap a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
         | ANMapConcat a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
         | ANProduct a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
         | ANSelect a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
         | ANDefault a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
         | ANEither a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
         | ANEitherConcat a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
         | ANApp a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
         | ANGetConstant _ => 1
         | ANEnv => 1
         | ANAppEnv a₁ a₂ => S (nraenv_core_size a₁ + nraenv_core_size a₂)
         | ANMapEnv a₁ => S (nraenv_core_size a₁)
       end.

  Lemma nraenv_core_size_nzero (a:nraenv_core) : nraenv_core_size a <> 0.
  Proof.
    induction a; simpl; omega.
  Qed.
  
  Fixpoint nraenv_core_depth (a:nraenv_core) : nat :=
    (* Better to start at zero, level one is at least one nested plan *)
    match a with
    | ANID => 0
    | ANConst d => 0
    | ANBinop op a₁ a₂ => max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | ANUnop op a₁ => nraenv_core_depth a₁
    | ANMap a₁ a₂ => max (S (nraenv_core_depth a₁)) (nraenv_core_depth a₂)
    | ANMapConcat a₁ a₂ => max (S (nraenv_core_depth a₁)) (nraenv_core_depth a₂)
    | ANProduct a₁ a₂ => max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | ANSelect a₁ a₂ => max (S (nraenv_core_depth a₁)) (nraenv_core_depth a₂)
    | ANDefault a₁ a₂ => max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | ANEither a₁ a₂=> max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | ANEitherConcat a₁ a₂=> max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | ANApp a₁ a₂ => max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | ANGetConstant _ => 0
    | ANEnv => 0
    | ANAppEnv a₁ a₂ => max (nraenv_core_depth a₁) (nraenv_core_depth a₂)
    | ANMapEnv a₁ => (S (nraenv_core_depth a₁))
    end.

End cNRAEnvSize.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
