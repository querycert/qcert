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
Require Import Utils.
Require Import CommonRuntime.
Require Import cNRAEnvRuntime.
Require Import NRARuntime.

Section cNRAEnvtoNRA.
  Context {fr:foreign_runtime}.

  Section Top.
    Context (h:brand_relation_t).

    Definition nraenv_core_to_nra_top (q:nraenv_core) : nra :=
      NRAApp (nra_of_nraenv_core q) (nra_context (NRAConst (drec nil)) (NRAConst dunit)).

    Theorem nraenv_core_to_nra_top_correct :
      forall q:nraenv_core, forall global_env:bindings,
          nraenv_core_eval_top h q global_env =
          nra_eval_top h (nraenv_core_to_nra_top q) global_env.
    Proof.
      intros.
      unfold nraenv_core_eval_top.
      unfold nra_eval_top.
      unfold nraenv_core_to_nra_top.
      rewrite unfold_env_nra_sort.
      simpl.
      unfold nra_context_data.
      rewrite drec_sort_idempotent.
      reflexivity.
    Qed.
  End Top.
    
End cNRAEnvtoNRA.

