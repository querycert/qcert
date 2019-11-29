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
Require Import CommonRuntime.
Require Import NRAEnvRuntime.
Require Import cNRAEnvRuntime.

Section NRAEnvtocNRAEnv.
  Context {fr:foreign_runtime}.

  Section Top.
    Context (h:brand_relation_t).

    Definition nraenv_to_nraenv_core_top (q:nraenv) : nraenv_core :=
      nraenv_to_nraenv_core q.

    Theorem nraenv_to_nraenv_core_top_correct :
      forall q:nraenv, forall global_env:bindings,
          nraenv_eval_top h q global_env =
          nraenv_core_eval_top h (nraenv_to_nraenv_core_top q) global_env.
    Proof.
      intros.
      unfold nraenv_core_eval_top.
      unfold nraenv_eval_top.
      unfold nraenv_to_nraenv_core_top.
      unfold nraenv_eval.
      reflexivity.
    Qed.
  End Top.
    
End NRAEnvtocNRAEnv.

