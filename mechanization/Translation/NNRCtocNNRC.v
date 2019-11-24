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
Require Import NNRC.
Require Import cNNRC.

Section NNRCtocNNRC.
  Context {fr:foreign_runtime}.

  Section Top.
    Context (h:brand_relation_t).

    Definition nnrc_to_nnrc_core_top (q:nnrc) : nnrc_core :=
      nnrc_to_nnrc_core q.

    Theorem nnrc_to_nnrc_core_top_correct :
      forall q:nnrc, forall global_env:bindings,
          nnrc_eval_top h q global_env =
          nnrc_core_eval_top h (nnrc_to_nnrc_core_top q) global_env.
    Proof.
      intros.
      unfold nnrc_core_eval_top.
      unfold nnrc_eval_top.
      unfold nnrc_to_nnrc_core_top.
      unfold lift_nnrc_core.
      simpl.
      unfold nnrc_eval.
      reflexivity.
    Qed.
  End Top.
    
End NNRCtocNNRC.

