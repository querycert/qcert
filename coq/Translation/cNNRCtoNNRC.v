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
Require Import cNNRC.
Require Import NNRC.

Section cNNRCtoNNRC.
  Context {fr:foreign_runtime}.

  Section Top.
    Context (h:brand_relation_t).

    Definition nnrc_core_to_nnrc_top (q:nnrc_core) : nnrc :=
      nnrc_core_to_nnrc q.

    Theorem nnrc_core_to_nnrc_top_correct :
      forall q:nnrc_core, forall global_env:bindings,
          nnrc_core_eval_top h q global_env =
          nnrc_eval_top h (nnrc_core_to_nnrc_top q) global_env.
    Proof.
      intros.
      unfold nnrc_eval_top.
      unfold nnrc_core_eval_top.
      unfold nnrc_core_to_nnrc_top.
      unfold lift_nnrc_core.
      unfold nnrc_eval.
      destruct q; simpl.
      rewrite core_nnrc_to_nnrc_ext_id.
      reflexivity.
      assumption.
    Qed.
  End Top.
    
End cNNRCtoNNRC.

