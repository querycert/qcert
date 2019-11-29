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
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNNRC.

Section cNNRCNorm.
  Context {fruntime:foreign_runtime}. 
  Context (h:brand_relation_t).
  Context (c:bindings).
 
  (** cNNRC evaluation preserves data normalization. *)
  Lemma nnrc_core_eval_normalized env e {o} :
    Forall (data_normalized h) (map snd c) ->
    nnrc_core_eval h c env e = Some o ->
    Forall (data_normalized h) (map snd env) ->
    data_normalized h o.
  Proof.
    revert env o. nnrc_cases (induction e) Case; simpl; intros env o Hc; intros.
    - Case "NNRCGetConstant"%string.
      rewrite Forall_forall in Hc.
      unfold edot in H. apply assoc_lookupr_in in H.
      apply (Hc o).
      rewrite in_map_iff.
      exists (v,o); eauto.
    - Case "NNRCVar"%string.
      rewrite Forall_forall in H0.
      apply lookup_in in H.
      apply (H0 o).
      rewrite in_map_iff.
      exists (v,o); eauto.
    - Case "NNRCConst"%string.
      inversion H; subst; intros.
      apply normalize_normalizes.
    - Case "NNRCBinop"%string.
      case_eq (nnrc_core_eval h c env e1); [intros ? eqq1 | intros eqq1];
      (rewrite eqq1 in *;
      case_eq (nnrc_core_eval h c env e2); [intros ? eqq2 | intros eqq2];
      rewrite eqq2 in *); simpl in *; try discriminate.
      eapply binary_op_eval_normalized; eauto.
    - Case "NNRCUnop"%string.
      case_eq (nnrc_core_eval h c env e); [intros ? eqq1 | intros eqq1];
      rewrite eqq1 in *;
        simpl in *; try discriminate.
      eapply unary_op_eval_normalized; eauto.
    - Case "NNRCLet"%string.
      case_eq (nnrc_core_eval h c env e1); [intros ? eqq1 | intros eqq1];
      rewrite eqq1 in *;
        simpl in *; try discriminate.
      case_eq (nnrc_core_eval h c ((v,d)::env) e2); [intros ? eqq2 | intros eqq2];
      rewrite eqq2 in *;
        simpl in *; try discriminate.
      inversion H; subst.
      eapply IHe2; eauto.
      constructor; eauto.
    - Case "NNRCFor"%string.
      case_eq (nnrc_core_eval h c env e1); [intros ? eqq1 | intros eqq1];
      rewrite eqq1 in *;
      simpl in *; try discriminate.
      destruct d; try discriminate.
      specialize (IHe1 _ _ Hc eqq1 H0).
      inversion IHe1; subst.
      apply some_lift in H.
      destruct H; subst.
      constructor.
      apply (lift_map_Forall e H2); intros.
      apply (IHe2 _ _ Hc H).
      constructor; eauto.
    - Case "NNRCIf"%string.
      case_eq (nnrc_core_eval h c env e1); [intros ? eqq1 | intros eqq1];
      rewrite eqq1 in *;
      simpl in *; try discriminate.
      destruct d; try discriminate.
      destruct b; eauto.
    - Case "NNRCEither"%string.
      case_eq (nnrc_core_eval h c env e1); [intros ? eqq1 | intros eqq1];
      rewrite eqq1 in *;
      simpl in *; try discriminate.
      specialize (IHe1 _ _ Hc eqq1 H0).
      destruct d; try discriminate; inversion IHe1; subst.
      + eapply IHe2; eauto.
         constructor; eauto.
      + eapply IHe3; eauto.
        constructor; eauto.
    - Case "NNRCGroupBy"%string.
      simpl; intros; congruence.
  Qed.

End cNNRCNorm.

Hint Resolve nnrc_core_eval_normalized.

