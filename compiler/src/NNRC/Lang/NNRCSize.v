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
Require Import Omega.
Require Import EquivDec.
Require Import Decidable.
Require Import Utils.
Require Import CommonRuntime.
Require Import cNNRC.
Require Import cNNRCShadow.

Section NNRCSize.
  Context {fruntime:foreign_runtime}.

  (* Java equivalent: NnnrcOptimizer.rew_size.nnrc_size *)
  Fixpoint nnrc_size (n:nnrc) : nat 
    := match n with
       | NNRCGetConstant v => 1
       | NNRCVar v => 1
       | NNRCConst d => 1
       | NNRCBinop op n₁ n₂ => S (nnrc_size n₁ + nnrc_size n₂)
       | NNRCUnop op n₁ => S (nnrc_size n₁)
       | NNRCLet v n₁ n₂ => S (nnrc_size n₁ + nnrc_size n₂)
       | NNRCFor v n₁ n₂ => S (nnrc_size n₁ + nnrc_size n₂)
       | NNRCIf n₁ n₂ n₃ => S (nnrc_size n₁ + nnrc_size n₂ + nnrc_size n₃)
       | NNRCEither nd vl nl vr nr => S (nnrc_size nd + nnrc_size nl + nnrc_size nr)
       | NNRCGroupBy g sl n => S (nnrc_size n)
       end.

  Lemma nnrc_size_nzero (n:nnrc) : nnrc_size n <> 0.
  Proof.
    induction n; simpl; omega.
  Qed.

  Lemma nnrc_rename_lazy_size n x1 x2:
    nnrc_size (nnrc_rename_lazy n x1 x2) = nnrc_size n.
  Proof.
    nnrc_cases (induction n) Case;
    unfold nnrc_rename_lazy in *;
    simpl;
    destruct (equiv_dec x1 x2);
    simpl;
    try reflexivity;
    try solve [ rewrite IHn1;
                rewrite IHn2;
                rewrite IHn3;
                reflexivity ];
    try solve [ rewrite IHn1;
                rewrite IHn2;
                reflexivity ];
    try solve [ rewrite IHn;
                reflexivity ];
    try solve [ rewrite IHn1;
                destruct (equiv_dec v x1);
                simpl; try reflexivity;
                rewrite IHn2;
                reflexivity ].
    - Case "NNRCVar"%string.
      destruct (equiv_dec v x1);
        simpl; reflexivity.
    - Case "NNRCEither"%string.
      rewrite IHn1.
      destruct (equiv_dec v x1);
        destruct (equiv_dec v0 x1);
        simpl; try reflexivity.
      + rewrite IHn3.
        reflexivity.
      + rewrite IHn2.
        reflexivity.
      + rewrite IHn2.
        rewrite IHn3.
        reflexivity.
  Qed.

End NNRCSize.

