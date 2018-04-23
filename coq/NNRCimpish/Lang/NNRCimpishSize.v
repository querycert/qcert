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
Require Import NNRCimpish.

Section NNRCimpishSize.
  Context {fruntime:foreign_runtime}.

  Fixpoint nnrc_impish_expr_size (n:nnrc_impish_expr) : nat
    := match n with
       | NNRCimpishGetConstant v => 1
       | NNRCimpishVar v => 1
       | NNRCimpishConst d => 1
       | NNRCimpishBinop op n₁ n₂ => S (nnrc_impish_expr_size n₁ + nnrc_impish_expr_size n₂)
       | NNRCimpishUnop op n₁ => S (nnrc_impish_expr_size n₁)
       | NNRCimpishGroupBy g sl e => S (nnrc_impish_expr_size e)
       end.

    Fixpoint nnrc_impish_stmt_size (n:nnrc_impish_stmt) : nat
    := match n with
       | NNRCimpishSeq s₁ s₂ => S (nnrc_impish_stmt_size s₁ + nnrc_impish_stmt_size s₂)
       | NNRCimpishLet v e s => S (nnrc_impish_expr_size e + nnrc_impish_stmt_size s)
       | NNRCimpishLetMut v eo s => S (nnrc_impish_stmt_size s + nnrc_impish_stmt_size s)
       | NNRCimpishLetMutColl _ s₁ s₂ => S (nnrc_impish_stmt_size s₁ + nnrc_impish_stmt_size s₂)
       | NNRCimpishAssign _ e => S (nnrc_impish_expr_size e)
       | NNRCimpishPush _ e => S (nnrc_impish_expr_size e)
       | NNRCimpishFor v n₁ n₂ => S (nnrc_impish_expr_size n₁ + nnrc_impish_stmt_size n₂)
       | NNRCimpishIf n₁ n₂ n₃ => S (nnrc_impish_expr_size n₁ + nnrc_impish_stmt_size n₂ + nnrc_impish_stmt_size n₃)
       | NNRCimpishEither nd vl nl vr nr => S (nnrc_impish_expr_size nd + nnrc_impish_stmt_size nl + nnrc_impish_stmt_size nr)
       end.

    Definition nnrc_impish_size (q:nnrc_impish) : nat :=
      let (n, v) := q in
      nnrc_impish_stmt_size n.

    Lemma nnrc_impish_expr_size_nzero (n:nnrc_impish_expr) : nnrc_impish_expr_size n <> 0.
    Proof.
      induction n; simpl; omega.
    Qed.

    Lemma nnrc_impish_stmt_size_nzero (n:nnrc_impish_stmt) : nnrc_impish_stmt_size n <> 0.
    Proof.
      induction n; simpl; omega.
    Qed.

    Corollary nnrc_impish_size_nzero (q:nnrc_impish) : nnrc_impish_size q <> 0.
    Proof.
      destruct q.
      apply nnrc_impish_stmt_size_nzero.
    Qed.

    Section Core.
      Program Definition nnrc_impish_core_size (q:nnrc_impish_core) : nat
        := nnrc_impish_size q.

      Lemma nnrc_impish_core_size_nzero (q:nnrc_impish_core) :
        nnrc_impish_core_size q <> 0.
      Proof.
        apply nnrc_impish_size_nzero.
      Qed.
    End Core.

End NNRCimpishSize.
