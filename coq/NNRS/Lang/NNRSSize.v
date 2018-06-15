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
Require Import NNRS.

Section NNRSSize.
  Context {fruntime:foreign_runtime}.

  Fixpoint nnrs_expr_size (n:nnrs_expr) : nat
    := match n with
       | NNRSGetConstant v => 1
       | NNRSVar v => 1
       | NNRSConst d => 1
       | NNRSBinop op n₁ n₂ => S (nnrs_expr_size n₁ + nnrs_expr_size n₂)
       | NNRSUnop op n₁ => S (nnrs_expr_size n₁)
       | NNRSGroupBy g sl e => S (nnrs_expr_size e)
       end.

    Fixpoint nnrs_stmt_size (n:nnrs_stmt) : nat
    := match n with
       | NNRSSeq s₁ s₂ => S (nnrs_stmt_size s₁ + nnrs_stmt_size s₂)
       | NNRSLet v e s => S (nnrs_expr_size e + nnrs_stmt_size s)
       | NNRSLetMut v eo s => S (nnrs_stmt_size s + nnrs_stmt_size s)
       | NNRSLetMutColl _ s₁ s₂ => S (nnrs_stmt_size s₁ + nnrs_stmt_size s₂)
       | NNRSAssign _ e => S (nnrs_expr_size e)
       | NNRSPush _ e => S (nnrs_expr_size e)
       | NNRSFor v n₁ n₂ => S (nnrs_expr_size n₁ + nnrs_stmt_size n₂)
       | NNRSIf n₁ n₂ n₃ => S (nnrs_expr_size n₁ + nnrs_stmt_size n₂ + nnrs_stmt_size n₃)
       | NNRSEither nd vl nl vr nr => S (nnrs_expr_size nd + nnrs_stmt_size nl + nnrs_stmt_size nr)
       end.

    Definition nnrs_size (q:nnrs) : nat :=
      let (n, v) := q in
      nnrs_stmt_size n.

    Lemma nnrs_expr_size_nzero (n:nnrs_expr) : nnrs_expr_size n <> 0.
    Proof.
      induction n; simpl; omega.
    Qed.

    Lemma nnrs_stmt_size_nzero (n:nnrs_stmt) : nnrs_stmt_size n <> 0.
    Proof.
      induction n; simpl; omega.
    Qed.

    Corollary nnrs_size_nzero (q:nnrs) : nnrs_size q <> 0.
    Proof.
      destruct q.
      apply nnrs_stmt_size_nzero.
    Qed.

    Section Core.
      Program Definition nnrs_core_size (q:nnrs_core) : nat
        := nnrs_size q.

      Lemma nnrs_core_size_nzero (q:nnrs_core) :
        nnrs_core_size q <> 0.
      Proof.
        apply nnrs_size_nzero.
      Qed.
    End Core.

End NNRSSize.
