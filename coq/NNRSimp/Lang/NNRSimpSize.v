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
Require Import NNRSimp.

Section NNRSimpSize.

  Context {fruntime:foreign_runtime}.

  Fixpoint nnrs_imp_expr_size (n:nnrs_imp_expr) : nat
    := match n with
       | NNRSimpGetConstant v => 1
       | NNRSimpVar v => 1
       | NNRSimpConst d => 1
       | NNRSimpBinop op n₁ n₂ => S (nnrs_imp_expr_size n₁ + nnrs_imp_expr_size n₂)
       | NNRSimpUnop op n₁ => S (nnrs_imp_expr_size n₁)
       | NNRSimpGroupBy g sl e => S (nnrs_imp_expr_size e)
       end.

    Fixpoint nnrs_imp_stmt_size (n:nnrs_imp_stmt) : nat
      := match n with
       | NNRSimpSkip => 1
       | NNRSimpSeq s₁ s₂ => S (nnrs_imp_stmt_size s₁ + nnrs_imp_stmt_size s₂)
       | NNRSimpAssign _ e => S (nnrs_imp_expr_size e)
       | NNRSimpLet v None s => S (nnrs_imp_stmt_size s)
       | NNRSimpLet v (Some e) s => S (nnrs_imp_expr_size e + nnrs_imp_stmt_size s)
       | NNRSimpFor v n₁ n₂ => S (nnrs_imp_expr_size n₁ + nnrs_imp_stmt_size n₂)
       | NNRSimpIf n₁ n₂ n₃ => S (nnrs_imp_expr_size n₁ + nnrs_imp_stmt_size n₂ + nnrs_imp_stmt_size n₃)
       | NNRSimpEither nd vl nl vr nr => S (nnrs_imp_expr_size nd + nnrs_imp_stmt_size nl + nnrs_imp_stmt_size nr)
       end.

    Definition nnrs_imp_size (q:nnrs_imp) : nat :=
      let (n, v) := q in
      nnrs_imp_stmt_size n.

    Lemma nnrs_imp_expr_size_nzero (n:nnrs_imp_expr) : nnrs_imp_expr_size n <> 0.
    Proof.
      induction n; simpl; omega.
    Qed.

    Lemma nnrs_imp_stmt_size_nzero (n:nnrs_imp_stmt) : nnrs_imp_stmt_size n <> 0.
    Proof.
      induction n; simpl; try destruct o; try omega.
    Qed.

    Corollary nnrs_imp_size_nzero (q:nnrs_imp) : nnrs_imp_size q <> 0.
    Proof.
      destruct q.
      apply nnrs_imp_stmt_size_nzero.
    Qed.

    Section Core.
      Program Definition nnrs_imp_core_size (q:nnrs_imp_core) : nat
        := nnrs_imp_size q.

      Lemma nnrs_imp_core_size_nzero (q:nnrs_imp_core) :
        nnrs_imp_core_size q <> 0.
      Proof.
        apply nnrs_imp_size_nzero.
      Qed.
    End Core.

End NNRSimpSize.
