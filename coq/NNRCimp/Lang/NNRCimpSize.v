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

Section NNRCimpSize.
  Require Import String.
  Require Import Omega.
  Require Import EquivDec.
  Require Import Decidable.
  Require Import Utils.
  Require Import CommonRuntime.
  Require Import NNRCimp.

  Context {fruntime:foreign_runtime}.

  Fixpoint nnrc_imp_expr_size (n:nnrc_imp_expr) : nat
    := match n with
       | NNRCimpGetConstant v => 1
       | NNRCimpVar v => 1
       | NNRCimpConst d => 1
       | NNRCimpBinop op n₁ n₂ => S (nnrc_imp_expr_size n₁ + nnrc_imp_expr_size n₂)
       | NNRCimpUnop op n₁ => S (nnrc_imp_expr_size n₁)
       | NNRCimpGroupBy g sl e => S (nnrc_imp_expr_size e)
       end.

    Fixpoint nnrc_imp_stmt_size (n:nnrc_imp_stmt) : nat
    := match n with
       | NNRCimpSeq s₁ s₂ => S (nnrc_imp_stmt_size s₁ + nnrc_imp_stmt_size s₂)
       | NNRCimpLet v e s => S (nnrc_imp_expr_size e + nnrc_imp_stmt_size s)
       | NNRCimpLetMut v eo s => S (nnrc_imp_stmt_size s + nnrc_imp_stmt_size s)
       | NNRCimpLetMutColl _ s₁ s₂ => S (nnrc_imp_stmt_size s₁ + nnrc_imp_stmt_size s₂)
       | NNRCimpAssign _ e => S (nnrc_imp_expr_size e)
       | NNRCimpPush _ e => S (nnrc_imp_expr_size e)
       | NNRCimpFor v n₁ n₂ => S (nnrc_imp_expr_size n₁ + nnrc_imp_stmt_size n₂)
       | NNRCimpIf n₁ n₂ n₃ => S (nnrc_imp_expr_size n₁ + nnrc_imp_stmt_size n₂ + nnrc_imp_stmt_size n₃)
       | NNRCimpEither nd vl nl vr nr => S (nnrc_imp_expr_size nd + nnrc_imp_stmt_size nl + nnrc_imp_stmt_size nr)
       end.

    Definition nnrc_imp_size (q:nnrc_imp) : nat :=
      let (n, v) := q in
      nnrc_imp_stmt_size n.

    Lemma nnrc_imp_expr_size_nzero (n:nnrc_imp_expr) : nnrc_imp_expr_size n <> 0.
    Proof.
      induction n; simpl; omega.
    Qed.

    Lemma nnrc_imp_stmt_size_nzero (n:nnrc_imp_stmt) : nnrc_imp_stmt_size n <> 0.
    Proof.
      induction n; simpl; omega.
    Qed.

    Corollary nnrc_imp_size_nzero (q:nnrc_imp) : nnrc_imp_size q <> 0.
    Proof.
      destruct q.
      apply nnrc_imp_stmt_size_nzero.
    Qed.

    Section Core.
      Program Definition nnrc_imp_core_size (q:nnrc_imp_core) : nat
        := nnrc_imp_size q.

      Lemma nnrc_imp_core_size_nzero (q:nnrc_imp_core) :
        nnrc_imp_core_size q <> 0.
      Proof.
        apply nnrc_imp_size_nzero.
      Qed.
    End Core.

End NNRCimpSize.
