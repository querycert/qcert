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

(* This includes some rewrites/simplification rules for the Nested relational calculus *)

Require Import String.
Require Import List.
Require Import ListSet.
Require Import Arith.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import Utils.
Require Import CommonSystem.
Require Import NNRSimpSystem.
Require Import NNRSimpRewrite.

Section TNNRSimpRewrite.
  Local Open Scope nnrs_imp.

  Context {m:basic_model}.

  Hint Immediate type_NNRSimpSkip.

  Lemma distinct_nil_trew :
    NNRSimpUnop OpDistinct (‵{||}) ⇒ᵉ ‵{||}.
  Proof.
    apply nnrs_imp_expr_eq_rewrites_to.
    - apply distinct_nil_eq.
    - intros ??? typ.
      invcs typ.
      invcs H2.
      eauto.
  Qed.

  Lemma for_nil_trew x e2 :
    (NNRSimpFor x ‵{||} e2) ⇒ˢ NNRSimpSkip.
  Proof.
    apply nnrs_imp_stmt_eq_rewrites_to.
    - apply for_nil_eq.
    - eauto.
  Qed.

End TNNRSimpRewrite.
