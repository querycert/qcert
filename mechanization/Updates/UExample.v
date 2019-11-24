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

Require Import RUtil.
Require Import RBag.
Require Import RData.
Require Import RDomain.
Require Import RRelation.
Require Import ROps.
Require Import RAlg.
Require Import RAlgExt.
Require Import RAlgEq.
Require Import RExample.

Require Import UDelta.

Section UExample.
  Local Open Scope string_scope.
  Local Open Scope alg_scope.

  (***********
   * Updates *
   ***********)


  (* Resets all ages to zero *)
  Definition u1 :=
    Δmap(Δrec (("name",Δid)
                 :: ("age",Δconst (dnat 0))
                 :: ("zip",Δid)
                 :: ("company",Δid) :: nil)).

  Eval compute in (update u1 persons).

  (* Inserts a new person *)
  Definition u2 :=
    Δbinop AUnion (mkpersons (("Jones", 29, 1010, "USA") :: nil)).

  Eval compute in (persons).
  Eval compute in (update u2 persons).

  (* Removes a person *)
  Definition u3 :=
    Δbinop AMinus (mkpersons (("John",23,1008,"IBM") :: nil)).

  Eval compute in (update u3 persons).

End UExample.

