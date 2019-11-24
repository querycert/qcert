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

(** * EXAMPLES manually translated from arl (JRules) *)

Require Import ZArith.
Local Open Scope Z_scope.
Require Import String.
Local Open Scope string.
Require Import List.
Import ListNotations.

Require Import Utils.
Require Import CAMPTest.
Require Import CommonSystem.
Require Import TrivialModel.
Require Import Program.
Require Import TCAMPTest.
  
(* This module encodes the examples in sample-rules.txt *)
Section TDataTest.
  (******* Defining model – should be automatized, but for now *** *)

  Definition personcoll :=
    (jobject (("$coll",jobject
                         (
                           ("pid",jstring "Nat")
                             :: ("name",jstring "String")
                             :: ("age",jstring "Nat")
                             :: ("company", jstring "Nat")::nil))::nil)).

  Definition personconst :=
    (jobject (("dist",jstring "distr")::("type",personcoll)::nil)).
  Existing Instance trivial_foreign_type.
  Existing Instance CPRModel_relation.

  Definition vd : rtype :=
    match json_to_vrtype_with_fail personconst with
    | None => Unit
    | Some (_,t) => t
    end.

  Existing Instance CPModel.
  
  (* Eval vm_compute in (@tuncoll _ _ vd). *)
  
End TDataTest.

