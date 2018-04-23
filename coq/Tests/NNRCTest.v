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

(* Notations *)

Require Import List.
Require Import Utils.
Require Import CommonRuntime.

Delimit Scope data_scope with data.

Notation "⊥" := (dunit) : data_scope. (* null value *)

Notation "[||]" := (drec nil) : data_scope. (* records *)
Notation "[| x1 ; .. ; xn |]" := (drec (cons x1 .. (cons xn nil) ..)) : data_scope.

Notation "{||}" := (dcoll nil) : data_scope. (* collections *)
Notation "{| x1 ; .. ; xn |}" := (dcoll (cons x1 .. (cons xn nil) ..)) : data_scope.

Require Import String.
Require Import ZArith.

Require Import NNRCRuntime.
Require Import cNNRC.
Require Import TrivialModel.

Section NNRCTest.
  Local Open Scope string_scope.
  Local Open Scope nnrc_scope.
  Local Open Scope data_scope.
  Open Scope Z_scope.

  Example db1
    := dcoll
         ([| ("A", dconst 1); ("B", dconst 3) |]
            :: [| ("A", dconst 1); ("B", dconst 5) |]
            :: [| ("A", dconst 2); ("B", dconst 7) |]
            :: [| ("A", dconst 4); ("B", dconst 5) |]
            :: nil).
  
  Example db2
    := dcoll
         ([| ("A", dconst 1); ("C", dconst 13) |]
            :: [| ("A", dconst 2); ("C", dconst 15) |]
            :: [| ("A", dconst 3); ("C", dconst 17) |]
            :: [| ("A", dconst 4); ("C", dconst 15) |]
            :: nil).

  (* Canned initial variable for the current value *)
  Definition init_vid := "id"%string.
  Definition init_venv := "env"%string.

  Example natural_join_aux varid varenv :=
    let (t1,t2) := fresh_var2 "tprod$" "tprod$" (varid::varenv::nil) in
    NNRCUnop OpFlatten
             (NNRCUnop OpFlatten
                       (NNRCFor t1 (NNRCConst db1)
                                (NNRCFor t2
                                         (NNRCConst db2)
                                         (NNRCBinop OpRecMerge (NNRCVar t1) (NNRCVar t2))))).
  Example natural_join : nnrc :=
    natural_join_aux init_vid init_venv.
  (* Eval vm_compute in
     (nnrc_eval_top nil natural_join nil). *)
  
End NNRCTest.
