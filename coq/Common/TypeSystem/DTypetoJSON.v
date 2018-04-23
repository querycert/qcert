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

Require Import List.
Require Import String.
Require Import ZArith.
Require Import Utils.
Require Import JSON.
Require Import BrandRelation.
Require Import RType.
Require Import RTypeNorm.
Require Import ForeignType.
Require Import ForeignTypeToJSON.
Require Import RTypetoJSON.
Require Import DType.

Section DTypetoJSON.
  
  Context {ftype:foreign_type}.
  Context {ftypeToJSON:foreign_type_to_JSON}.

  (* JSON to DType *)
  Definition json_to_drtype {br:brand_relation} (j:json) : drtype :=
    match j with
    | jobject (("$dist"%string,j')::nil) => Tdistr (json_to_rtype j')
    | _ => Tlocal (json_to_rtype j)
    end.

  Definition json_to_drtype_with_fail {br:brand_relation} (j:json) : option drtype :=
    match j with
    | jobject (("$dist"%string,j')::nil) => lift Tdistr (json_to_rtype_with_fail j')
    | _ => lift Tlocal (json_to_rtype_with_fail j)
    end.

End DTypetoJSON.

