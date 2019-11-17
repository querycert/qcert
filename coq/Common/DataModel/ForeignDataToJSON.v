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
Require Import Utils.
Require Import ForeignData.
Require Import JSON.

Local Open Scope string_scope.

Section ForeignDatatoJSON.

(* TODO: properties required to ensure round-tripping *)

Class foreign_to_JSON {fdata:foreign_data}: Type
  := mk_foreign_to_JSON {
         foreign_to_JSON_to_data
           (j:json) : option foreign_data_type
         ; foreign_to_JSON_from_data
             (fd:foreign_data_type) : json
         ; foreign_to_JSON_to_data_to_json (fd:foreign_data_type) :
             foreign_to_JSON_to_data (foreign_to_JSON_from_data fd) = Some fd
       }.

End ForeignDatatoJSON.

