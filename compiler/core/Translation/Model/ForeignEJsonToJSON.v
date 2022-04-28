(*
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

Require Import ForeignEJson.
Require Import JSONRuntime.

Local Open Scope string_scope.

Class foreign_to_json
      {foreign_ejson_model:Set}
      {fejson:foreign_ejson foreign_ejson_model}
  : Type
  := mk_foreign_to_json {
         foreign_to_json_to_ejson
             (fd:json) : option foreign_ejson_model
         ; foreign_to_json_from_ejson
             (j:foreign_ejson_model) : json
         (* XXX TO ADD BACK 
         ; foreign_to_json_to_ejson_to_json (fd:foreign_ejson_model) :
             foreign_to_json_to_ejson (foreign_to_json_from_ejson fd) = Some fd *)
       }.
