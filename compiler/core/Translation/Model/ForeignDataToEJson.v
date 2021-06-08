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

Require Import DataRuntime.
Require Import ForeignRuntime.
Require Import ForeignEJson.
Require Import ForeignEJsonRuntime.

Local Open Scope string_scope.

Class foreign_to_ejson
      (foreign_ejson_model:Set)
      (foreign_ejson_runtime_op:Set)
      {fejson:foreign_ejson foreign_ejson_model}
      {fruntime:foreign_runtime}
  : Type
  := mk_foreign_to_ejson {
         foreign_to_ejson_runtime :> foreign_ejson_runtime foreign_ejson_runtime_op
         ; foreign_to_ejson_to_data
             (j:foreign_ejson_model) : foreign_data_model
         ; foreign_to_ejson_from_data
             (fd:foreign_data_model) : foreign_ejson_model
         ; foreign_to_ejson_to_data_to_ejson (fd:foreign_data_model) :
             foreign_to_ejson_to_data (foreign_to_ejson_from_data fd) = fd
       }.
