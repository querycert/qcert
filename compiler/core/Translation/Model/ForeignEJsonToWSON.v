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

Require Import ForeignEJson.
Require Import ForeignWSON.

Local Open Scope string_scope.

Class foreign_to_wson
      (foreign_ejson_model:Set)
  : Type
  := mk_foreign_to_wson {
         foreign_to_wson_from_ejson
           (j:foreign_ejson_model) : foreign_wson
       }.
