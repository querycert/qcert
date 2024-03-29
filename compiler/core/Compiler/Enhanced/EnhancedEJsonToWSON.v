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

Require Import EquivDec.
Require Import RelationClasses.
Require Import Equivalence.
Require Import ForeignWSON.
Require Import ForeignEJsonToWSON.

Require Import EnhancedEJson.

Parameter enhanced_foreign_to_wson_from_ejson : enhanced_ejson -> foreign_wson.

Extract Constant enhanced_foreign_to_wson_from_ejson => "Wasm_enhanced.foreign_ejson_to_wson".

Global Program Instance enhanced_foreign_to_wson : foreign_to_wson _ :=
  mk_foreign_to_wson enhanced_ejson _.
Next Obligation.
  apply enhanced_foreign_to_wson_from_ejson.
  exact j.
Defined.
