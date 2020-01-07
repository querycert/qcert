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
Require Import ZArith.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Equivalence.
Require Import ToString.
Require Import String.
Require Import Utils.
Require Import ForeignType.
Require Import ForeignTypeToJSON.
Require Import ForeignToScala.

Require Import EnhancedData.
Require Import EnhancedEJson.
Require Import EnhancedDataToEJson.
Require Import EnhancedEJsonToJSON.
Require Import EnhancedToJava.
Require Import EnhancedType.

Local Open Scope nstring_scope.

Definition enhanced_to_scala_unary_op (op: enhanced_unary_op) (d: nstring) : nstring :=
  match op with
  | enhanced_unary_sql_date_op op => ^"EnhancedModel: SQL date ops not supported for now."
  | enhanced_unary_uri_op op => ^"EnhancedModel: URI ops not supported for now."
  end.

Definition enhanced_to_scala_spark_datatype (ft: foreign_type_type) : nstring :=
  (* AVI: This is obviously not correct. Where is the place I should put this? *)
  ^"FloatType".

Instance enhanced_foreign_to_scala:
  @foreign_to_scala enhanced_foreign_runtime _
  := mk_foreign_to_scala
       enhanced_foreign_runtime _
       enhanced_to_scala_unary_op
       enhanced_to_scala_spark_datatype.

