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
Require Import ForeignEJson.
Require Import ForeignWSONRuntime.
Require Import ForeignToWasmAst.

Require Import EnhancedEJson.

Parameter enhanced_foreign_to_wasm_op : enhanced_foreign_ejson_runtime_op -> foreign_wson_runtime_op.

Extract Constant enhanced_foreign_to_wasm_op => "Wasm_enhanced.foreign_ejson_to_wasm_op".

Program Instance enhanced_foreign_to_wasm_ast : @foreign_to_wasm_ast enhanced_foreign_ejson_runtime_op :=
  mk_foreign_to_wasm_ast enhanced_foreign_ejson_runtime_op _.
Next Obligation.
  apply enhanced_foreign_to_wasm_op.
  exact j.
Defined.
