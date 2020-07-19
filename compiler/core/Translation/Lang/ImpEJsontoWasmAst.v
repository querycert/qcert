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

Require Import String.
Require Import List.
Require Import EJsonRuntime.
Require Import Imp.
Require Export ImpEJson.
Require Import WasmAstRuntime.

Section ImpEJsontoWasmAst.
  Section Top.
    Context {foreign_ejson_model:Set}.
    Context {foreign_ejson_runtime_op : Set}.

    Axiom imp_ejson_to_wasm_ast : @imp_ejson foreign_ejson_model foreign_ejson_runtime_op -> wasm_ast.
  End Top.
    
End ImpEJsontoWasmAst.

Extract Constant imp_ejson_to_wasm_ast => "Wasm_ast.imp_ejson_to_wasm_ast".
