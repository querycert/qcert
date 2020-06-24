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

Require Import Utils.
Require Import ForeignEJson.
Require Import EJson.
Require Import BrandRelation.

Section WasmAst.
  Context {fejson:foreign_ejson}.

  (** WASM programs are in AST form *)
  Parameter wasm_ast : Set.
  Parameter wasm_ast_eval : brand_relation_t -> wasm_ast -> jbindings -> option ejson.

End WasmAst.

Extract Constant wasm_ast => "Wasm.ast".
Extract Constant wasm_ast_eval => "Wasm.eval".

Require Import DataRuntime.
Require Import ForeignDataToEJson.
Require Import DataToEJson.
Section Top.
  Context {fruntime:foreign_runtime}.
  Context {fejson:foreign_ejson}.
  Context {fdatatoejson:foreign_to_ejson}.
  (* XXX We should try and compile the hierarchy in. Currenty it is still used in cast for sub-branding check *)
  Context (h:brand_relation_t).
  Definition wasm_ast_eval_top (cenv: bindings) (q:wasm_ast) : option data :=
    let jenv := List.map (fun xy => (fst xy, data_to_ejson(snd xy))) cenv in
    lift ejson_to_data (wasm_ast_eval h q jenv).
End Top.
