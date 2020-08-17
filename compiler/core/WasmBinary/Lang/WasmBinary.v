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
Require Import DataRuntime.
Require Import ForeignDataToEJson.
Require Import DataToEJson.

Section Wasm.
  Context {foreign_ejson_model:Set}.
  Context {fejson:foreign_ejson foreign_ejson_model}.

  (** WASM binary *)
  Parameter wasm : Set.
  Parameter wasm_eval : wasm -> @jbindings foreign_ejson_model -> option (@ejson foreign_ejson_model).
End Wasm.

Extract Constant wasm => "string".
Extract Constant wasm_eval => "(fun q -> fun env -> failwith (""Cannot evaluate binary Wasm""))".

Section Top.
  Context {foreign_ejson_model:Set}.
  Context {fejson:foreign_ejson foreign_ejson_model}.
  Context {fruntime:foreign_runtime}.
  Context {foreign_ejson_runtime_op : Set}.
  Context {fdatatoejson:foreign_to_ejson foreign_ejson_model foreign_ejson_runtime_op}.
  (* XXX We should try and compile the hierarchy in. Currenty it is still used in cast for sub-branding check *)
  Definition wasm_eval_top (cenv: bindings) (q:wasm) : option data :=
    let jenv := List.map (fun xy => (fst xy, data_to_ejson(snd xy))) cenv in
    lift ejson_to_data (wasm_eval q jenv).
End Top.
