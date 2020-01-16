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

(** Imp with the Json data model *)

Require Import String.
Require Import EJsonRuntime.
Require Import Imp.

Section ImpEJson.
  Section Syntax.
    Context {ftoejson:foreign_ejson}.
    Context {fejruntime:foreign_ejson_runtime}.

    Definition imp_ejson_model := ejson.
    Definition imp_ejson_constant := ejson.

    (* XXX This should contain at least:
       - all JS operators/expressions used in translation from NNRSimp to JsAst
       - all JS operators/expressions used to manipulate values in data but not in json (brands, nat, left, right, foreign)
       imp_ejson_op constructors names are based on JsAst names
       imp_ejson_runtime_op constructors names are in the JS Qcert runtime
     *)
    Definition imp_ejson_op := ejson_op. (* See ./EJson/Operators/EJsonOperators.v *)
    Definition imp_ejson_runtime_op := ejson_runtime_op.  (* See ./EJson/Operators/EJsonRuntimeOperators.v *)
    Definition imp_ejson_expr := @imp_expr imp_ejson_model imp_ejson_op imp_ejson_runtime_op.
    Definition imp_ejson_stmt := @imp_stmt imp_ejson_model imp_ejson_op imp_ejson_runtime_op.
    Definition imp_ejson_function := @imp_function imp_ejson_model imp_ejson_op imp_ejson_runtime_op.
    Definition imp_ejson := @imp imp_ejson_model imp_ejson_op imp_ejson_runtime_op.

  End Syntax.

End ImpEJson.
