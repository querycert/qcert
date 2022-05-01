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
Require Import EJsonRuntime.
Require Import DataRuntime.
Require Import ForeignToJava.
Require Import ForeignToJavaScriptAst.
Require Import ForeignToWasmAst.
Require Import ForeignToScala.
Require Import ForeignDataToEJson.
Require Import ForeignEJsonToWSON.
Require Import ForeignToEJsonRuntime.
Require Import ForeignEJsonToJSON.
Require Import ForeignTypeToJSON.
Require Import ForeignReduceOps.
Require Import ForeignToReduceOps.
Require Import ForeignToSpark.
Require Import OptimizerLogger.
Require Import ForeignType.
Require Import ForeignDataTyping.
Require Import cNNRC.
Require Import cNRAEnv.
Require Import NRAEnv.
Require Import DNNRC.
Require Import tDNNRC.
Require Import NNRSimp.

Module Type CompilerRuntime.
  Global Declare Instance compiler_foreign_type : foreign_type.
  Global Declare Instance compiler_foreign_runtime : foreign_runtime.
  Axiom compiler_foreign_ejson_model : Set.
  Global Declare Instance compiler_foreign_ejson : foreign_ejson compiler_foreign_ejson_model.
  Axiom compiler_foreign_ejson_runtime_op : Set.
  Global Declare Instance compiler_foreign_to_ejson : foreign_to_ejson compiler_foreign_ejson_model compiler_foreign_ejson_runtime_op.
  Global Declare Instance compiler_foreign_to_wson : foreign_to_wson compiler_foreign_ejson_model.
  Global Declare Instance compiler_foreign_to_ejson_runtime : foreign_to_ejson_runtime.
  Global Declare Instance compiler_foreign_to_json : foreign_to_json.
  Global Declare Instance compiler_foreign_to_java : foreign_to_java.
  Global Declare Instance compiler_foreign_ejson_to_ajavascript : foreign_ejson_to_ajavascript.
  Global Declare Instance compiler_foreign_to_wasm_ast : foreign_to_wasm_ast compiler_foreign_ejson_runtime_op.
  Global Declare Instance compiler_foreign_to_scala : foreign_to_scala.
  Global Declare Instance compiler_foreign_type_to_JSON : foreign_type_to_JSON.
  Global Declare Instance compiler_foreign_reduce_op : foreign_reduce_op.
  Global Declare Instance compiler_foreign_to_reduce_op : foreign_to_reduce_op.
  Global Declare Instance compiler_foreign_to_spark : foreign_to_spark.
  Global Declare Instance compiler_nraenv_optimizer_logger : optimizer_logger string nraenv.
  Global Declare Instance compiler_nnrc_optimizer_logger : optimizer_logger string nnrc.
  Global Declare Instance compiler_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr.
  Global Declare Instance compiler_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt.
  Global Declare Instance compiler_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp.
  Global Declare Instance compiler_dnnrc_optimizer_logger : forall {br:brand_relation}, optimizer_logger string (dnnrc_typed).
  Global Declare Instance compiler_foreign_data_typing : foreign_data_typing.
End CompilerRuntime.

