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
  Declare Instance compiler_foreign_type : foreign_type.
  Declare Instance compiler_foreign_runtime : foreign_runtime.
  Axiom compiler_foreign_ejson_model : Set.
  Declare Instance compiler_foreign_ejson : foreign_ejson compiler_foreign_ejson_model.
  Axiom compiler_foreign_ejson_runtime_op : Set.
  Declare Instance compiler_foreign_to_ejson : foreign_to_ejson compiler_foreign_ejson_model compiler_foreign_ejson_runtime_op.
  Declare Instance compiler_foreign_to_wson : foreign_to_wson compiler_foreign_ejson_model.
  Declare Instance compiler_foreign_to_ejson_runtime : foreign_to_ejson_runtime.
  Declare Instance compiler_foreign_to_json : foreign_to_json.
  Declare Instance compiler_foreign_to_java : foreign_to_java.
  Declare Instance compiler_foreign_ejson_to_ajavascript : foreign_ejson_to_ajavascript.
  Declare Instance compiler_foreign_to_scala : foreign_to_scala.
  Declare Instance compiler_foreign_type_to_JSON : foreign_type_to_JSON.
  Declare Instance compiler_foreign_reduce_op : foreign_reduce_op.
  Declare Instance compiler_foreign_to_reduce_op : foreign_to_reduce_op.
  Declare Instance compiler_foreign_to_spark : foreign_to_spark.
  Declare Instance compiler_nraenv_optimizer_logger : optimizer_logger string nraenv.
  Declare Instance compiler_nnrc_optimizer_logger : optimizer_logger string nnrc.
  Declare Instance compiler_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr.
  Declare Instance compiler_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt.
  Declare Instance compiler_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp.
  Declare Instance compiler_dnnrc_optimizer_logger : forall {br:brand_relation}, optimizer_logger string (dnnrc_typed).
  Declare Instance compiler_foreign_data_typing : foreign_data_typing.
End CompilerRuntime.

