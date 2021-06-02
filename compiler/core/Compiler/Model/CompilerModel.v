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
Require Import CompilerRuntime.
Require Import DataSystem.
Require Import ForeignEJson.
Require Import ForeignDataToEJson.
Require Import ForeignToEJsonRuntime.
Require Import ForeignEJsonToJSON.
Require Import ForeignEJsonToWSON.
Require Import ForeignTypeToJSON.
Require Import ForeignReduceOps.
Require Import ForeignToReduceOps.
Require Import ForeignToJava.
Require Import ForeignToJavaScriptAst.
Require Import ForeignToScala.
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

Module Type CompilerModel.
  Declare Instance compiler_basic_model : basic_model.
  Declare Instance compiler_model_foreign_runtime : foreign_runtime.
  Axiom compiler_model_foreign_ejson_model : Set.
  Declare Instance compiler_model_foreign_ejson : foreign_ejson compiler_model_foreign_ejson_model.
  Axiom compiler_model_foreign_ejson_runtime_op : Set.
  Declare Instance compiler_model_foreign_to_ejson : foreign_to_ejson compiler_model_foreign_ejson_model compiler_model_foreign_ejson_runtime_op.
  Declare Instance compiler_model_foreign_to_wson : foreign_to_wson compiler_model_foreign_ejson_model.
  Declare Instance compiler_model_foreign_to_ejson_runtime : foreign_to_ejson_runtime.
  Declare Instance compiler_model_foreign_to_json : foreign_to_json.
  Declare Instance compiler_model_foreign_to_java : foreign_to_java.
  Declare Instance compiler_model_foreign_ejson_to_ajavascript : foreign_ejson_to_ajavascript.
  Declare Instance compiler_model_foreign_to_scala : foreign_to_scala.
  Declare Instance compiler_model_foreign_type_to_JSON : foreign_type_to_JSON.
  Declare Instance compiler_model_foreign_reduce_op : foreign_reduce_op.
  Declare Instance compiler_model_foreign_to_reduce_op : foreign_to_reduce_op.
  Declare Instance compiler_model_foreign_to_spark : foreign_to_spark.
  Declare Instance compiler_model_nraenv_optimizer_logger : optimizer_logger string nraenv.
  Declare Instance compiler_model_nnrc_optimizer_logger : optimizer_logger string nnrc.
  Declare Instance compiler_model_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr.
  Declare Instance compiler_model_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt.
  Declare Instance compiler_model_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp.
  Declare Instance compiler_model_dnnrc_optimizer_logger : forall {br:brand_relation}, optimizer_logger string (dnnrc_typed).
  Declare Instance compiler_model_foreign_data_typing : foreign_data_typing.
End CompilerModel.

Module CompilerModelRuntime(model:CompilerModel) <: CompilerRuntime.
  Definition compiler_foreign_type : foreign_type
    := basic_model_foreign_type.
  Definition compiler_foreign_runtime : foreign_runtime
    := model.compiler_model_foreign_runtime.
  Definition compiler_foreign_ejson_model : Set
    := model.compiler_model_foreign_ejson_model.
  Definition compiler_foreign_ejson : foreign_ejson compiler_foreign_ejson_model
    := model.compiler_model_foreign_ejson.
  Definition compiler_foreign_ejson_runtime_op : Set
    := model.compiler_model_foreign_ejson_runtime_op.
  Definition compiler_foreign_to_ejson : foreign_to_ejson compiler_foreign_ejson_model compiler_foreign_ejson_runtime_op
    := model.compiler_model_foreign_to_ejson.
  Definition compiler_foreign_to_wson : foreign_to_wson compiler_foreign_ejson_model
    := model.compiler_model_foreign_to_wson.
  Definition compiler_foreign_to_ejson_runtime : foreign_to_ejson_runtime
    := model.compiler_model_foreign_to_ejson_runtime.
  Definition compiler_foreign_to_json : foreign_to_json
    := model.compiler_model_foreign_to_json.
  Definition compiler_foreign_to_java : foreign_to_java
    := model.compiler_model_foreign_to_java.
  Definition compiler_foreign_ejson_to_ajavascript : foreign_ejson_to_ajavascript
    := model.compiler_model_foreign_ejson_to_ajavascript.
  Definition compiler_foreign_to_scala : foreign_to_scala
    := model.compiler_model_foreign_to_scala.
  Definition compiler_foreign_type_to_JSON : foreign_type_to_JSON
    := model.compiler_model_foreign_type_to_JSON.
  Definition compiler_foreign_reduce_op : foreign_reduce_op
    := model.compiler_model_foreign_reduce_op.
  Definition compiler_foreign_to_reduce_op : foreign_to_reduce_op
    := model.compiler_model_foreign_to_reduce_op.
  Definition compiler_foreign_to_spark : foreign_to_spark
    := model.compiler_model_foreign_to_spark.
  Definition compiler_nraenv_optimizer_logger : optimizer_logger string nraenv
    :=  model.compiler_model_nraenv_optimizer_logger.
  Definition compiler_nnrc_optimizer_logger : optimizer_logger string nnrc
    :=  model.compiler_model_nnrc_optimizer_logger.
  Definition compiler_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr
    :=  model.compiler_model_nnrs_imp_expr_optimizer_logger.
  Definition compiler_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt
    :=  model.compiler_model_nnrs_imp_stmt_optimizer_logger.
  Definition compiler_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp
    :=  model.compiler_model_nnrs_imp_optimizer_logger.
  Definition compiler_dnnrc_optimizer_logger {br:brand_relation}: optimizer_logger string  (dnnrc_typed)
    :=  model.compiler_model_dnnrc_optimizer_logger.
  Definition compiler_foreign_data_typing : foreign_data_typing
    := model.compiler_model_foreign_data_typing.
End CompilerModelRuntime.

(* Useful utility module functors that create a CompilerModel *)
Module Type CompilerForeignType.
  Declare Instance compiler_foreign_type : foreign_type.
End CompilerForeignType.
Module Type CompilerBrandModel(ftype:CompilerForeignType).
  Declare Instance compiler_brand_model : brand_model.
End CompilerBrandModel.

