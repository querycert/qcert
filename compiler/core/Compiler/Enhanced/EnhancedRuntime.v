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
Require Import String.
Require Import Utils.
Require Import JSONSystem.
Require Import EJsonSystem.
Require Import DataSystem.
Require Import ForeignToJava.
Require Import ForeignToJavaScriptAst.
Require Import ForeignToWasmAst.
Require Import ForeignToScala.
Require Import ForeignEJson.
Require Import ForeignWSON.
Require Import ForeignDataToEJson.
Require Import ForeignEJsonToWSON.
Require Import ForeignToEJsonRuntime.
Require Import ForeignEJsonToJSON.
Require Import ForeignTypeToJSON.
Require Import ForeignToSpark.
Require Import ForeignEJsonRuntime.
Require Import ForeignReduceOps.
Require Import ForeignToReduceOps.
Require Import NNRCMR.
Require Import OptimizerLogger.
Require Import cNRAEnv.
Require Import NRAEnv.
Require Import cNNRC.
Require Import NNRSimp.
Require Import DNNRCBase.
Require Import tDNNRC.
Require Import Dataframe.
Require Import CompilerRuntime.
Require Import CompilerModel.
Require Import SqlDateComponent.
Require Import LoggerComponent.

Require Import EnhancedData.
Require Import EnhancedEJson.
Require Import EnhancedDataToEJson.
Require Import EnhancedEJsonToJSON.
Require Import EnhancedEJsonToWSON.
Require Import EnhancedToJava.
Require Import EnhancedToJavascriptAst.
Require Import EnhancedToWasmAst.
Require Import EnhancedReduceOps.
Require Import EnhancedToReduceOps.
Require Import EnhancedToSpark.
Require Import EnhancedType.
Require Import EnhancedToScala.
Require Import EnhancedDataTyping.
Require Import EnhancedTypeToJSON.

(** Loggers *)
Section Loggers.
  Global Instance foreign_nraenv_optimizer_logger :
    optimizer_logger string nraenv
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_nraenv_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nraenv_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nraenv_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nraenv_endPass
      } .
  Global Instance foreign_nnrc_optimizer_logger :
    optimizer_logger string nnrc
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrc_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nnrc_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nnrc_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nnrc_endPass
      } .
  Global Instance foreign_nnrs_imp_expr_optimizer_logger :
    optimizer_logger string nnrs_imp_expr
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrs_imp_expr_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nnrs_imp_expr_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nnrs_imp_expr_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nnrs_imp_expr_endPass
      } .
  Global Instance foreign_nnrs_imp_stmt_optimizer_logger :
    optimizer_logger string nnrs_imp_stmt
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nnrs_imp_stmt_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nnrs_imp_stmt_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nnrs_imp_stmt_endPass
      } .
  Global Instance foreign_nnrs_imp_optimizer_logger :
    optimizer_logger string nnrs_imp
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrs_imp_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nnrs_imp_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nnrs_imp_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nnrs_imp_endPass
      } .
  Definition dnnrc_for_log {br:brand_relation}
    := (@dnnrc_base enhanced_foreign_runtime (type_annotation unit) dataframe).

  Global Instance foreign_dnnrc_optimizer_logger {br:brand_relation} :
    optimizer_logger string dnnrc_for_log
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_dnnrc_token_type
        ; logStartPass := OPTIMIZER_LOGGER_dnnrc_startPass
        ; logStep :=  OPTIMIZER_LOGGER_dnnrc_step
        ; logEndPass :=  OPTIMIZER_LOGGER_dnnrc_endPass
      } .
End Loggers.

Module EnhancedRuntime <: CompilerRuntime.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
  Definition compiler_foreign_runtime : foreign_runtime
    := enhanced_foreign_runtime.
  Definition compiler_foreign_to_java : foreign_to_java
    := enhanced_foreign_to_java.
  Definition compiler_foreign_ejson_model : Set
    := enhanced_ejson.
  Definition compiler_foreign_ejson : foreign_ejson compiler_foreign_ejson_model
    := enhanced_foreign_ejson.
  Definition compiler_foreign_ejson_runtime_op : Set :=
    enhanced_foreign_ejson_runtime_op.
  Definition compiler_foreign_to_ejson : foreign_to_ejson compiler_foreign_ejson_model compiler_foreign_ejson_runtime_op
    := enhanced_foreign_to_ejson.
  Definition compiler_foreign_to_wson : foreign_to_wson compiler_foreign_ejson_model
    := enhanced_foreign_to_wson.
  Definition compiler_foreign_to_ejson_runtime : foreign_to_ejson_runtime
    := enhanced_foreign_to_ejson_runtime.
  Definition compiler_foreign_to_json : foreign_to_json
    := enhanced_foreign_to_json.
  Definition compiler_foreign_ejson_to_ajavascript : foreign_ejson_to_ajavascript
    := enhanced_foreign_ejson_to_ajavascript.
  Definition compiler_foreign_to_wasm_ast : foreign_to_wasm_ast compiler_foreign_ejson_runtime_op
    := enhanced_foreign_to_wasm_ast.
  Definition compiler_foreign_to_scala : foreign_to_scala
    := enhanced_foreign_to_scala.
  Definition compiler_foreign_type_to_JSON : foreign_type_to_JSON
    := enhanced_foreign_type_to_JSON.
  Definition compiler_foreign_reduce_op : foreign_reduce_op
    := enhanced_foreign_reduce_op.
  Definition compiler_foreign_to_reduce_op : foreign_to_reduce_op
    := enhanced_foreign_to_reduce_op.
  Definition compiler_foreign_to_spark : foreign_to_spark
    := enhanced_foreign_to_spark.
  Definition compiler_nraenv_optimizer_logger : optimizer_logger string nraenv
    := foreign_nraenv_optimizer_logger.
  Definition compiler_nnrc_optimizer_logger : optimizer_logger string nnrc
    := foreign_nnrc_optimizer_logger.
  Definition compiler_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr
    := foreign_nnrs_imp_expr_optimizer_logger.
  Definition compiler_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt
    := foreign_nnrs_imp_stmt_optimizer_logger.
  Definition compiler_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp
    := foreign_nnrs_imp_optimizer_logger.
  Definition compiler_dnnrc_optimizer_logger {br:brand_relation}: optimizer_logger string (@dnnrc_base _ (type_annotation unit) dataframe)
    := foreign_dnnrc_optimizer_logger.
  Definition compiler_foreign_data_typing : foreign_data_typing
    := enhanced_foreign_data_typing.
End EnhancedRuntime.

