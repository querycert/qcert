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
Require Import ForeignDataToEJson.
Require Import ForeignToEJsonRuntime.
Require Import ForeignEJsonToJSON.
Require Import ForeignEJsonToWSON.
Require Import ForeignTypeToJSON.
Require Import ForeignToSpark.
Require Import ForeignEJsonRuntime.
Require Import ForeignReduceOps.
Require Import ForeignToReduceOps.
Require Import NNRCMR.
Require Import cNRAEnv.
Require Import NRAEnv.
Require Import cNNRC.
Require Import NNRSimp.
Require Import DNNRCBase.
Require Import tDNNRC.
Require Import Dataframe.
Require Import CompilerRuntime.
Require Import CompilerModel.
Require Import LoggerComponent.
Require Import SqlDateComponent.
Require Import UriComponent.

(* XXX Export those for convenience *)
Require Export EnhancedData.
Require Export EnhancedEJson.
Require Export EnhancedDataToEJson.
Require Export EnhancedEJsonToJSON.
Require Export EnhancedEJsonToWSON.
Require Export EnhancedToJava.
Require Export EnhancedToJavascriptAst.
Require Export EnhancedToWasmAst.
Require Export EnhancedReduceOps.
Require Export EnhancedToReduceOps.
Require Export EnhancedToSpark.
Require Export EnhancedType.
Require Export EnhancedToScala.
Require Export EnhancedDataTyping.
Require Export EnhancedTypeToJSON.
Require Export EnhancedRuntime.
Require Export EnhancedTyping.

Instance enhanced_basic_model {model:brand_model} :
  basic_model
  := mk_basic_model
       enhanced_foreign_runtime
       enhanced_foreign_type
       model
       enhanced_foreign_typing.

Module EnhancedForeignType <: CompilerForeignType.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
End EnhancedForeignType.

Module EnhancedModel(bm:CompilerBrandModel(EnhancedForeignType)) <: CompilerModel.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
  Definition compiler_basic_model : @basic_model
    := @enhanced_basic_model bm.compiler_brand_model.
  Definition compiler_model_foreign_runtime : foreign_runtime
    := enhanced_foreign_runtime.
  Definition compiler_model_foreign_ejson_model : Set
    := enhanced_ejson.
  Definition compiler_model_foreign_ejson : foreign_ejson compiler_model_foreign_ejson_model
    := enhanced_foreign_ejson.
  Definition compiler_model_foreign_ejson_runtime_op : Set
    := enhanced_foreign_ejson_runtime_op.
  Definition compiler_model_foreign_to_ejson : foreign_to_ejson compiler_model_foreign_ejson_model compiler_model_foreign_ejson_runtime_op
    := enhanced_foreign_to_ejson.
  Definition compiler_model_foreign_to_wson : foreign_to_wson compiler_model_foreign_ejson_model
    := enhanced_foreign_to_wson.
  Definition compiler_model_foreign_to_ejson_runtime : foreign_to_ejson_runtime
    := enhanced_foreign_to_ejson_runtime.
  Definition compiler_model_foreign_to_json : foreign_to_json
    := enhanced_foreign_to_json.
  Definition compiler_model_foreign_to_java : foreign_to_java
    := enhanced_foreign_to_java.
  Definition compiler_model_foreign_ejson_to_ajavascript : foreign_ejson_to_ajavascript
    := enhanced_foreign_ejson_to_ajavascript.
  Definition compiler_model_foreign_to_wasm_ast : foreign_to_wasm_ast compiler_model_foreign_ejson_runtime_op
    := enhanced_foreign_to_wasm_ast.
  Definition compiler_model_foreign_to_scala : foreign_to_scala
    := enhanced_foreign_to_scala.
  Definition compiler_model_foreign_type_to_JSON : foreign_type_to_JSON
    := enhanced_foreign_type_to_JSON.
  Definition compiler_model_foreign_reduce_op : foreign_reduce_op
    := enhanced_foreign_reduce_op.
  Definition compiler_model_foreign_to_reduce_op : foreign_to_reduce_op
    := enhanced_foreign_to_reduce_op.
  Definition compiler_model_foreign_to_spark : foreign_to_spark
    := enhanced_foreign_to_spark.
  Definition compiler_model_nraenv_optimizer_logger : optimizer_logger string nraenv
    := foreign_nraenv_optimizer_logger.
  Definition compiler_model_nnrc_optimizer_logger : optimizer_logger string nnrc
    := foreign_nnrc_optimizer_logger.
  Definition compiler_model_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr
    := foreign_nnrs_imp_expr_optimizer_logger.
  Definition compiler_model_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt
    := foreign_nnrs_imp_stmt_optimizer_logger.
  Definition compiler_model_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp
    := foreign_nnrs_imp_optimizer_logger.
  Definition compiler_model_dnnrc_optimizer_logger {br:brand_relation}: optimizer_logger string (@dnnrc_base _ (type_annotation unit) dataframe)
    := foreign_dnnrc_optimizer_logger.
  Definition compiler_model_foreign_data_typing : foreign_data_typing
    := enhanced_foreign_data_typing.
End EnhancedModel.

Module CompEnhanced.
  Module Enhanced.
    Module Model.
      Definition basic_model (bm:brand_model) : basic_model
        := @enhanced_basic_model bm.

      Definition foreign_type : foreign_type
        := enhanced_foreign_type.

      Definition foreign_typing (bm:brand_model) : foreign_typing
        := @enhanced_foreign_typing bm.

    End Model.

    Module Data.
      Definition sql_date_part := sql_date_component.
      Definition sql_date_day : sql_date_part := sql_date_DAY.
      Definition sql_date_month : sql_date_part := sql_date_MONTH.
      Definition sql_date_year : sql_date_part := sql_date_YEAR.

      Definition dsql_date (d:SQL_DATE) : data
        := dforeign (enhancedsqldate d).

      Definition dsql_date_period (d:SQL_DATE_PERIOD) : data
        := dforeign (enhancedsqldateperiod d).

    End Data.

    Module Ops.
      Module Unary.
        (* for ocaml *)
        Definition sql_date_get_component (component:sql_date_component)
          := OpForeignUnary (enhanced_unary_sql_date_op (uop_sql_date_get_component component)).
        Definition sql_date_from_string
          := OpForeignUnary (enhanced_unary_sql_date_op uop_sql_date_from_string).
        Definition sql_date_period_from_string
          := OpForeignUnary (enhanced_unary_sql_date_op uop_sql_date_period_from_string).

        Definition uri_encode
          := OpForeignUnary (enhanced_unary_uri_op (uop_uri_encode)).
        Definition uri_decode
          := OpForeignUnary (enhanced_unary_uri_op (uop_uri_decode)).

        (* for coq style syntax *)
        Definition OpSqlGetDateComponent := sql_date_get_component.
        Definition OpSqlDateFromString := sql_date_from_string.
        Definition OpSqlDatePeriodFromString := sql_date_period_from_string.

      End Unary.

      Module Binary.
        (* for ocaml *)
        Definition sql_date_plus
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_plus).
        Definition sql_date_minus
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_minus).
        Definition sql_date_ne 
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_ne).
        Definition sql_date_lt 
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_lt).
        Definition sql_date_le 
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_le).
        Definition sql_date_gt 
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_gt).
        Definition sql_date_ge 
          := OpForeignBinary (enhanced_binary_sql_date_op bop_sql_date_ge).

        Definition sql_date_period_between 
          := OpForeignBinary (enhanced_binary_sql_date_op (bop_sql_date_period_between)).
        Definition sql_date_set_component (component:sql_date_component)
          := OpForeignBinary (enhanced_binary_sql_date_op (bop_sql_date_set_component component)).
        
        (* for coq style syntax *)
        Definition OpSqlDatePlus := sql_date_plus.
        Definition OpSqlDateMinus := sql_date_minus.
        Definition OpSqlDateNe := sql_date_ne.
        Definition OpSqlDateLt := sql_date_lt.
        Definition OpSqlDateLe := sql_date_le.
        Definition OpSqlDateGt := sql_date_gt.
        Definition OpSqlDateGe := sql_date_ge.

        Definition OpSqlDatePeriodBetween := sql_date_period_between.

      End Binary.
    End Ops.
  End Enhanced.
End CompEnhanced.  
