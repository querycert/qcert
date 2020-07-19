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

Set Typeclasses Axioms Are Instances.

Module Type CompilerRuntime.
  Axiom compiler_foreign_type : foreign_type.
  Axiom compiler_foreign_runtime : foreign_runtime.
  Axiom compiler_foreign_ejson_model : Set.
  Axiom compiler_foreign_ejson : foreign_ejson compiler_foreign_ejson_model.
  Axiom compiler_foreign_ejson_runtime_op : Set.
  Axiom compiler_foreign_to_ejson : foreign_to_ejson compiler_foreign_ejson_model compiler_foreign_ejson_runtime_op.
  Axiom compiler_foreign_to_ejson_runtime : foreign_to_ejson_runtime.
  Axiom compiler_foreign_to_json : foreign_to_json.
  Axiom compiler_foreign_to_java : foreign_to_java.
  Axiom compiler_foreign_ejson_to_ajavascript : foreign_ejson_to_ajavascript.
  Axiom compiler_foreign_to_scala : foreign_to_scala.
  Axiom compiler_foreign_type_to_JSON : foreign_type_to_JSON.
  Axiom compiler_foreign_reduce_op : foreign_reduce_op.
  Axiom compiler_foreign_to_reduce_op : foreign_to_reduce_op.
  Axiom compiler_foreign_to_spark : foreign_to_spark.
  Axiom compiler_nraenv_optimizer_logger : optimizer_logger string nraenv.
  Axiom compiler_nnrc_optimizer_logger : optimizer_logger string nnrc.
  Axiom compiler_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr.
  Axiom compiler_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt.
  Axiom compiler_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp.
  Axiom compiler_dnnrc_optimizer_logger : forall {br:brand_relation}, optimizer_logger string (dnnrc_typed).
  Axiom compiler_foreign_data_typing : foreign_data_typing.
End CompilerRuntime.

