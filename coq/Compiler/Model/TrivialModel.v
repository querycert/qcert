(*
 * Copyright 2015-2016 IBM Corporation
 *
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
Require Import EquivDec.

Require Import Utils.
Require Import CommonSystem.
Require Import ForeignToJava.
Require Import ForeignToJavaScript.
Require Import ForeignToJavaScriptAst.
Require Import ForeignToScala.
Require Import ForeignDataToJSON.
Require Import ForeignTypeToJSON.
Require Import ForeignReduceOps.
Require Import ForeignToReduceOps.
Require Import ForeignToSpark.
Require Import CompilerRuntime.
Require Import CompilerModel.
Require NNRCMR.
Require Import OptimizerLogger.
Require Import String.
Require Import cNRAEnv.
Require Import NRAEnv.
Require Import cNNRC.
Require Import NNRSimp.
Require Import DNNRCBase.
Require Import tDNNRC.
Require Import Dataframe.

Program Instance trivial_foreign_data : foreign_data
  := mk_foreign_data Empty_set _ _ _ _ _ _.
Next Obligation.
  intros []. 
Defined.
Next Obligation.
  destruct a.
Defined.
Next Obligation.
  destruct a.
Defined.
Next Obligation.
  constructor; intros [].
Defined.

Program Instance trivial_foreign_unary_op:
  foreign_unary_op
  := mk_foreign_unary_op trivial_foreign_data Empty_set _ _ _ _ defaultDataToString defaultDataToString.
Next Obligation.
  intros []. 
Defined.
Next Obligation.
  constructor.
  intros []. 
Defined.
Next Obligation.
  destruct op. 
Defined.
Next Obligation.
  destruct op. 
Defined.

Program Instance trivial_foreign_binary_op:
  foreign_binary_op
  := mk_foreign_binary_op trivial_foreign_data Empty_set _ _ _ _.
Next Obligation.
  intros []. 
Defined.
Next Obligation.
  constructor.
  intros []. 
Defined.
Next Obligation.
  destruct op. 
Defined.
Next Obligation.
  destruct op. 
Defined.

  Program Instance trivial_foreign_to_JSON : foreign_to_JSON
    := mk_foreign_to_JSON trivial_foreign_data _ _ _.
  Next Obligation.
    exact None.
  Defined.
  Next Obligation.
     destruct fd. 
  Defined.
  Next Obligation.
    destruct fd.
  Qed.
  
  Instance trivial_foreign_runtime :
    foreign_runtime
  := mk_foreign_runtime
       trivial_foreign_data
       trivial_foreign_unary_op
       trivial_foreign_binary_op
       trivial_foreign_to_JSON.

  Program Instance trivial_foreign_type : foreign_type
    := mk_foreign_type Empty_set _ _ _ _ _ _ _.
  Next Obligation.
     intros []. 
  Defined.
  Next Obligation.
    econstructor;
      intros [].
    Grab Existential Variables.
    solve [intros []].
    solve [intros []].
  Defined.
  Next Obligation.
    destruct a.
  Defined.
  Next Obligation.
    destruct a.
  Defined.
  Next Obligation.
    constructor;
      intros [].
  Defined.
  Next Obligation.
    intros [].
  Defined.
  Next Obligation.
    econstructor;
      intros [].
  Defined.

  Program Instance trivial_foreign_data_typing :
    @foreign_data_typing trivial_foreign_data trivial_foreign_type
    := mk_foreign_data_typing
         trivial_foreign_data
         trivial_foreign_type
         _ _ _ _ _ _ _ _.
  Next Obligation.
    destruct d.
  Defined.
  Next Obligation.
    destruct d.
  Defined.
  Next Obligation.
    destruct d.
  Defined.
  Next Obligation.
    destruct d.
  Defined.
  Next Obligation.
    destruct d.
  Defined.

  Program Instance trivial_foreign_unary_op_typing
          {model:brand_model} :
    @foreign_unary_op_typing
      trivial_foreign_data
      trivial_foreign_unary_op
      trivial_foreign_type
      trivial_foreign_data_typing
      model
    := mk_foreign_unary_op_typing
         _ _ _ _ _ _
         _ _ _ _ _ _.
  Next Obligation.
    destruct fu.
  Defined.
  Next Obligation.
    destruct fu.
  Defined.
  Next Obligation.
    destruct fu.
  Defined.
  Next Obligation.
    destruct fu.
  Defined.
  Next Obligation.
    destruct fu.
  Defined.
  Next Obligation.
    destruct fu.
  Defined.
  Next Obligation.
    destruct fu.
  Defined.
  

  Program Instance trivial_foreign_binary_op_typing
          {model:brand_model} :
    @foreign_binary_op_typing
      trivial_foreign_data
      trivial_foreign_binary_op
      trivial_foreign_type
      trivial_foreign_data_typing
      model
    := mk_foreign_binary_op_typing
         _ _ _ _ _ _
         _ _ _ _ _ _.
  Next Obligation.
    destruct fb.
  Defined.
  Next Obligation.
    destruct fb.
  Defined.
  Next Obligation.
    destruct fb.
  Defined.
  Next Obligation.
    destruct fb.
  Defined.
  Next Obligation.
    destruct fb.
  Defined.
  Next Obligation.
    destruct fb.
  Defined.
  Next Obligation.
    destruct fb.
  Defined.

  Instance trivial_foreign_typing {model:brand_model}:
    @foreign_typing
      trivial_foreign_runtime
      trivial_foreign_type
      model
  := mk_foreign_typing
       trivial_foreign_runtime
       trivial_foreign_type
       model
       trivial_foreign_data_typing
       trivial_foreign_unary_op_typing
       trivial_foreign_binary_op_typing.

  Instance trivial_basic_model {model:brand_model} :
    basic_model
    := mk_basic_model
         trivial_foreign_runtime
         trivial_foreign_type
         model
         trivial_foreign_typing.

  Program Instance trivial_foreign_to_java :
    @foreign_to_java trivial_foreign_runtime
    := mk_foreign_to_java
         trivial_foreign_runtime
         _ _ _.
  Next Obligation.
    destruct fd.
  Defined.

  Program Instance trivial_foreign_to_javascript :
    @foreign_to_javascript trivial_foreign_runtime
    := mk_foreign_to_javascript
         trivial_foreign_runtime
         _ _.

  Program Instance trivial_foreign_to_ajavascript :
    @foreign_to_ajavascript trivial_foreign_runtime
    := mk_foreign_to_ajavascript
         trivial_foreign_runtime
         _ _.

  Program Instance trivial_foreign_to_scala :
    @foreign_to_scala trivial_foreign_runtime trivial_foreign_type
    := mk_foreign_to_scala
         trivial_foreign_runtime trivial_foreign_type
         _ _.
  Next Obligation.
    exact "TRIVIAL MODEL DOES NOT SUPPORT FOREIGN TYPES"%string.
  Defined.
  
  Program Instance trivial_foreign_type_to_JSON : foreign_type_to_JSON
    := mk_foreign_type_to_JSON trivial_foreign_type _ _.
  Next Obligation.
    exact None.
  Defined.
  Next Obligation.
     destruct fd. 
  Defined.

  Program Instance trivial_foreign_reduce_op
            {fdata:foreign_data}:
      foreign_reduce_op
    := mk_foreign_reduce_op fdata Empty_set _ _ _ _.
  Next Obligation.
     intros []. 
  Defined.
  Next Obligation.
    constructor.
    intros []. 
  Defined.
  Next Obligation.
    destruct op. 
  Defined.
  Next Obligation.
    destruct op. 
  Defined.

  Program Instance trivial_foreign_to_reduce_op :
      foreign_to_reduce_op
    := mk_foreign_to_reduce_op trivial_foreign_runtime trivial_foreign_reduce_op _ _ _ _.
  Next Obligation.
    exact None.
  Defined.
  Next Obligation.
    exact None.
  Defined.

  Program Instance trivial_foreign_to_spark : foreign_to_spark
  := mk_foreign_to_spark trivial_foreign_runtime trivial_foreign_reduce_op _ _.

Existing Instance silent_optimizer_logger.

  Module TrivialRuntime <: CompilerRuntime.
    Definition compiler_foreign_type : foreign_type
      := trivial_foreign_type.
    Definition compiler_foreign_runtime : foreign_runtime
      := trivial_foreign_runtime.
    Definition compiler_foreign_to_java : foreign_to_java
      := trivial_foreign_to_java.
    Definition compiler_foreign_to_javascript : foreign_to_javascript
      := trivial_foreign_to_javascript.
    Definition compiler_foreign_to_ajavascript : foreign_to_ajavascript
      := trivial_foreign_to_ajavascript.
    Definition compiler_foreign_to_scala : foreign_to_scala
      := trivial_foreign_to_scala.
    Definition compiler_foreign_to_JSON : foreign_to_JSON
      := trivial_foreign_to_JSON.
    Definition compiler_foreign_type_to_JSON : foreign_type_to_JSON
      := trivial_foreign_type_to_JSON.
    Definition compiler_foreign_reduce_op : foreign_reduce_op
      := trivial_foreign_reduce_op.
    Definition compiler_foreign_to_reduce_op : foreign_to_reduce_op
      := trivial_foreign_to_reduce_op.
    Definition compiler_foreign_to_spark : foreign_to_spark
      := trivial_foreign_to_spark.
    Definition compiler_nraenv_optimizer_logger : optimizer_logger string nraenv
      := silent_optimizer_logger string nraenv.
    Definition compiler_nnrc_optimizer_logger : optimizer_logger string nnrc
      := silent_optimizer_logger string nnrc.
    Definition compiler_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr
      := silent_optimizer_logger string nnrs_imp_expr.
    Definition compiler_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt
      := silent_optimizer_logger string nnrs_imp_stmt.
    Definition compiler_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp
      := silent_optimizer_logger string nnrs_imp.
    Definition compiler_dnnrc_optimizer_logger {br:brand_relation}: optimizer_logger string (@dnnrc_base _ (type_annotation unit) dataframe)
      := silent_optimizer_logger string (@dnnrc_base _ (type_annotation unit) dataframe).
    Definition compiler_foreign_data_typing : foreign_data_typing
      := trivial_foreign_data_typing.
    
  End TrivialRuntime.

  Module TrivialForeignType <: CompilerForeignType.
    Definition compiler_foreign_type : foreign_type
      := trivial_foreign_type.
  End TrivialForeignType.
  
  Module TrivialModel(bm:CompilerBrandModel(TrivialForeignType)) <: CompilerModel.
    Definition compiler_foreign_type : foreign_type
      := trivial_foreign_type.
    Definition compiler_basic_model : @basic_model
      := @trivial_basic_model bm.compiler_brand_model.
    Definition compiler_model_foreign_to_java : foreign_to_java
      := trivial_foreign_to_java.
    Definition compiler_model_foreign_to_javascript : foreign_to_javascript
      := trivial_foreign_to_javascript.
    Definition compiler_model_foreign_to_ajavascript : foreign_to_ajavascript
      := trivial_foreign_to_ajavascript.
    Definition compiler_model_foreign_to_scala : foreign_to_scala
      := trivial_foreign_to_scala.
    Definition compiler_model_foreign_to_JSON : foreign_to_JSON
      := trivial_foreign_to_JSON.
    Definition compiler_model_foreign_type_to_JSON : foreign_type_to_JSON
      := trivial_foreign_type_to_JSON.
    Definition compiler_model_foreign_reduce_op : foreign_reduce_op
      := trivial_foreign_reduce_op.
    Definition compiler_model_foreign_to_reduce_op : foreign_to_reduce_op
      := trivial_foreign_to_reduce_op.
    Definition compiler_model_foreign_to_spark : foreign_to_spark
      := trivial_foreign_to_spark.
    Definition compiler_model_nraenv_optimizer_logger : optimizer_logger string nraenv
      := silent_optimizer_logger string nraenv.
    Definition compiler_model_nnrc_optimizer_logger : optimizer_logger string nnrc
      := silent_optimizer_logger string nnrc.
    Definition compiler_model_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr
      := silent_optimizer_logger string nnrs_imp_expr.
    Definition compiler_model_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt
      := silent_optimizer_logger string nnrs_imp_stmt.
    Definition compiler_model_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp
      := silent_optimizer_logger string nnrs_imp.
    Definition compiler_model_dnnrc_optimizer_logger {br:brand_relation}: optimizer_logger string (@dnnrc_base _ (type_annotation unit) dataframe)
      := silent_optimizer_logger string (@dnnrc_base _ (type_annotation unit) dataframe).
    Definition compiler_model_foreign_data_typing : foreign_data_typing
      := trivial_foreign_data_typing.
  End TrivialModel.

