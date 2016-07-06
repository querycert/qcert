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

Require Import Utils BasicSystem.
Require Import ForeignToJava ForeignToJavascript ForeignToJSON ForeignTypeToJSON.
Require Import ForeignReduceOps ForeignToReduceOps.
Require Import ForeignToSpark.
Require Import ForeignCloudant ForeignToCloudant.
Require Import CompilerRuntime CompilerModel.
Require NNRCMR CloudantMR.
Require Import OptimizerLogger String RAlgEnv NNRC.

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

Program Instance trivial_foreign_unary_op
        {fdata:foreign_data}:
  foreign_unary_op
  := mk_foreign_unary_op fdata Empty_set _ _ _ _.
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

  Program Instance trivial_foreign_binary_op
            {fdata:foreign_data}:
      foreign_binary_op
    := mk_foreign_binary_op fdata Empty_set _ _ _ _.
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

  Instance trivial_foreign_runtime :
    foreign_runtime
  := mk_foreign_runtime
       trivial_foreign_data
       trivial_foreign_unary_op
       trivial_foreign_binary_op.

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
         _ _ _ _ _
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
  

  Program Instance trivial_foreign_binary_op_typing
          {model:brand_model} :
    @foreign_binary_op_typing
      trivial_foreign_data
      trivial_foreign_binary_op
      trivial_foreign_type
      trivial_foreign_data_typing
      model
    := mk_foreign_binary_op_typing
         _ _ _ _ _
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
         _ _ _.

  Program Instance trivial_foreign_to_JSON : foreign_to_JSON
    := mk_foreign_to_JSON trivial_foreign_data _ _.
  Next Obligation.
    exact None.
  Defined.
  Next Obligation.
     destruct fd. 
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
    := mk_foreign_to_reduce_op trivial_foreign_runtime trivial_foreign_reduce_op _ _.
  Next Obligation.
    exact None.
  Defined.

  Program Instance trivial_foreign_to_spark : foreign_to_spark
  := mk_foreign_to_spark trivial_foreign_runtime trivial_foreign_reduce_op _ _.

  Program Instance trivial_foreign_to_cloudant : foreign_to_cloudant
    := mk_foreign_to_cloudant trivial_foreign_runtime trivial_foreign_reduce_op _ _ _ _.
  Next Obligation.
    destruct rop.
  Defined.
  Next Obligation.
    exact True.
  Defined.
  Next Obligation.
    compute; trivial.
  Qed.

Instance trivial_foreign_cloudant : foreign_cloudant
  := mk_foreign_cloudant
       trivial_foreign_runtime
       ASum
       ANumMin
       ANumMax.

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
    Definition compiler_foreign_cloudant : foreign_cloudant
      := trivial_foreign_cloudant.
    Definition compiler_foreign_to_cloudant : foreign_to_cloudant
      := trivial_foreign_to_cloudant.
    Definition compiler_nra_optimizer_logger : optimizer_logger string algenv
      := silent_optimizer_logger string algenv.
    Definition compiler_nrc_optimizer_logger : optimizer_logger string nrc
      := silent_optimizer_logger string nrc.
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
    Definition compiler_model_foreign_cloudant : foreign_cloudant
      := trivial_foreign_cloudant.
    Definition compiler_model_foreign_to_cloudant : foreign_to_cloudant
      := trivial_foreign_to_cloudant.
    Definition compiler_model_nra_optimizer_logger : optimizer_logger string algenv
      := silent_optimizer_logger string algenv.
    Definition compiler_model_nrc_optimizer_logger : optimizer_logger string nrc
      := silent_optimizer_logger string nrc.
    Definition compiler_model_foreign_data_typing : foreign_data_typing
      := trivial_foreign_data_typing.
  End TrivialModel.
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
