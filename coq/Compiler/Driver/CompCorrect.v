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

Section CompCorrect.

  Require Import String.
  Require Import Morphisms.

  (** Core libraries *)
  Require Import BasicSystem.
  Require Import TypingRuntime.

  (** Query languages *)
  Require Import SQLRuntime.
  Require Import OQLRuntime.
  Require Import LambdaNRARuntime.
  (** Rule languages *)
  Require Import CAMPRuleRuntime.
  Require Import TechRuleRuntime.
  Require Import DesignRuleRuntime.
  (** Intermediate languages *)
  Require Import NRARuntime.
  Require Import NRAEnvRuntime.
  Require Import NNRCRuntime.
  Require Import NNRCMRRuntime.
  Require Import CldMRRuntime.
  Require Import DNNRCRuntime.
  Require Import CAMPRuntime.
  (** Target languages *)
  Require Import JavaScriptRuntime.
  Require Import JavaRuntime.
  Require Import SparkRDDRuntime.
  Require Import SparkDFRuntime.
  Require Import CloudantRuntime.

  (** Translations *)
  Require Import OQLtoNRAEnv.
  Require Import SQLtoNRAEnv.
  Require Import LambdaNRAtoNRAEnv.
  Require Import CAMPtoNRA.
  Require Import CAMPtocNRAEnv.
  Require Import CAMPtoNRAEnv.
  Require Import NRAtocNNRC cNRAEnvtocNNRC NRAEnvtoNNRC.
  Require Import NNRCtoJavaScript.
  Require Import NNRCtoJava.
  Require Import NNRCtoNNRCMR.
  Require Import cNNRCtoCAMP.
  Require Import NNRCMRtoNNRC.
  Require Import NNRCMRtoSparkRDD.
  Require Import NNRCMRtoCldMR.
  Require Import NNRCMRtoDNNRC.
  Require Import CldMRtoCloudant.
  Require Import NNRCtoDNNRC.
  Require Import TDNNRCInfer tDNNRCtoSparkDF.

  (** Optimizers *)
  Require Import NRAEnvOptim.
  Require Import NNRCOptim.
  Require Import NNRCMROptim.
  Require Import DNNRCOptim.
  Require Import OptimizerLogger.

  (** Foreign Datatypes Support *)
  Require Import ForeignToReduceOps.
  Require Import ForeignToSpark.
  Require Import ForeignCloudant.
  Require Import ForeignToCloudant.
  Require Import ForeignToJava.
  Require Import ForeignToJavaScript.
  Require Import ForeignToScala.

  (** Compiler Driver *)
  
  Require Import CompLang CompEnv CompConfig CompDriver.

  (* Some useful notations *)
  Local Open Scope list_scope.

  (* Context *)
  Context {ft:foreign_type}.
  Context {fr:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {fcloudant:foreign_cloudant}.
  Context {ftocloudant:foreign_to_cloudant}.
  Context {ftoredop:foreign_to_reduce_op}.
  Context {bm:brand_model}.
  Context {ftyping: foreign_typing}.
  Context {nraenv_logger:optimizer_logger string nraenv}.
  Context {nnrc_logger:optimizer_logger string nnrc}.
  Context {dnnrc_logger:optimizer_logger string (DNNRC.dnnrc fr (type_annotation unit) dataset)}.
  Context {ftojs:foreign_to_javascript}.
  Context {ftojava:foreign_to_java}.
  Context {ftos:foreign_to_scala}.
  Context {ftospark:foreign_to_spark}.

  
End CompCorrect.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
