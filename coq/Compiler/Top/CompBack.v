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

Require Import CompilerRuntime.
Module CompBack(runtime:CompilerRuntime).

  Require Import String List String EquivDec.
  
  Require Import BasicSystem.

  Require Import CompUtil.
  
  (* Compilation from NNRC to Javascript *)

  Require Import NNRC.
  Require Import NNRCtoJava ForeignToJava .
  Require Import NNRCtoJavascript ForeignToJavascript.
  
  Definition nrc_to_java_code_gen (class_name:string) (imports:string) (e:nrc) : string :=
    nrcToJavaTop class_name imports e.

  Definition nrc_to_js_code_gen (e:nrc) : string :=
    nrcToJSTop e.

  (* Compilation from DNNRC to Scala *)

  Require Import DNNRC.
  Require Import DNNRCtoScala RAlgEnv.
  Require Import TypingRuntime.

  Definition dnrc_to_scala_code_gen {h:brand_relation_t} (bm:brand_model) (inputType:rtype) (name:string) (e:dnrc_algenv) : string :=
    @dnrcToSpark2Top _ h bool _ _ _ bm inputType name e.

  (* Compilation from NNRCMR to CloudantMR *)

  Definition localization := DData.dlocalization.

  Require Import NNRCMR CloudantMR NNRCMRtoCloudant CloudantMRtoJavascript ForeignToCloudant.
  Require Import NRewMR.

  (* Java equivalent: MROptimizer.optimize *)
  Definition nrcmr_to_nrcmr_prepared_for_cldmr (env_vars:list (var * dlocalization)) (e_mr:nrcmr) : nrcmr :=
    let e_mr := foreign_to_cloudant_prepare_nrcmr e_mr in
    let e_mr := mr_optimize e_mr in
    (* Maybe add call to nnrc_to_nnrcmr_no_chain in case e_mr is more than one Map/Reduce *)
    let e_mr := foreign_to_cloudant_prepare_nrcmr e_mr in
    let e_mr := nrcmr_rename_for_cloudant (List.map fst env_vars) e_mr in
    e_mr.

  Definition nrcmr_to_cldmr_chain_translate (h:list (string*string)) (env_vars:list (var * dlocalization)) (e_mr:nrcmr) : cld_mrl :=
    NNRCMRtoNNRCMRCloudantTop h env_vars e_mr.

  Definition nrcmr_to_cldmr_chain_with_prepare (h:list (string*string)) (env_vars:list (var * dlocalization)) (e_mr:nrcmr) : cld_mrl :=
    let e_mr := nrcmr_to_nrcmr_prepared_for_cldmr env_vars e_mr in
    let cld_mr := NNRCMRtoNNRCMRCloudantTop h env_vars e_mr in
    cld_mr.

  (* To Cloudant *)

  Definition nrcmr_to_cloudant_code_gen_with_prepare
             (h:list (string*string)) (env_vars:list (var * dlocalization)) (e_mr:nrcmr) (rulename:string) : (list (string*string) * (string * list string)) :=
    let mrl := nrcmr_to_cldmr_chain_with_prepare h env_vars e_mr in
    mapReducePairstoCloudant h mrl rulename.

  Definition cldmr_code_gen (h:list (string*string)) (mrl:cld_mrl) (rulename:string) :=
    mapReducePairstoCloudant h mrl rulename.
  
  (* To Spark *)

  Require Import NNRCMRtoSpark ForeignToSpark.

  Definition nrcmr_to_nrcmr_prepared_for_spark (env_vars:list (var * dlocalization)) (e_mr:nrcmr) : nrcmr :=
    let e_mr := foreign_to_spark_prepare_nrcmr e_mr in
    let e_mr := mr_optimize e_mr in
    let e_mr := foreign_to_spark_prepare_nrcmr e_mr in
    let e_mr := nrcmr_rename_for_spark (List.map fst env_vars) e_mr in
    e_mr.

  Definition mrchain_to_spark_code_gen_with_prepare rulename (env_vars:list (var * dlocalization)) (e_mr:nrcmr) :=
    let e_mr := nrcmr_to_nrcmr_prepared_for_spark env_vars e_mr in
    let spark_mr := nrcmrToSparkTopDataFromFileTop rulename init_vinit env_vars e_mr in
    spark_mr.

  Definition mrchain_to_spark_code_gen rulename (env_vars:list (var * dlocalization)) (e_mr:nrcmr) :=
    nrcmrToSparkTopDataFromFileTop rulename init_vinit env_vars e_mr.

End CompBack.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
