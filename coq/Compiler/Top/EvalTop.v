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
Module EvalTop(runtime:CompilerRuntime).

  Require Import String List String EquivDec.
  
  Require Import BasicRuntime.
  Require Import CompUtil.
  Require CompDriver.

  Module CD := CompDriver.CompDriver(runtime).

  (****************
   * Rule Section *
   ****************)

  Require Import CAMPRuntime.

  Definition rule_eval_top (h:list(string*string)) (r:rule) (world:list data) : option (list data) :=
    eval_rule h r world.
  Definition rule_eval_top_debug (h:list(string*string)) (flag:bool) (r:rule) (world:list data) : string :=
    eval_rule_res_to_string h flag r world.

  Definition pattern_eval_top (h:list(string*string)) (p:pat) (world:list data) : option (list data) :=
    eval_pattern h p world.
  Definition pattern_eval_top_debug (h:list(string*string)) (flag:bool) (p:pat) (world:list data) : string :=
    eval_pattern_res_to_string h flag p world.


  (***************
   * OQL Section *
   ***************)
  
  Require Import OQL.

  Definition oql_eval_top (h:list(string*string)) (e:oql_expr) (world:list data) : option data :=
    oql_interp h (mkWorld world) e nil.


  (***************
   * NRA Section *
   ***************)

  Require Import NRAEnvRuntime.

  Definition algenv_eval_top (h:list(string*string)) (op:algenv) (world:list data) : option data :=
    fun_of_algenv h (mkWorld world) op (drec nil) dunit.


  (****************
   * NNRC Section *
   ****************)

  Require Import NNRCRuntime NNRCMRRuntime.
  Require Import NRAEnvtoNNRC. (* contains mkConstants *)
  Require Import NNRCtoNNRCMR. (* contains load_init_env *)

  Definition nrc_eval_top (h:list(string*string)) (e:nrc) (world:list data) : option data :=
    let cenv := mkWorld world in
    nrc_eval h ((init_venv,drec nil) :: (init_vid,dunit) :: (mkConstants (rec_sort cenv))) e.


  (*****************
   * DNNRC Section *
   *****************)

  Require Import DData DNNRC SparkIR.
  Require Import TDNRCInfer DNNRCtoScala DNNRCSparkIRRewrites.
  
  Require Import BasicSystem.
  Require Import TypingRuntime.
 
  Definition dnrc_eval_top {bm:brand_model} (h:list (string*string)) 
             (e:CD.dnnrc_dataset) (world:list data) : option data :=
    let tenv := mkDistWorld world in
    lift localize_data (@dnrc_eval _ _ _ h SparkIRPlug tenv e).

  (******************
   * NNRCMR Section *
   ******************)

  Definition nrcmr_chain_eval_top (h:list(string*string)) (e:nrcmr) (world:list data) : option data :=
    let env_with_world := mkWorld world in
    let cenv := mkConstants env_with_world in
    let loc_cenv := localize_bindings cenv in
    let res :=
        match load_init_env init_vinit loc_cenv cenv with
        | Some mr_env => nrcmr_eval h mr_env e
        | None => None
        end
    in res.


  (*****************
   * CLDMR Section *
   *****************)

  Require Import CloudantMR.

  Definition cldmr_chain_eval_top (h:list(string*string)) (e:cld_mrl) (world:list data) : option data :=
    (* mkWorldColl does not wrap cenv in a dcoll quite yet, since we
    need to create the keys first (in cld_load_init_env) *)
    let env_with_world := mkWorldColl world in
    let cenv := mkConstants env_with_world in
    cld_mrl_eval h (cld_load_init_env init_vinit cenv) e.

End EvalTop.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
