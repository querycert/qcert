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


Require Import String.
Require Import CommonSystem.
Require Import NRARuntime.
Require Import NRAEnvRuntime.
Require Import NNRCRuntime.
Require Import NNRSRuntime.
Require Import NNRCMRRuntime.
Require Import DNNRCRuntime.
Require Import tDNNRCRuntime.
Require Import CAMPRuntime.
Require Import OQLRuntime.
Require Import CompEnv.
Require Import CompLang.
Require Import CompConfig.
Require Import CompDriver.
Require Import CompilerRuntime.
Require Import TypingRuntime.
Require Import JSON.

Module QDriver(runtime:CompilerRuntime).

  Local Open Scope list_scope.

  Section QD.
    Definition optim_config := optim_config.
    Definition optim_config_default : optim_config
      := optim_config_default.
    Definition optim_config_to_json : optim_config -> json
      := optim_config_to_json.
    Definition json_to_optim_config : json -> string + optim_config
      := json_to_optim_config.

    Definition optim_config_list_to_json : json
      := optim_config_list_to_json.
    
    Definition optim_config_default_to_json : json
      := optim_config_default_to_json.
    
    Context {bm:brand_model}.
    Context {ftyping: foreign_typing}.

    Definition driver : Set := driver.
    Definition compile : driver -> query -> list query := compile.

    Definition language_of_driver : driver -> language := language_of_driver.
    Definition name_of_driver : driver -> string := name_of_driver.

    (* Compilers config *)

    Definition driver_config := driver_config.
    Definition driver_of_path : driver_config -> list language -> driver :=
      driver_of_path.

    Definition get_path_from_source_target : language -> language -> list language :=
      get_path_from_source_target.

    (* Optimizers config *)

    Definition optim_config_list := optim_config_list.

    (* Constants config *)

    Definition constants_config := constants_config.
    Definition mk_constant_config := mkConstantConfig.
    
    (* Comp *)
    (* XXX TODO : use driver *)
    Definition get_driver_from_source_target : driver_config -> language -> language -> driver := get_driver_from_source_target.

    (* Some macros, that aren't really just about source-target *)

    Definition default_dv_config := default_dv_config.
    Definition compile_from_source_target :
      driver_config -> language -> language -> query -> query
      := compile_from_source_target.

    Definition compile_nraenv_to_imp_qcert_verified :
      driver_config -> query -> query
      := compile_nraenv_to_imp_qcert_verified.

    (* Used in CompTest: *)
    Definition camp_rule_to_nraenv_optim : camp_rule -> nraenv := camp_rule_to_nraenv_optim.
    Definition camp_rule_to_nnrc_optim : camp_rule -> nnrc := camp_rule_to_nnrc_optim.

    (* Used in CALib: *)
    Definition nraenv_optim_to_nnrc_optim : nraenv -> nnrc := nraenv_optim_to_nnrc_optim.
    Definition nraenv_optim_to_nnrc_optim_to_dnnrc :
      vdbindings -> nraenv -> dnnrc
      := nraenv_optim_to_nnrc_optim_to_dnnrc.
    Definition nraenv_optim_to_nnrc_optim_to_nnrcmr_optim : vdbindings -> nraenv -> nnrcmr
      := nraenv_optim_to_nnrc_optim_to_nnrcmr_optim.

    (* Used in PrettyIL *)
    Definition nraenv_core_to_nraenv : nraenv_core -> nraenv := nraenv_core_to_nraenv.
    
    (* Used in queryTests: *)
    Definition camp_rule_to_nraenv_to_nnrc_optim : camp_rule -> nnrc := camp_rule_to_nraenv_to_nnrc_optim.
    Definition camp_rule_to_nraenv_to_nnrc_optim_to_dnnrc :
      vdbindings -> camp_rule -> dnnrc := camp_rule_to_nraenv_to_nnrc_optim_to_dnnrc.
    Definition camp_rule_to_nnrcmr : vdbindings -> camp_rule -> nnrcmr := camp_rule_to_nnrcmr.

  End QD.
End QDriver.

