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
Require Import NRARuntime.
Require Import NRAEnvRuntime.
Require Import NNRCRuntime.
Require Import NNRCMRRuntime.
Require Import CloudantMR.
Require Import DNNRC Dataset.
Require Import CAMPRuntime.
Require Import ODMGRuntime.
Require Import TOptimEnvFunc.

Require Import CompDriver.

Require Import CompilerRuntime.
Module QDriver(runtime:CompilerRuntime).

  Require Import BasicSystem.
  Require Import TypingRuntime.
  Require Import CompEnv.

  Local Open Scope list_scope.

  Definition vdbindings := vdbindings.

  (* Languages *)

  Section QD.
    Context {bm:brand_model}.
    Context {ftyping: foreign_typing}.

    Definition rule := rule.
    Definition camp := camp.
    Definition oql := oql.
    Definition lambda_nra := lambda_nra.
    Definition nra := nra.
    Definition nraenv := nraenv.
    Definition nnrc := nnrc.
    Definition nnrcmr := nnrcmr.
    Definition cldmr := cldmr.
    Definition dnnrc_dataset := dnnrc_dataset.
    Definition dnnrc_typed_dataset {bm:brand_model} := dnnrc_typed_dataset.
    Definition javascript := javascript.
    Definition java := java.
    Definition spark := spark.
    Definition spark2 := spark2.
    Definition cloudant := cloudant.

    Definition language : Set := language.

    Definition query : Set := query.

    Definition driver : Set := driver.
    Definition compile : driver -> query -> list query := compile.

    Definition language_of_name_case_sensitive : string -> language :=
      language_of_name_case_sensitive.
    Definition name_of_language : language -> string :=
      name_of_language.

    Definition language_of_driver : driver -> language := language_of_driver.
    Definition name_of_driver : driver -> string := name_of_driver.
    Definition language_of_query : query -> language := language_of_query.
    Definition name_of_query : query -> string := name_of_query.

    (* Compilers config *)

    Definition driver_config := driver_config.
    Definition push_translation : driver_config -> language -> driver -> driver :=
      push_translation.
    Definition driver_of_language : language -> driver := driver_of_language.

    Definition driver_of_path : driver_config -> list language -> driver :=
      driver_of_path.
    Definition fix_driver : driver -> query -> driver := fix_driver.

    Definition get_path_from_source_target : language -> language -> list language :=
      get_path_from_source_target.

    (* Comp *)
    (* XXX TODO : use driver *)
    Definition get_driver_from_source_target : driver_config -> language -> language -> driver := get_driver_from_source_target.

    (* Some macros, that aren't really just about source-target *)

    Definition default_dv_config := default_dv_config.
    Definition compile_from_source_target :
      driver_config -> language -> language -> query -> query
      := compile_from_source_target.

    (* Used in CompStat: *)
    Definition nraenv_optim_to_nnrc : nraenv -> nnrc := nraenv_optim_to_nnrc.

    (* Used in CompTest: *)
    Definition rule_to_nraenv_optim : rule -> nraenv := rule_to_nraenv_optim.
    Definition rule_to_nnrc_optim : rule -> nnrc := rule_to_nnrc_optim.

    (* Used in CALib: *)
    Definition nraenv_optim_to_nnrc_optim : nraenv -> nnrc := nraenv_optim_to_nnrc_optim.
    Definition nraenv_optim_to_nnrc_optim_to_dnnrc :
      vdbindings -> nraenv -> dnnrc_dataset
      := nraenv_optim_to_nnrc_optim_to_dnnrc.
    Definition nraenv_optim_to_nnrc_optim_to_nnrcmr_comptop_optim : nraenv -> nrcmr
      := nraenv_optim_to_nnrc_optim_to_nnrcmr_comptop_optim.

    (* Used in FrontUtil: *)
    Definition rule_to_nraenv := rule_to_nraenv.
    Definition rule_to_camp := rule_to_camp.
    Definition camp_to_nraenv := camp_to_nraenv.
    Definition oql_to_nraenv := oql_to_nraenv.

    (* Used in DisplayUtil: *)
    Definition nnrcmr_to_nnrcmr_spark_prepare := nnrcmr_to_nnrcmr_spark_prepare.
    Definition nnrcmr_to_nnrcmr_cldmr_prepare := nnrcmr_to_nnrcmr_cldmr_prepare.
    Definition dnnrc_dataset_to_dnnrc_typed_dataset := dnnrc_dataset_to_dnnrc_typed_dataset.

    (* Used in CloudantUtil *)
    Definition cldmr_to_cloudant : string -> list (string*string) -> cldmr -> cloudant := cldmr_to_cloudant.
    Definition nnrcmr_to_cldmr : list (string*string) -> nnrcmr -> cldmr := nnrcmr_to_cldmr.
    Definition nnrcmr_prepared_to_cldmr : list (string*string) -> nnrcmr -> cldmr := nnrcmr_prepared_to_cldmr.

    (* Used in EvalUtil *)
    Definition nraenv_optim := nraenv_optim.
    
    (* Used in queryTests: *)
    Definition rule_to_nraenv_to_nnrc_optim : rule -> nnrc := rule_to_nraenv_to_nnrc_optim.
    Definition rule_to_nraenv_to_nnrc_optim_to_dnnrc :
      vdbindings -> rule -> dnnrc_dataset := rule_to_nraenv_to_nnrc_optim_to_dnnrc.
    Definition rule_to_nraenv_to_nnrc_optim_to_javascript :
      rule -> string := rule_to_nraenv_to_nnrc_optim_to_javascript.
    Definition rule_to_nnrcmr : rule -> nnrcmr := rule_to_nnrcmr.
    Definition rule_to_cldmr : list (string*string) -> rule -> cldmr := rule_to_cldmr.

    (* Stat: Top level *)

    Definition json_stat_of_query : query -> string := json_stat_of_query.
    Definition json_stat_tree_of_query : string -> query -> string := json_stat_tree_of_query.
  End QD.
End QDriver.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
