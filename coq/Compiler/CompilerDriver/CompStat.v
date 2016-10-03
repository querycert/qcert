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

Section CompStat.

  Require Import String.
  Require Import NRARuntime.
  Require Import NRAEnvRuntime.
  Require Import NNRCRuntime.
  Require Import NNRCMRRuntime.
  Require Import CloudantMR.
  Require Import DNNRC Dataset.
  Require Import CAMPRuntime.
  Require Import ODMGRuntime.

  Require Import CompilerRuntime.
  Require Import BasicSystem.

  Require Import NNRCtoJavascript.
  
  Require Import OptimizerLogger.

  Require Import CompLang CompDriver.

  Local Open Scope list_scope.

  Require Import  ForeignCloudant.
  Context {ft:foreign_type}.
  Context {fr:foreign_runtime}.
  Context {bm:brand_model}.
  Context {nraenv_logger:optimizer_logger string algenv}.
  Context {nnrc_logger:optimizer_logger string nrc}.
  Context {fredop:foreign_reduce_op}.

  Require Import ZArith.
  Local Open Scope string_scope.

  (* Stat for an individual query *)

  Require Import ForeignToJavascript.
  Context {ftojs:foreign_to_javascript}.

  Definition stat_error (q: string) : data :=
    drec
      (("error_stat", dstring "no stat available")
         :: nil).

  Definition stat_cloudant (q: cloudant) : data :=
    drec
      (("cloudant_stat", dstring "no stat available")
         :: nil).

  Definition stat_spark2 (q: spark2) : data :=
    drec
      (("spark2_stat", dstring "no stat available")
         :: nil).

  Definition stat_spark (q: spark) : data :=
    drec
      (("spark_stat", dstring "no stat available")
         :: nil).

  Definition stat_java (q: java) : data :=
    drec
      (("java_stat", dstring "no stat available")
         :: nil).

  Definition stat_javascript (q: javascript) : data :=
    drec
      (("javascript_stat", dstring "no stat available")
         :: nil).

  Definition stat_dnnrc_typed_dataset (q: dnnrc_typed_dataset) : data :=
    drec
      (("dnnrc_typed_dataset_stat", dstring "no stat available")
         :: nil).

  Definition stat_dnnrc_dataset (q: dnnrc_dataset) : data :=
    drec
      (("dnnrc_dataset_stat", dstring "no stat available")
         :: nil).

  Definition stat_cldmr (q: cldmr) : data :=
    drec
      (("cldmr_stat", dstring "no stat available")
         :: nil).

  Definition stat_nnrcmr (q: nnrcmr) : data :=
    drec
      (("nnrcmr_length", dnat (Z_of_nat (List.length q.(mr_chain))))
         :: nil).

  Definition stat_nnrc (q: nnrc) : data :=
    drec
      (("nnrc_size", dnat (Z_of_nat (nrc_size q)))
         :: nil).

  Definition stat_nra (q:nra) : data :=
    drec
      (("nra_size", dnat (Z_of_nat (alg_size q)))
         :: ("nra_depth", dnat (Z_of_nat (alg_depth q)))
         :: nil).

  Definition stat_nraenv (q:nraenv) : data :=
    drec
      (("nraenv_size", dnat (Z_of_nat (algenv_size q)))
         :: ("nraenv_depth", dnat (Z_of_nat (algenv_depth q)))
         :: nil).

  Definition stat_camp (q:camp) : data :=
    drec
      (("camp_size", dnat (Z_of_nat (pat_size q)))
         :: nil).

  Definition stat_rule (q:rule) : data :=
    drec
      (("rule_size", dnat (Z_of_nat (pat_size (rule_to_camp q))))
         :: nil).

  Definition stat_oql (q:oql) : data :=
    drec
      (("oql_size", dnat (Z_of_nat (oql_size q)))
         :: nil).

  Definition stat_lambda_nra (q: lambda_nra) : data :=
    drec
      (("lambda_nra_stat", dstring "no stat available")
         :: nil).

  (* Build the tree of all stats *)
  
  Definition stat_tree_error (q: string) : data :=
    drec
      (("error", stat_error q)
         :: nil).

  Definition stat_tree_cloudant (q: cloudant) : data :=
    drec
      (("cloudant", stat_cloudant q)
         :: nil).

  Definition stat_tree_spark2 (q: spark2) : data :=
    drec
      (("spark2", stat_spark2 q)
         :: nil).

  Definition stat_tree_spark (q: spark) : data :=
    drec
      (("spark", stat_spark q)
         :: nil).

  Definition stat_tree_java (q: java) : data :=
    drec
      (("java", stat_java q)
         :: nil).

  Definition stat_tree_javascript (q: javascript) : data :=
    drec
      (("javascript", stat_javascript q)
         :: nil).

  Definition stat_tree_dnnrc_typed_dataset (q: dnnrc_typed_dataset) : data :=
    drec
      (("dnnrc_typed_dataset", stat_dnnrc_typed_dataset q)
         :: nil).

  Definition stat_tree_dnnrc_dataset (q: dnnrc_dataset) : data :=
    drec
      (("dnnrc_dataset", stat_dnnrc_dataset q)
         :: nil).

  Definition stat_tree_cldmr (q: cldmr) : data :=
    drec
      (("cldmr", stat_cldmr q)
         :: nil).

  Definition stat_tree_nnrcmr (q: nnrcmr) : data :=
    drec
      (("nnrcmr_no_optim", stat_nnrcmr q)
         :: ("nnrcmr_optim", stat_nnrcmr (nnrcmr_optim q))
         :: nil).

  Definition stat_tree_nnrc (q: nnrc) : data :=
    drec
      (("nnrc_no_optim", stat_nnrc q)
         :: ("nnrc_optim", stat_nnrc (nnrc_optim q))
         :: nil).

  Definition stat_tree_body_nra (q:nra) : data :=
    match stat_nra q with
    | drec l =>
      drec (l ++ ("nra_to_nnrc", stat_tree_nnrc (nra_to_nnrc q))
              :: nil)
    | s => s
    end.

  Definition stat_tree_nra (q:nra) : data :=
    drec
      (("nra_no_optim", stat_tree_body_nra q)
         :: ("nra_optim", stat_tree_body_nra (nra_optim q))
         :: nil).

  Definition stat_tree_body_nraenv (q:nraenv) : data :=
    match stat_nraenv q with
    | drec l =>
      drec (l ++ ("nraenv_to_nnrc", stat_tree_nnrc (nraenv_to_nnrc q))
              :: ("nraenv_to_nra", stat_tree_nra (nraenv_to_nra q))
              :: nil)
    | s => s
    end.

  Definition stat_tree_nraenv (q:nraenv) : data :=
    drec
      (("nraenv_no_optim", stat_tree_body_nraenv q)
         :: ("nraenv_optim", stat_tree_body_nraenv (nraenv_optim q))
         :: ("nraenv_compiler", stat_tree_nnrc (nraenv_optim_to_nnrc q))
         :: nil).

  Definition stat_tree_camp (q:camp) : data :=
    match stat_camp q with
    | drec l =>
      drec (l ++ ("camp_to_nraenv", stat_tree_nraenv (camp_to_nraenv q))
              :: ("camp_to_nra", stat_tree_nra (camp_to_nra q))
              :: nil)
    | s => s
    end.

  Definition stat_tree_rule (q:rule) : data :=
    match stat_rule q with
    | drec l =>
      drec (l ++ ("rule_to_nraenv", stat_tree_nraenv (rule_to_nraenv q))
              :: ("rule_to_nra", stat_tree_nra (rule_to_nra q))
              :: nil)
    | s => s
    end.

  Definition stat_tree_oql (q:oql) : data :=
    match stat_oql q with
    | drec l =>
      drec (l ++ ("oql_to_nraenv", stat_tree_nraenv (oql_to_nraenv q))
              :: nil)
    | s => s
    end.

  Definition stat_tree_lambda_nra (q:lambda_nra) : data :=
    match stat_lambda_nra q with
    | drec l =>
      drec (l ++ ("lambda_nra_to_nraenv", stat_tree_nraenv (lambda_nra_to_nraenv q))
              :: nil)
    | s => s
    end.

  (* Top level *)

  Definition json_stat_of_query (q:query) : string :=
    let stat :=
        match q with
        | Q_rule q => stat_rule q
        | Q_camp q => stat_camp q
        | Q_oql q => stat_oql q
        | Q_lambda_nra q => stat_lambda_nra q
        | Q_nra q => stat_nra q
        | Q_nraenv q => stat_nraenv q
        | Q_nnrc q => stat_nnrc q
        | Q_nnrcmr q => stat_nnrcmr q
        | Q_cldmr q => stat_cldmr q
        | Q_dnnrc_dataset q => stat_dnnrc_dataset q
        | Q_dnnrc_typed_dataset q => stat_dnnrc_typed_dataset q
        | Q_javascript q => stat_javascript q
        | Q_java q => stat_java q
        | Q_spark q => stat_spark q
        | Q_spark2 q => stat_spark2 q
        | Q_cloudant q => stat_cloudant q
        | Q_error q => stat_error q
        end
    in
    dataToJS quotel_double stat.

  Definition json_stat_tree_of_query (qname:string) (q:query) : string :=
    let stat :=
        match q with
        | Q_rule q => stat_tree_rule q
        | Q_camp q => stat_tree_camp q
        | Q_oql q => stat_tree_oql q
        | Q_lambda_nra q => stat_tree_lambda_nra q
        | Q_nra q => stat_tree_nra q
        | Q_nraenv q => stat_tree_nraenv q
        | Q_nnrc q => stat_tree_nnrc q
        | Q_nnrcmr q => stat_tree_nnrcmr q
        | Q_cldmr q => stat_tree_cldmr q
        | Q_dnnrc_dataset q => stat_tree_dnnrc_dataset q
        | Q_dnnrc_typed_dataset q => stat_tree_dnnrc_typed_dataset q
        | Q_javascript q => stat_tree_javascript q
        | Q_java q => stat_tree_java q
        | Q_spark q => stat_tree_spark q
        | Q_spark2 q => stat_tree_spark2 q
        | Q_cloudant q => stat_tree_cloudant q
        | Q_error q => stat_tree_error q
        end
    in
    dataToJS quotel_double
             (drec
                (("name", dstring qname)
                   :: ("stats", stat)
                   :: nil)).

End CompStat.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
