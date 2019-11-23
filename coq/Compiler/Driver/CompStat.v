(*
 * Copyright 2015-2017 IBM Corporation
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

Require Extraction.
Require Import String.
Require Import ZArith.
Require Import Utils.

(** Query languages *)
Require Import SQLRuntime.
Require Import SQLPPRuntime.
Require Import OQLRuntime.
Require Import LambdaNRARuntime.
(** Rule languages *)
Require Import CAMPRuleRuntime.
Require Import TechRuleRuntime.
Require Import DesignerRuleRuntime.
(** Intermediate languages *)
Require Import NRARuntime.
Require Import NRAEnvRuntime.
Require Import NNRCRuntime.
Require Import NNRSRuntime.
Require Import NNRSimpRuntime.
Require Import ImpRuntime.
Require Import NNRCMRRuntime.
Require Import DNNRCRuntime.
Require Import tDNNRCRuntime.
Require Import CAMPRuntime.
(** Target languages *)
Require Import JavaScriptAstRuntime.
Require Import JavaScriptRuntime.
Require Import JavaRuntime.
Require Import SparkDFRuntime.

Require Import CompilerRuntime.
Require Import CommonSystem.

Require Import ForeignToJavaScript.
Require Import NNRCtoJavaScript.
Require Import OptimizerLogger.
Require Import CompLang.
Require Import CompDriver.

Definition time {A: Type} {B: Type} (compile: A -> B) (q: A) := ("no timing info"%string, compile q).
Extract Inlined Constant time => "(fun f x -> Util.time f x)".

Section CompStat.
  Local Open Scope list_scope.

  Context {ft:foreign_type}.
  Context {fr:foreign_runtime}.
  Context {ftjson:foreign_to_JSON}.
  Context {bm:brand_model}.
  Context {nraenv_core_logger:optimizer_logger string nraenv_core}.
  Context {nraenv_logger:optimizer_logger string nraenv}.
  Context {nnrc_logger:optimizer_logger string nnrc}.
  Context {fredop:foreign_reduce_op}.

  Local Open Scope string_scope.

  (* Stat for an individual query *)
  Context {ftojs:foreign_to_javascript}.

  Definition stat_error (q: string) : data :=
    drec
      (("error_stat", dstring "no stat available")
         :: nil).

  Definition stat_spark_df (q: spark_df) : data :=
    drec
      (("spark_df_stat", dstring "no stat available")
         :: nil).

  Definition stat_java (q: java) : data :=
    drec
      (("java_stat", dstring "no stat available")
         :: nil).

  Definition stat_javascript (q: javascript) : data :=
    drec
      (("javascript_stat", dstring "no stat available")
         :: nil).

  Definition stat_js_ast (q: js_ast) : data :=
    drec
      (("js_ast_stat", dstring "no stat available") (* TODO *)
         :: nil).

  Definition stat_dnnrc_typed (q: dnnrc_typed) : data :=
    drec
      (("dnnrc_typed_stat", dstring "no stat available")
         :: nil).

  Definition stat_dnnrc (q: dnnrc) : data :=
    drec
      (("dnnrc_stat", dstring "no stat available")
         :: nil).

  Definition stat_nnrcmr (q: nnrcmr) : data :=
    drec
      (("nnrcmr_length", dnat (Z_of_nat (List.length q.(mr_chain))))
         :: nil).

  Definition stat_imp_json (q: imp_json) : data :=
    drec
      (("imp_json_size", dnat (Z_of_nat (imp_json_size q)))
         :: nil).

  Definition stat_imp_qcert (q: imp_qcert) : data :=
    drec
      (("imp_qcert_size", dnat (Z_of_nat (imp_qcert_size q)))
         :: nil).

  Definition stat_nnrs_imp (q: nnrs_imp) : data :=
    drec
      (("nnrs_imp_size", dnat (Z_of_nat (nnrs_imp_size q)))
         :: nil).

  Definition stat_nnrs_core (q: nnrs_core) : data :=
    drec
      (("nnrs_core_size", dnat (Z_of_nat (nnrs_core_size q)))
         :: nil).

  Definition stat_nnrs (q: nnrs) : data :=
    drec
      (("nnrs_size", dnat (Z_of_nat (nnrs_size q)))
         :: nil).

  Definition stat_nnrc_core (q: nnrc_core) : data :=
    drec
      (("nnrc_core_size", dnat (Z_of_nat (lift_nnrc_core nnrc_size q)))
         :: nil).

  Definition stat_nnrc (q: nnrc) : data :=
    drec
      (("nnrc_size", dnat (Z_of_nat (nnrc_size q)))
         :: nil).

  Definition stat_nra (q:nra) : data :=
    drec
      (("nra_size", dnat (Z_of_nat (nra_size q)))
         :: ("nra_depth", dnat (Z_of_nat (nra_depth q)))
         :: nil).

  Definition stat_nraenv_core (q:nraenv_core) : data :=
    drec
      (("nraenv_core_size", dnat (Z_of_nat (nraenv_core_size q)))
         :: ("nraenv_core_depth", dnat (Z_of_nat (nraenv_core_depth q)))
         :: nil).

  Definition stat_nraenv (q:nraenv) : data :=
    drec
      (("nraenv_size", dnat (Z_of_nat (nraenv_size q)))
         :: ("nraenv_depth", dnat (Z_of_nat (nraenv_depth q)))
         :: nil).

  Definition stat_camp (q:camp) : data :=
    drec
      (("camp_size", dnat (Z_of_nat (camp_size q)))
         :: nil).

  Definition stat_camp_rule (q:camp_rule) : data :=
    drec
      (("rule_size", dnat (Z_of_nat (camp_size (camp_rule_to_camp q))))
         :: nil).

  Definition stat_tech_rule (q:tech_rule) : data :=
    drec
      (("tech_rule_stat", dstring "no stat available")
         :: nil).

  Definition stat_designer_rule (q:designer_rule) : data :=
    drec
      (("tech_designer_stat", dstring "no stat available")
         :: nil).

  Definition stat_oql (q:oql) : data :=
    drec
      (("oql_size", dnat (Z_of_nat (oql_size q)))
         :: nil).

  Definition stat_sql (q:sql) : data :=
    drec
      (("sql_size", dnat (Z_of_nat (sql_size q)))
         :: ("sql_depth", dnat (Z_of_nat (sql_depth q)))
         :: nil).

  Definition stat_sqlpp (q:sqlpp) : data :=
    drec
      (("sqlpp_size", dnat (Z_of_nat (sqlpp_size q)))
         :: ("sqlpp_depth", dnat (Z_of_nat (sqlpp_depth q)))
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

  Definition stat_tree_spark_df (q: spark_df) : data :=
    drec
      (("spark_df", stat_spark_df q)
         :: nil).

  Definition stat_tree_java (q: java) : data :=
    drec
      (("java", stat_java q)
         :: nil).

  Definition stat_tree_js_ast (q: js_ast) : data :=
    drec
      (("js_ast", stat_js_ast q)
         :: nil).

  Definition stat_tree_javascript (q: javascript) : data :=
    drec
      (("javascript", stat_javascript q)
         :: nil).

  Definition stat_tree_dnnrc_typed (q: dnnrc_typed) : data :=
    drec
      (("dnnrc_typed", stat_dnnrc_typed q)
         :: nil).

  Definition stat_tree_dnnrc (q: dnnrc) : data :=
    drec
      (("dnnrc", stat_dnnrc q)
         :: nil).

  Definition stat_tree_nnrcmr (q: nnrcmr) : data :=
    let (t, q') := time nnrcmr_optim q in
    drec
      (("nnrcmr_no_optim", stat_nnrcmr q)
         :: ("nnrcmr_optim", stat_nnrcmr q')
         :: ("nnrcmr_optim_time", dstring t)
         :: nil).

  Definition stat_tree_imp_json (q: imp_json) : data :=
    drec
      (("imp_json", stat_imp_json q)
         :: nil).

  Definition stat_tree_imp_qcert (q: imp_qcert) : data :=
    drec
      (("imp_qcert", stat_imp_qcert q)
         :: nil).

  Definition stat_tree_nnrs_imp (q: nnrs_imp) : data :=
    drec
      (("nnrs_imp", stat_nnrs_imp q)
         :: nil).

  Definition stat_tree_nnrs_core (q: nnrs_core) : data :=
    drec
      (("nnrs_core", stat_nnrs_core q)
         :: nil).

  Definition stat_tree_nnrs (q: nnrs) : data :=
    drec
      (("nnrs", stat_nnrs q)
         :: nil).

  Definition stat_tree_nnrc_core (q: nnrc_core) : data :=
    drec
      (("nnrc_core", stat_nnrc_core q)
         :: nil).

  Definition stat_tree_nnrc (q: nnrc) : data :=
    let (t, q') := time nnrc_optim_default q in
    drec
      (("nnrc_no_optim", stat_nnrc q)
         :: ("nnrc_optim", stat_nnrc q')
         :: ("nnrc_optim_time", dstring t)
         :: nil).

  Definition stat_tree_body_nra (q:nra) : data :=
    match stat_nra q with
    | drec l =>
      let (t, q') := time nra_to_nnrc_core q in
      drec (l ++ ("nra_to_nnrc_core", stat_tree_nnrc_core q')
              :: ("nra_to_nnrc_core_time", dstring t)
              :: nil)
    | s => s
    end.

  Definition stat_tree_nra (q:nra) : data :=
    drec
      (("nra", stat_tree_body_nra q)
         :: nil).

  Definition stat_tree_body_nraenv_core (q:nraenv_core) : data :=
    match stat_nraenv_core q with
    | drec l =>
      let (t_nnrc, q_nnrc) := time nraenv_core_to_nnrc_core q in
      let (t_nra, q_nra) := time nraenv_core_to_nra q in
      drec (l ++ ("nraenv_core_to_nnrc_core", stat_tree_nnrc_core q_nnrc)
              :: ("nraenv_core_to_nnrc_core_time", dstring t_nnrc)
              :: ("nraenv_core_to_nra", stat_tree_nra q_nra)
              :: ("nraenv_core_to_nra_time", dstring t_nra)
              :: nil)
    | s => s
    end.

  Definition stat_tree_nraenv_core (q:nraenv_core) : data :=
    drec
      (("nraenv_core_no_optim", stat_tree_body_nraenv_core q)
         :: nil).

  Definition stat_tree_body_nraenv (q:nraenv) : data :=
    match stat_nraenv q with
    | drec l =>
      let (t_nraenv_core, q_nraenv_core) := time nraenv_to_nraenv_core q in
      let (t_nnrc, q_nnrc) := time nraenv_to_nnrc q in
      drec (l ++ ("nraenv_to_nnrc", stat_tree_nnrc q_nnrc)
              :: ("nraenv_to_nnrc_time", dstring t_nnrc)
              :: ("nraenv_to_nraenv_core", stat_tree_nraenv_core q_nraenv_core)
              :: nil)
    | s => s
    end.

  Definition stat_tree_nraenv (q:nraenv) : data :=
    let (t, q') := time nraenv_optim_default q in
    drec
      (("nraenv_no_optim", stat_tree_body_nraenv q)
         :: ("nraenv_optim", stat_tree_body_nraenv q')
         :: ("nraenv_optim_time", dstring t)
         :: nil).

  Definition stat_tree_camp (q:camp) : data :=
    match stat_camp q with
    | drec l =>
      let (t_nraenv, q_nraenv) := time camp_to_nraenv q in
      let (t_nraenv_core, q_nraenv_core) := time camp_to_nraenv_core q in
      let (t_nra, q_nra) := time camp_to_nra q in
      drec (l ++ ("camp_to_nraenv", stat_tree_nraenv q_nraenv)
              :: ("camp_to_nraenv_time", dstring t_nraenv)
              :: ("camp_to_nraenv_core", stat_tree_nraenv_core q_nraenv_core)
              :: ("camp_to_nraenv_core_time", dstring t_nraenv_core)
              :: ("camp_to_nra", stat_tree_nra q_nra)
              :: ("camp_to_nra_time", dstring t_nra)
              :: nil)
    | s => s
    end.

  Definition stat_tree_camp_rule (q:camp_rule) : data :=
    match stat_camp_rule q with
    | drec l =>
      let (t_camp, q_camp) := time camp_rule_to_camp q in
      drec (l ++ ("camp_rule_to_camp", stat_tree_camp q_camp)
              :: ("camp_rule_to_camp", dstring t_camp)
              :: nil)
    | s => s
    end.

  Definition stat_tree_tech_rule (q:tech_rule) : data :=
    match stat_tech_rule q with
    | drec l =>
      let (t_camp_rule, q_camp_rule) := time tech_rule_to_camp_rule q in
      drec (l ++ ("tech_rule_to_camp_rule", stat_tree_camp_rule q_camp_rule)
              :: ("tech_rule_to_camp_rule", dstring t_camp_rule)
              :: nil)
    | s => s
    end.

  Definition stat_tree_designer_rule (q:designer_rule) : data :=
    match stat_designer_rule q with
    | drec l =>
      let (t_camp_rule, q_camp_rule) := time designer_rule_to_camp_rule q in
      drec (l ++ ("designer_rule_to_camp_rule", stat_tree_camp_rule q_camp_rule)
              :: ("designer_rule_to_camp_rule", dstring t_camp_rule)
              :: nil)
    | s => s
    end.

  Definition stat_tree_oql (q:oql) : data :=
    match stat_oql q with
    | drec l =>
      let (t_nraenv, q_nraenv) := time oql_to_nraenv q in
      drec (l ++ ("oql_to_nraenv", stat_tree_nraenv q_nraenv)
              :: ("oql_to_nraenv_time", dstring t_nraenv)
              :: nil)
    | s => s
    end.

  Definition stat_tree_sql (q:sql) : data :=
    match stat_sql q with
    | drec l =>
      let (t_nraenv, q_nraenv) := time sql_to_nraenv q in
      drec (l ++ ("sql_to_nraenv", stat_tree_nraenv q_nraenv)
              :: ("sql_to_nraenv_time", dstring t_nraenv)
              :: nil)
    | s => s
    end.

  Definition stat_tree_sqlpp (q:sqlpp) : data :=
    match stat_sqlpp q with
    | drec l =>
      let (t_nraenv, q_nraenv) := time sqlpp_to_nraenv q in
      drec (l ++ ("sqlpp_to_nraenv", stat_tree_nraenv q_nraenv)
              :: ("sqlpp_to_nraenv_time", dstring t_nraenv)
              :: nil)
    | s => s
    end.

  Definition stat_tree_lambda_nra (q:lambda_nra) : data :=
    match stat_lambda_nra q with
    | drec l =>
      let (t_nraenv, q_nraenv) := time lambda_nra_to_nraenv q in
      drec (l ++ ("lambda_nra_to_nraenv", stat_tree_nraenv q_nraenv)
              :: ("lambda_nra_to_nraenv_time", dstring t_nraenv)
              :: nil)
    | s => s
    end.

  (* Top level *)

  Definition json_stat_of_query (q:query) : string :=
    let stat :=
        match q with
        | Q_camp_rule q => stat_camp_rule q
        | Q_tech_rule q => stat_tech_rule q
        | Q_designer_rule q => stat_designer_rule q
        | Q_camp q => stat_camp q
        | Q_oql q => stat_oql q
        | Q_sql q => stat_sql q
        | Q_sqlpp q => stat_sqlpp q
        | Q_lambda_nra q => stat_lambda_nra q
        | Q_nra q => stat_nra q
        | Q_nraenv_core q => stat_nraenv_core q
        | Q_nraenv q => stat_nraenv q
        | Q_nnrc_core q => stat_nnrc_core q
        | Q_nnrc q => stat_nnrc q
        | Q_nnrs_core q => stat_nnrs_core q
        | Q_nnrs q => stat_nnrs q
        | Q_nnrs_imp q => stat_nnrs_imp q
        | Q_imp_qcert q => stat_imp_qcert q
        | Q_imp_json q => stat_imp_json q
        | Q_nnrcmr q => stat_nnrcmr q
        | Q_dnnrc q => stat_dnnrc q
        | Q_dnnrc_typed q => stat_dnnrc_typed q
        | Q_js_ast q => stat_js_ast q
        | Q_javascript q => stat_javascript q
        | Q_java q => stat_java q
        | Q_spark_df q => stat_spark_df q
        | Q_error q => stat_error q
        end
    in
    dataToJS quotel_double stat.

  Definition json_stat_tree_of_query (qname:string) (q:query) : string :=
    let stat :=
        match q with
        | Q_camp_rule q => stat_tree_camp_rule q
        | Q_tech_rule q => stat_tree_tech_rule q
        | Q_designer_rule q => stat_tree_designer_rule q
        | Q_camp q => stat_tree_camp q
        | Q_oql q => stat_tree_oql q
        | Q_sql q => stat_tree_sql q
        | Q_sqlpp q => stat_tree_sqlpp q
        | Q_lambda_nra q => stat_tree_lambda_nra q
        | Q_nra q => stat_tree_nra q
        | Q_nraenv_core q => stat_tree_nraenv_core q
        | Q_nraenv q => stat_tree_nraenv q
        | Q_nnrc_core q => stat_tree_nnrc_core q
        | Q_nnrc q => stat_tree_nnrc q
        | Q_nnrs_core q => stat_tree_nnrs_core q
        | Q_nnrs q => stat_tree_nnrs q
        | Q_nnrs_imp q => stat_tree_nnrs_imp q
        | Q_imp_qcert q => stat_tree_imp_qcert q
        | Q_imp_json q => stat_tree_imp_json q
        | Q_nnrcmr q => stat_tree_nnrcmr q
        | Q_dnnrc q => stat_tree_dnnrc q
        | Q_dnnrc_typed q => stat_tree_dnnrc_typed q
        | Q_js_ast q => stat_tree_js_ast q
        | Q_javascript q => stat_tree_javascript q
        | Q_java q => stat_tree_java q
        | Q_spark_df q => stat_tree_spark_df q
        | Q_error q => stat_tree_error q
        end
    in
    dataToJS quotel_double
             (drec
                (("name", dstring qname)
                   :: ("stats", stat)
                   :: nil)).

End CompStat.

