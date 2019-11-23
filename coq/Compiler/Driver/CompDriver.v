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

Require Import String.
Require Import List.
Require Import Morphisms.

(* Common libraries *)
Require Import Utils.
Require Import CommonSystem.
Require Import TypingRuntime.

(* Query languages *)
Require Import SQLRuntime.
Require Import SQLPPRuntime.
Require Import OQLRuntime.
Require Import LambdaNRARuntime.
(* Rule languages *)
Require Import CAMPRuleRuntime.
Require Import TechRuleRuntime.
Require Import DesignerRuleRuntime.
(* Intermediate languages *)
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
(* Target languages *)
Require Import JavaScriptAstRuntime.
Require Import JavaScriptRuntime.
Require Import JavaRuntime.
Require Import SparkRDDRuntime.
Require Import SparkDFRuntime.

(* Translations *)
Require Import OQLtoNRAEnv.
Require Import SQLtoNRAEnv.
Require Import SQLPPtoNRAEnv.
Require Import LambdaNRAtoNRAEnv.
Require Import CAMPRuletoCAMP.
Require Import TechRuletoCAMPRule.
Require Import DesignerRuletoCAMPRule.
Require Import CAMPtoNRA.
Require Import CAMPtocNRAEnv.
Require Import CAMPtoNRAEnv.
Require Import NRAtocNNRC.
Require Import cNRAEnvtocNNRC.
Require Import NRAEnvtoNNRC.
Require Import cNRAEnvtoNRA.
Require Import cNRAEnvtoNRAEnv.
Require Import NRAEnvtocNRAEnv.
Require Import NRAtocNRAEnv.
Require Import NNRCtocNNRC.
Require Import NNRCtoNNRS.
Require Import NNRStoNNRSimp.
Require Import NNRSimptoJavaScriptAst.
Require Import NNRSimptoImpQcert.
Require Import ImpQcerttoImpJson.
Require Import ImpJsontoJavaScriptAst.
Require Import JavaScriptAsttoJavaScript.
Require Import NNRCtoDNNRC.
Require Import NNRCtoNNRCMR.
Require Import NNRCtoJavaScript.
Require Import NNRCtoJava.
Require Import cNNRCtoCAMP.
Require Import cNNRCtoNNRC.
Require Import NNRCMRtoNNRC.
Require Import NNRCMRtoSparkRDD.
Require Import NNRCMRtoDNNRC.
Require Import DNNRCtotDNNRC.
Require Import tDNNRCtoSparkDF.

(* Optimizers *)
Require Import NRAEnvOptim.
Require Import NNRCOptim.
Require Import NNRCMROptim.
Require Import tDNNRCOptim.
Require Import NNRSimpOptim.
(* Require Import ImpOptim. *)
Require Import OptimizerLogger.

(* Foreign Datatypes Support *)
Require Import ForeignToReduceOps.
Require Import ForeignToSpark.
Require Import ForeignToJava.
Require Import ForeignToJavaScript.
Require Import ForeignToJavaScriptAst.
Require Import ForeignToScala.

(** Compiler Driver *)
Require Import CompLang.
Require Import CompEnv.
Require Import CompConfig.

Section CompDriver.
  (* Some useful notations *)
  Local Open Scope list_scope.

  (* Context *)
  Context {ft:foreign_type}.
  Context {fr:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {ftoredop:foreign_to_reduce_op}.
  Context {bm:brand_model}.
  Context {ftyping: foreign_typing}.
  Context {nraenv_logger:optimizer_logger string nraenv}.
  Context {nnrc_logger:optimizer_logger string nnrc}.
  Context {nnrs_imp_expr_logger:optimizer_logger string nnrs_imp_expr}.
  Context {nnrs_imp_stmt_logger:optimizer_logger string nnrs_imp_stmt}.
  Context {nnrs_imp_logger:optimizer_logger string nnrs_imp}.
  Context {dnnrc_logger:optimizer_logger string (DNNRCBase.dnnrc_base fr (type_annotation unit) dataframe)}.
  Context {ftojs:foreign_to_javascript}.
  Context {ftoajs:foreign_to_ajavascript}.
  Context {ftojava:foreign_to_java}.
  Context {ftos:foreign_to_scala}.
  Context {ftospark:foreign_to_spark}.
  Context {ftjson:foreign_to_JSON}.

  Section translations.
    Import ListNotations.

    (** Source languages translations *)
    Definition oql_to_nraenv (q:oql) : nraenv :=
      OQLtoNRAEnv.oql_to_nraenv_top q.

    Definition sql_to_nraenv (q:sql) : nraenv :=
      SQLtoNRAEnv.sql_to_nraenv_top q.
    
    Definition sqlpp_to_nraenv (q:sqlpp) : nraenv := SQLPPtoNRAEnv.sqlpp_to_nraenv_top q.

    Definition lambda_nra_to_nraenv (q:lambda_nra) : nraenv :=
      LambdaNRAtoNRAEnv.lambda_nra_to_nraenv_top q.

    (** Rules and CAMP translations *)
    Definition camp_rule_to_camp (q:camp_rule) : camp :=
      CAMPRuletoCAMP.camp_rule_to_camp_top q.

    Definition tech_rule_to_camp_rule (q:tech_rule) : camp_rule :=
      TechRuletoCAMPRule.tech_rule_to_camp_rule_top q.

    Definition designer_rule_to_camp_rule (q:designer_rule) : camp_rule :=
      DesignerRuletoCAMPRule.designer_rule_to_camp_rule_top q.

    Definition camp_to_nra (q:camp) : nra :=
      CAMPtoNRA.camp_to_nra_top q.

    Definition camp_to_nraenv_core (q:camp) : nraenv_core :=
      CAMPtocNRAEnv.camp_to_nraenv_core_top q.

    Definition camp_to_nraenv (q:camp) : nraenv :=
      CAMPtoNRAEnv.camp_to_nraenv_top q.

    (** NRA/NRAEnv translations *)
    Definition nra_to_nraenv_core (q: nra) : nraenv_core :=
      NRAtocNRAEnv.nra_to_nraenv_core_top q.

    Definition nra_to_nnrc_core (q: nra) : nnrc_core :=
      NRAtocNNRC.nra_to_nnrc_core_top q.

    Definition nraenv_core_to_nnrc_core (q: nraenv_core) : nnrc_core :=
      cNRAEnvtocNNRC.nraenv_core_to_nnrc_core_top q.

    Definition nraenv_core_to_nra (q: nraenv_core) : nra :=
      cNRAEnvtoNRA.nraenv_core_to_nra_top q.

    Definition nraenv_core_to_nraenv (q: nraenv_core) : nraenv :=
      cNRAEnvtoNRAEnv.nraenv_core_to_nraenv_top q.

    Definition nraenv_to_nraenv_core (q: nraenv) : nraenv_core :=
      NRAEnvtocNRAEnv.nraenv_to_nraenv_core_top q.

    Definition nraenv_to_nnrc (q: nraenv) : nnrc :=
      NRAEnvtoNNRC.nraenv_to_nnrc_top q.

    (** NNRC translations *)
    Definition nnrc_to_nnrc_core (q:nnrc) : nnrc_core :=
      NNRCtocNNRC.nnrc_to_nnrc_core_top q.

    Definition nnrc_core_to_nnrc (q: nnrc_core) : nnrc :=
      cNNRCtoNNRC.nnrc_core_to_nnrc_top q. (* XXX avoid ? XXX *)

    Definition nnrc_core_to_camp (avoid: list var) (q: nnrc_core) : camp :=
      lift_nnrc_core (nnrcToCamp_let avoid) q. (* XXX avoid ? XXX *)

    (* Free variables should eventually be passed from the application. *)
    Definition nnrc_core_to_nnrs_core (inputs: list var) (q: nnrc_core) : nnrs_core :=
      nnrc_core_to_nnrs_core_top inputs q.

    (* Free variables should eventually be passed from the application. *)
    Definition nnrc_to_nnrs (inputs: list var) (q: nnrc) : nnrs :=
      nnrc_to_nnrs_top inputs q.

    Definition nnrs_to_nnrs_imp (q: nnrs) : nnrs_imp :=
      nnrs_to_nnrs_imp_top "$"%string q.

    Definition nnrs_imp_to_js_ast (inputs: list var) (q: nnrs_imp) : js_ast :=
      [ (nnrs_imp_to_js_ast_top inputs q) ].

    Definition nnrs_imp_to_imp_qcert (qname: string) (q: nnrs_imp) : imp_qcert :=
      nnrs_imp_to_imp_qcert_top qname q.

    Definition imp_qcert_to_imp_json (q: imp_qcert) : imp_json :=
      imp_qcert_to_imp_json q.

    Definition imp_json_to_js_ast (q: imp_json) : js_ast :=
      imp_json_to_js_ast q.

    Definition js_ast_to_javascript (q: js_ast) : javascript :=
      List.fold_left (fun acc q => String.append acc (js_ast_to_js_top q)) q  ""%string.

    (* Java equivalent: NnrcToNnrcmr.convert *)
    (* Free variables should eventually be passed from the application. *)
    Definition nnrc_to_nnrcmr (vinit: var) (inputs_loc: vdbindings) (q: nnrc) : nnrcmr :=
      nnrc_to_nnrcmr_top vinit inputs_loc q.

    Definition nnrc_to_dnnrc (inputs_loc: vdbindings) (q: nnrc) : dnnrc :=
      nnrc_to_dnnrc_top inputs_loc q.

    Definition nnrc_to_javascript (q: nnrc) : javascript := (* XXX Expands GroupBy For now XXX *)
      lift_nnrc_core nnrc_to_js_top (nnrc_to_nnrc_core q).

    Definition nnrc_to_java (class_name:string) (imports:string) (q: nnrc) : java := (* XXX Expands GroupBy For now XXX *)
      lift_nnrc_core (nnrc_to_java_top class_name imports) (nnrc_to_nnrc_core q).

    (** NNRCMR translations *)
    Definition nnrcmr_to_nnrc (q: nnrcmr) : option nnrc := nnrc_of_nnrcmr_top q.

    Definition nnrcmr_to_dnnrc (q: nnrcmr) : option dnnrc := dnnrc_base_of_nnrcmr_top tt q.

    Definition nnrcmr_to_spark_rdd (queryname: string) (q: nnrcmr) : spark_rdd :=
      nnrcmr_to_spark_rdd_top init_vinit queryname q. (* XXX init_vinit should be a parameter? *)

    (** DNNRC translations *)

    Definition dnnrc_to_dnnrc_typed (q: dnnrc) (tdenv: tdbindings)
      : option dnnrc_typed :=
      dnnrc_to_dnnrc_typed_top tdenv q.

    Definition dnnrc_typed_to_spark_df
               (tenv:tdbindings) (name:string) (q:dnnrc_typed) : spark_df :=
      @dnnrc_typed_to_spark_df_top _ _ bm _ unit tenv name q.

  End translations.

  (** Optimization functions *)
  Section optimizations.
    Definition nraenv_optim (opc:optim_phases_config) (q: nraenv) : nraenv
      := NRAEnvOptimizer.run_nraenv_optims opc q.
    Definition nraenv_optim_default (q: nraenv) : nraenv
      := nraenv_optim default_nraenv_optim_phases q.

    Definition nnrc_optim (opc:optim_phases_config) (q: nnrc) : nnrc
      := run_nnrc_optims opc q.
    Definition nnrc_optim_default (q:nnrc) : nnrc
      := nnrc_optim (get_default_optim_config L_nnrc) q.

    Definition nnrs_imp_optim (opc:optim_phases3_config) (q: nnrs_imp) : nnrs_imp
      := run_nnrs_imp_optims opc q.

    Definition nnrs_imp_optim_default (q:nnrs_imp) : nnrs_imp
      := run_nnrs_imp_optims (get_default_optim_config L_nnrs_imp) q.

    Definition nnrcmr_optim (q: nnrcmr) : nnrcmr
      := run_nnrcmr_optims q.

    Definition dnnrc_typed_optim (q:dnnrc_typed) : dnnrc_typed
      := dnnrcToDataframeRewrite q.
  End optimizations.

  (** Drivers *)

  Inductive javascript_driver : Set :=
    | Dv_javascript_stop : javascript_driver.

  Inductive js_ast_driver : Set :=
    | Dv_js_ast_stop : js_ast_driver
    | Dv_js_ast_to_javascript : javascript_driver -> js_ast_driver.

  Inductive java_driver : Set :=
    | Dv_java_stop : java_driver.

  Inductive spark_rdd_driver : Set :=
    | Dv_spark_rdd_stop : spark_rdd_driver.

  Inductive spark_df_driver : Set :=
    | Dv_spark_df_stop : spark_df_driver.

  Inductive dnnrc_typed_driver : Set :=
    | Dv_dnnrc_typed_stop : dnnrc_typed_driver
    | Dv_dnnrc_typed_optim : dnnrc_typed_driver -> dnnrc_typed_driver
    | Dv_dnnrc_typed_to_spark_df : tdbindings -> string -> spark_df_driver -> dnnrc_typed_driver
  .

  Inductive dnnrc_driver : Set :=
    | Dv_dnnrc_stop : dnnrc_driver
    | Dv_dnnrc_to_dnnrc_typed : tdbindings -> dnnrc_typed_driver -> dnnrc_driver
  .

  Inductive imp_json_driver : Set :=
    | Dv_imp_json_stop : imp_json_driver
    | Dv_imp_json_to_js_ast : js_ast_driver -> imp_json_driver
  .

  Inductive imp_qcert_driver : Set :=
    | Dv_imp_qcert_stop : imp_qcert_driver
    | Dv_imp_qcert_to_imp_json : imp_json_driver -> imp_qcert_driver
  .

  Inductive nnrs_imp_driver : Set :=
    | Dv_nnrs_imp_stop : nnrs_imp_driver
    | Dv_nnrs_imp_optim : optim_phases3_config -> nnrs_imp_driver -> nnrs_imp_driver
    | Dv_nnrs_imp_to_js_ast : (* inputs *) list var -> js_ast_driver -> nnrs_imp_driver
    | Dv_nnrs_imp_to_imp_qcert : (* query name*) string -> imp_qcert_driver -> nnrs_imp_driver
  .

  Inductive nnrs_driver : Set :=
    | Dv_nnrs_stop : nnrs_driver
    | Dv_nnrs_to_nnrs_imp : nnrs_imp_driver -> nnrs_driver
  .

  Inductive nnrs_core_driver : Set :=
  | Dv_nnrs_core_stop : nnrs_core_driver
  | Dv_nnrs_core_to_nnrs : nnrs_driver -> nnrs_core_driver
  .

  (* Unset Elimination Schemes. *)
  Inductive camp_driver : Set :=
    | Dv_camp_stop : camp_driver
    | Dv_camp_to_nraenv_core : nraenv_core_driver -> camp_driver
    | Dv_camp_to_nraenv : nraenv_driver -> camp_driver
    | Dv_camp_to_nra : nra_driver -> camp_driver

  with nra_driver : Set :=
    | Dv_nra_stop : nra_driver
    | Dv_nra_to_nnrc_core : nnrc_core_driver -> nra_driver
    | Dv_nra_to_nraenv_core : nraenv_core_driver -> nra_driver

  with nraenv_core_driver : Set :=
    | Dv_nraenv_core_stop : nraenv_core_driver
    | Dv_nraenv_core_to_nraenv : nraenv_driver -> nraenv_core_driver
    | Dv_nraenv_core_to_nnrc_core : nnrc_core_driver -> nraenv_core_driver
    | Dv_nraenv_core_to_nra : nra_driver -> nraenv_core_driver

  with nraenv_driver : Set :=
    | Dv_nraenv_stop : nraenv_driver
    | Dv_nraenv_optim : optim_phases_config -> nraenv_driver -> nraenv_driver
    | Dv_nraenv_to_nnrc : nnrc_driver -> nraenv_driver
    | Dv_nraenv_to_nraenv_core : nraenv_core_driver -> nraenv_driver

  with nnrc_driver : Set :=
    | Dv_nnrc_stop : nnrc_driver
    | Dv_nnrc_optim : optim_phases_config -> nnrc_driver -> nnrc_driver
    | Dv_nnrc_to_nnrc_core : nnrc_core_driver -> nnrc_driver
    | Dv_nnrc_to_nnrs : (* inputs *) list var -> nnrs_driver -> nnrc_driver
    | Dv_nnrc_to_nnrcmr : (* vinit *) var -> (* inputs_loc *) vdbindings -> nnrcmr_driver -> nnrc_driver
    | Dv_nnrc_to_dnnrc : (* inputs_loc *) vdbindings -> dnnrc_driver -> nnrc_driver
    | Dv_nnrc_to_javascript : javascript_driver -> nnrc_driver
    | Dv_nnrc_to_java : (* class_name *) string -> (* imports *) string -> java_driver -> nnrc_driver

  with nnrc_core_driver : Set :=
    | Dv_nnrc_core_stop : nnrc_core_driver
    | Dv_nnrc_core_to_nnrs_core : (* inputs *) list var -> nnrs_core_driver -> nnrc_core_driver
    | Dv_nnrc_core_to_nnrc : nnrc_driver -> nnrc_core_driver
    | Dv_nnrc_core_to_camp : (* avoid *) list var -> camp_driver -> nnrc_core_driver

  with nnrcmr_driver : Set :=
    | Dv_nnrcmr_stop : nnrcmr_driver
    | Dv_nnrcmr_optim : nnrcmr_driver -> nnrcmr_driver
    | Dv_nnrcmr_to_spark_rdd : (* queryname *) string -> spark_rdd_driver -> nnrcmr_driver
    | Dv_nnrcmr_to_nnrc : nnrc_driver -> nnrcmr_driver
    | Dv_nnrcmr_to_dnnrc : dnnrc_driver -> nnrcmr_driver.

(*  Set Elimination Scheme. *)

  Scheme camp_driver_ind' :=
    Induction for camp_driver Sort Prop
    with nra_driver_ind' :=
      Induction for nra_driver Sort Prop
      with nraenv_core_driver_ind' :=
        Induction for nraenv_core_driver Sort Prop
        with nraenv_driver_ind' :=
          Induction for nraenv_driver Sort Prop
          with nnrc_core_driver_ind' :=
            Induction for nnrc_core_driver Sort Prop
            with nnrc_driver_ind' :=
              Induction for nnrc_driver Sort Prop
              with nnrcmr_driver_ind' := Induction for nnrcmr_driver Sort Prop.

  Combined Scheme cnd_combined_ind
           from camp_driver_ind',
  nra_driver_ind',
  nraenv_core_driver_ind',
  nraenv_driver_ind',
  nnrc_core_driver_ind',
  nnrc_driver_ind',
  nnrcmr_driver_ind'.

  Inductive camp_rule_driver : Set :=
    | Dv_camp_rule_stop : camp_rule_driver
    | Dv_camp_rule_to_camp : camp_driver -> camp_rule_driver.

  Inductive tech_rule_driver : Set :=
    | Dv_tech_rule_stop : tech_rule_driver
    | Dv_tech_rule_to_camp_rule : camp_rule_driver -> tech_rule_driver.

  Inductive designer_rule_driver : Set :=
    | Dv_designer_rule_stop : designer_rule_driver
    | Dv_designer_rule_to_camp_rule : camp_rule_driver -> designer_rule_driver.

  Inductive oql_driver : Set :=
    | Dv_oql_stop : oql_driver
    | Dv_oql_to_nraenv : nraenv_driver -> oql_driver.

  Inductive sql_driver : Set :=
    | Dv_sql_stop : sql_driver
    | Dv_sql_to_nraenv : nraenv_driver -> sql_driver.

  Inductive sqlpp_driver : Set :=
    | Dv_sqlpp_stop : sqlpp_driver
    | Dv_sqlpp_to_nraenv : nraenv_driver -> sqlpp_driver.

  Inductive lambda_nra_driver : Set :=
    | Dv_lambda_nra_stop : lambda_nra_driver
    | Dv_lambda_nra_to_nraenv : nraenv_driver -> lambda_nra_driver.

  Inductive driver : Set :=
  | Dv_camp_rule : camp_rule_driver -> driver
  | Dv_tech_rule : tech_rule_driver -> driver
  | Dv_designer_rule : designer_rule_driver -> driver
  | Dv_camp : camp_driver -> driver
  | Dv_oql : oql_driver -> driver
  | Dv_sql : sql_driver -> driver
  | Dv_sqlpp : sqlpp_driver -> driver
  | Dv_lambda_nra : lambda_nra_driver -> driver
  | Dv_nra : nra_driver -> driver
  | Dv_nraenv_core : nraenv_core_driver -> driver
  | Dv_nraenv : nraenv_driver -> driver
  | Dv_nnrc_core : nnrc_core_driver -> driver
  | Dv_nnrc : nnrc_driver -> driver
  | Dv_nnrs_core : nnrs_core_driver -> driver
  | Dv_nnrs : nnrs_driver -> driver
  | Dv_nnrs_imp : nnrs_imp_driver -> driver
  | Dv_imp_qcert : imp_qcert_driver -> driver
  | Dv_imp_json : imp_json_driver -> driver
  | Dv_nnrcmr : nnrcmr_driver -> driver
  | Dv_dnnrc : dnnrc_driver -> driver
  | Dv_dnnrc_typed : dnnrc_typed_driver -> driver
  | Dv_js_ast : js_ast_driver -> driver
  | Dv_javascript : javascript_driver -> driver
  | Dv_java : java_driver -> driver
  | Dv_spark_rdd : spark_rdd_driver -> driver
  | Dv_spark_df : spark_df_driver -> driver
  | Dv_error : string -> driver.


  Tactic Notation "driver_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "Dv_camp_rule"%string
    | Case_aux c "Dv_tech_rule"%string
    | Case_aux c "Dv_designer_rule"%string
    | Case_aux c "Dv_camp"%string
    | Case_aux c "Dv_oql"%string
    | Case_aux c "Dv_sql"%string
    | Case_aux c "Dv_lambda_nra"%string
    | Case_aux c "Dv_nra"%string
    | Case_aux c "Dv_nraenv_core"%string
    | Case_aux c "Dv_nraenv"%string
    | Case_aux c "Dv_nnrc_core"%string
    | Case_aux c "Dv_nnrc"%string
    | Case_aux c "Dv_nnrs_core"%string
    | Case_aux c "Dv_nnrs"%string
    | Case_aux c "Dv_nnrs_imp"%string
    | Case_aux c "Dv_imp_qcert"%string
    | Case_aux c "Dv_imp_json"%string
    | Case_aux c "Dv_nnrcmr"%string
    | Case_aux c "Dv_dnnrc"%string
    | Case_aux c "Dv_dnnrc_typed"%string
    | Case_aux c "Dv_js_ast"%string
    | Case_aux c "Dv_javascript"%string
    | Case_aux c "Dv_java"%string
    | Case_aux c "Dv_spark_rdd"%string
    | Case_aux c "Dv_spark_df"%string
    | Case_aux c "Dv_error"%string ].


  (** Driver utility functions *)
  Section CompDriverUtil.

  Definition language_of_driver (dv: driver) :=
    match dv with
    | Dv_nra _ => L_nra
    | Dv_nraenv_core _ => L_nraenv_core
    | Dv_nraenv _ => L_nraenv
    | Dv_nnrc_core _ => L_nnrc_core
    | Dv_nnrc _ => L_nnrc
    | Dv_nnrs_core _ => L_nnrs_core
    | Dv_nnrs _ => L_nnrs
    | Dv_nnrs_imp _ => L_nnrs_imp
    | Dv_imp_qcert _ => L_imp_qcert
    | Dv_imp_json _ => L_imp_json
    | Dv_nnrcmr _ => L_nnrcmr
    | Dv_camp_rule _ => L_camp_rule
    | Dv_tech_rule _ => L_tech_rule
    | Dv_designer_rule _ => L_designer_rule
    | Dv_camp _ => L_camp
    | Dv_oql _ => L_oql
    | Dv_sql _ => L_sql
    | Dv_sqlpp _ => L_sqlpp
    | Dv_lambda_nra _ => L_lambda_nra
    | Dv_dnnrc  _ => L_dnnrc
    | Dv_dnnrc_typed _ => L_dnnrc_typed
    | Dv_js_ast _ => L_js_ast
    | Dv_javascript _ => L_javascript
    | Dv_java _ => L_java
    | Dv_spark_rdd _ => L_spark_rdd
    | Dv_spark_df _ => L_spark_df
    | Dv_error err => L_error ("language of "++err)
    end.

  Definition name_of_driver dv :=
    name_of_language (language_of_driver dv).

  Definition driver_length_javascript (dv: javascript_driver) :=
  match dv with
  | Dv_javascript_stop => 1
  end.

  Definition driver_length_js_ast (dv: js_ast_driver) :=
  match dv with
  | Dv_js_ast_stop => 1
  | Dv_js_ast_to_javascript dv => 1 + driver_length_javascript dv
  end.

  Definition driver_length_java (dv: java_driver) :=
    match dv with
    | Dv_java_stop => 1
    end.

  Definition driver_length_spark_rdd (dv: spark_rdd_driver) :=
    match dv with
    | Dv_spark_rdd_stop => 1
    end.

  Definition driver_length_spark_df (dv: spark_df_driver) :=
    match dv with
    | Dv_spark_df_stop => 1
    end.

  Fixpoint driver_length_imp_json (dv: imp_json_driver) :=
    match dv with
    | Dv_imp_json_stop => 1
    | Dv_imp_json_to_js_ast dv => 1 + driver_length_js_ast dv
    end.

  Fixpoint driver_length_imp_qcert (dv: imp_qcert_driver) :=
    match dv with
    | Dv_imp_qcert_stop => 1
    | Dv_imp_qcert_to_imp_json dv => 1 + driver_length_imp_json dv
    end.

  Fixpoint driver_length_nnrs_imp (dv: nnrs_imp_driver) :=
    match dv with
    | Dv_nnrs_imp_stop => 1
    | Dv_nnrs_imp_optim _ dv => 1 + driver_length_nnrs_imp dv
    | Dv_nnrs_imp_to_js_ast _ dv => 1 + driver_length_js_ast dv
    | Dv_nnrs_imp_to_imp_qcert _ dv => 1 + driver_length_imp_qcert dv
    end.

  Definition driver_length_nnrs (dv: nnrs_driver) :=
    match dv with
    | Dv_nnrs_stop => 1
    | Dv_nnrs_to_nnrs_imp dv => 1 + driver_length_nnrs_imp dv
    end.

  Definition driver_length_nnrs_core (dv: nnrs_core_driver) :=
    match dv with
    | Dv_nnrs_core_stop => 1
    | Dv_nnrs_core_to_nnrs dv => 1 + driver_length_nnrs dv
    end.

  Fixpoint driver_length_dnnrc_typed {ftyping: foreign_typing} (dv: dnnrc_typed_driver) :=
    match dv with
    | Dv_dnnrc_typed_stop => 1
    | Dv_dnnrc_typed_optim dv => 1 + driver_length_dnnrc_typed dv
    | Dv_dnnrc_typed_to_spark_df rt queryname dv => 1 + driver_length_spark_df dv
    end.

  Definition driver_length_dnnrc (dv: dnnrc_driver) :=
    match dv with
    | Dv_dnnrc_stop => 1
    | Dv_dnnrc_to_dnnrc_typed _ dv => 1 + driver_length_dnnrc_typed dv
    end.

  Fixpoint driver_length_camp (dv: camp_driver) :=
    match dv with
    | Dv_camp_stop => 1
    | Dv_camp_to_nraenv_core dv => 1 + driver_length_nraenv_core dv
    | Dv_camp_to_nraenv dv => 1 + driver_length_nraenv dv
    | Dv_camp_to_nra dv => 1 + driver_length_nra dv
    end

  with driver_length_nra (dv: nra_driver)  :=
    match dv with
    | Dv_nra_stop => 1
    | Dv_nra_to_nnrc_core dv => 1 + driver_length_nnrc_core dv
    | Dv_nra_to_nraenv_core dv => 1 + driver_length_nraenv_core dv
    end

  with driver_length_nraenv_core (dv: nraenv_core_driver) :=
    match dv with
    | Dv_nraenv_core_stop => 1
    | Dv_nraenv_core_to_nraenv dv => 1 + driver_length_nraenv dv
    | Dv_nraenv_core_to_nnrc_core dv => 1 + driver_length_nnrc_core dv
    | Dv_nraenv_core_to_nra dv => 1 + driver_length_nra dv
    end

  with driver_length_nraenv (dv: nraenv_driver) :=
    match dv with
    | Dv_nraenv_stop => 1
    | Dv_nraenv_optim opc dv => 1 + driver_length_nraenv dv
    | Dv_nraenv_to_nnrc dv => 1 + driver_length_nnrc dv
    | Dv_nraenv_to_nraenv_core dv => 1 + driver_length_nraenv_core dv
    end

  with driver_length_nnrc_core (dv: nnrc_core_driver) :=
    match dv with
    | Dv_nnrc_core_stop => 1
    | Dv_nnrc_core_to_nnrs_core inputs dv => 1 + driver_length_nnrs_core dv
    | Dv_nnrc_core_to_nnrc dv => 1 + driver_length_nnrc dv
    | Dv_nnrc_core_to_camp avoid dv => 1 + driver_length_camp dv
    end

  with driver_length_nnrc (dv: nnrc_driver) :=
    match dv with
    | Dv_nnrc_stop => 1
    | Dv_nnrc_optim opc dv => 1 + driver_length_nnrc dv
    | Dv_nnrc_to_nnrc_core dv => 1 + driver_length_nnrc_core dv
    | Dv_nnrc_to_nnrs inputs dv => 1 + driver_length_nnrs dv
    | Dv_nnrc_to_nnrcmr vinit inputs_loc dv => 1 + driver_length_nnrcmr dv
    | Dv_nnrc_to_dnnrc inputs_loc dv => 1 + driver_length_dnnrc dv
    | Dv_nnrc_to_javascript dv => 1 + driver_length_javascript dv
    | Dv_nnrc_to_java class_name imports dv => 1 + driver_length_java dv
    end

  with driver_length_nnrcmr (dv: nnrcmr_driver) :=
    match dv with
    | Dv_nnrcmr_stop => 1
    | Dv_nnrcmr_optim dv => 1 + driver_length_nnrcmr dv
    | Dv_nnrcmr_to_spark_rdd queryname dv => 1 + driver_length_spark_rdd dv
    | Dv_nnrcmr_to_nnrc dv => 1 + driver_length_nnrc dv
    | Dv_nnrcmr_to_dnnrc dv => 1 + driver_length_dnnrc dv
    end.

  Definition driver_length_camp_rule (dv: camp_rule_driver) :=
    match dv with
    | Dv_camp_rule_stop => 1
    | Dv_camp_rule_to_camp dv => 1 + driver_length_camp dv
    end.

  Definition driver_length_tech_rule (dv: tech_rule_driver) :=
    match dv with
    | Dv_tech_rule_stop => 1
    | Dv_tech_rule_to_camp_rule dv => 1 + driver_length_camp_rule dv
    end.

  Definition driver_length_designer_rule (dv: designer_rule_driver) :=
    match dv with
    | Dv_designer_rule_stop => 1
    | Dv_designer_rule_to_camp_rule dv => 1 + driver_length_camp_rule dv
    end.

  Definition driver_length_oql (dv: oql_driver) :=
    match dv with
    | Dv_oql_stop => 1
    | Dv_oql_to_nraenv dv => 1 + driver_length_nraenv dv
    end.

  Definition driver_length_sql (dv: sql_driver) :=
    match dv with
    | Dv_sql_stop => 1
    | Dv_sql_to_nraenv dv => 1 + driver_length_nraenv dv
    end.

  Definition driver_length_sqlpp (dv: sqlpp_driver) :=
    match dv with
    | Dv_sqlpp_stop => 1
    | Dv_sqlpp_to_nraenv dv => 1 + driver_length_nraenv dv
    end.

  Definition driver_length_lambda_nra (dv: lambda_nra_driver) :=
    match dv with
    | Dv_lambda_nra_stop => 1
    | Dv_lambda_nra_to_nraenv dv => 1 + driver_length_nraenv dv
    end.

  Definition driver_length (dv: driver)  :=
    match dv with
    | Dv_camp_rule dv => driver_length_camp_rule dv
    | Dv_tech_rule dv => driver_length_tech_rule dv
    | Dv_designer_rule dv => driver_length_designer_rule dv
    | Dv_camp dv => driver_length_camp dv
    | Dv_oql dv => driver_length_oql dv
    | Dv_sql dv => driver_length_sql dv
    | Dv_sqlpp dv => driver_length_sqlpp dv
    | Dv_lambda_nra dv => driver_length_lambda_nra dv
    | Dv_nra dv => driver_length_nra dv
    | Dv_nraenv_core dv => driver_length_nraenv_core dv
    | Dv_nraenv dv => driver_length_nraenv dv
    | Dv_nnrc_core dv => driver_length_nnrc_core dv
    | Dv_nnrc dv => driver_length_nnrc dv
    | Dv_nnrs_core dv => driver_length_nnrs_core dv
    | Dv_nnrs dv => driver_length_nnrs dv
    | Dv_nnrs_imp dv => driver_length_nnrs_imp dv
    | Dv_imp_qcert dv => driver_length_imp_qcert dv
    | Dv_imp_json dv => driver_length_imp_json dv
    | Dv_nnrcmr dv => driver_length_nnrcmr dv
    | Dv_dnnrc dv => driver_length_dnnrc dv
    | Dv_dnnrc_typed dv => driver_length_dnnrc_typed dv
    | Dv_js_ast dv => driver_length_js_ast dv
    | Dv_javascript dv => driver_length_javascript dv
    | Dv_java dv => driver_length_java dv
    | Dv_spark_rdd dv => driver_length_spark_rdd dv
    | Dv_spark_df dv => driver_length_spark_df dv
    | Dv_error s => 1
    end.

  End CompDriverUtil.

  (** Compilation functions*)
  Section CompDriverCompile.
    Definition compile_javascript (dv: javascript_driver) (q: javascript) : list query :=
      let queries :=
          match dv with
          | Dv_javascript_stop => nil
          end
      in
      (Q_javascript q) :: queries.

    Definition compile_js_ast (dv: js_ast_driver) (q: js_ast) : list query :=
      let queries :=
          match dv with
          | Dv_js_ast_stop => nil
          | Dv_js_ast_to_javascript dv =>
            let q := js_ast_to_javascript q in
            compile_javascript dv q
          end
      in
      (Q_js_ast q) :: queries.

    Definition compile_java (dv: java_driver) (q: java) : list query :=
      let queries :=
          match dv with
          | Dv_java_stop => nil
          end
      in
      (Q_java q) :: queries.

    Definition compile_spark_rdd (dv: spark_rdd_driver) (q: spark_rdd) : list query :=
      let queries :=
          match dv with
          | Dv_spark_rdd_stop => nil
          end
      in
      (Q_spark_rdd q) :: queries.

    Definition compile_spark_df (dv: spark_df_driver) (q: spark_df) : list query :=
      let queries :=
          match dv with
          | Dv_spark_df_stop => nil
          end
      in
      (Q_spark_df q) :: queries.

    Definition compile_imp_json (dv: imp_json_driver) (q: imp_json) : list query :=
      let queries :=
          match dv with
          | Dv_imp_json_stop => nil
          | Dv_imp_json_to_js_ast dv =>
            let q := imp_json_to_js_ast q in
            compile_js_ast dv q
          end
      in
      (Q_imp_json q) :: queries.

    Definition compile_imp_qcert (dv: imp_qcert_driver) (q: imp_qcert) : list query :=
      let queries :=
          match dv with
          | Dv_imp_qcert_stop => nil
          | Dv_imp_qcert_to_imp_json dv =>
            let q := imp_qcert_to_imp_json q in
            compile_imp_json dv q
          end
      in
      (Q_imp_qcert q) :: queries.

    Fixpoint compile_nnrs_imp (dv: nnrs_imp_driver) (q: nnrs_imp) : list query :=
      let queries :=
          match dv with
          | Dv_nnrs_imp_stop => nil
          | Dv_nnrs_imp_optim oc dv =>
            let q := nnrs_imp_optim oc q in
            compile_nnrs_imp dv q
          | Dv_nnrs_imp_to_js_ast inputs dv =>
            let q := nnrs_imp_to_js_ast inputs q in
            compile_js_ast dv q
          | Dv_nnrs_imp_to_imp_qcert qname dv =>
            let q := nnrs_imp_to_imp_qcert qname q in
            compile_imp_qcert dv q
          end
      in
      (Q_nnrs_imp q) :: queries.

    Definition compile_nnrs (dv: nnrs_driver) (q: nnrs) : list query :=
      let queries :=
          match dv with
          | Dv_nnrs_stop => nil
          | Dv_nnrs_to_nnrs_imp dv =>
            let q := nnrs_to_nnrs_imp q in
            compile_nnrs_imp dv q
          end
      in
      (Q_nnrs q) :: queries.

    Definition compile_nnrs_core (dv: nnrs_core_driver) (q: nnrs_core) : list query :=
      let queries :=
          match dv with
          | Dv_nnrs_core_stop => nil
          | Dv_nnrs_core_to_nnrs dv =>
            let q := nnrs_core_to_nnrs q in
            compile_nnrs dv q
          end
      in
      (Q_nnrs_core q) :: queries.

    Fixpoint compile_dnnrc_typed (dv: dnnrc_typed_driver) (q: dnnrc_typed) : list query :=
      let queries :=
          match dv with
          | Dv_dnnrc_typed_stop => nil
          | Dv_dnnrc_typed_optim dv =>
            let q := dnnrc_typed_optim q in
            compile_dnnrc_typed dv q
          | Dv_dnnrc_typed_to_spark_df rt queryname dv =>
            let q := dnnrc_typed_to_spark_df rt queryname q in
            compile_spark_df dv q
          end
      in
      (Q_dnnrc_typed q) :: queries.

    Definition compile_dnnrc (dv: dnnrc_driver) (q: dnnrc) : list query :=
      let queries :=
          match dv with
          | Dv_dnnrc_stop => nil
          | Dv_dnnrc_to_dnnrc_typed tdenv dv =>
            let q := dnnrc_to_dnnrc_typed q tdenv in
            match q with
            | Some q => compile_dnnrc_typed dv q
            | None => (Q_error "Type checking failed for dnnrc query") :: nil
            end
          end
      in
      (Q_dnnrc q) :: queries.

    Fixpoint compile_camp (dv: camp_driver) (q: camp) : list query :=
      let queries :=
          match dv with
          | Dv_camp_stop => nil
          | Dv_camp_to_nraenv_core dv =>
            let q := camp_to_nraenv_core q in
            compile_nraenv_core dv q
          | Dv_camp_to_nraenv dv =>
            let q := camp_to_nraenv q in
            compile_nraenv dv q
          | Dv_camp_to_nra dv =>
            let q := camp_to_nra q in
            compile_nra dv q
          end
      in
      (Q_camp q) :: queries

    with compile_nra (dv: nra_driver) (q: nra) : list query :=
      let queries :=
          match dv with
          | Dv_nra_stop => nil
          | Dv_nra_to_nnrc_core dv =>
            let q := nra_to_nnrc_core q in
            compile_nnrc_core dv q
          | Dv_nra_to_nraenv_core dv =>
            let q := nra_to_nraenv_core q in
            compile_nraenv_core dv q
          end
      in
      (Q_nra q) :: queries

    with compile_nraenv (dv: nraenv_driver) (q: nraenv) : list query :=
      let queries :=
          match dv with
          | Dv_nraenv_stop => nil
          | Dv_nraenv_optim opc dv =>
            let q := nraenv_optim opc q in
            compile_nraenv dv q
          | Dv_nraenv_to_nnrc dv =>
            let q := nraenv_to_nnrc q in
            compile_nnrc dv q
          | Dv_nraenv_to_nraenv_core dv =>
            let q := nraenv_to_nraenv_core q in
            compile_nraenv_core dv q
          end
      in
      (Q_nraenv q) :: queries

    with compile_nraenv_core (dv: nraenv_core_driver) (q: nraenv_core) : list query :=
      let queries :=
          match dv with
          | Dv_nraenv_core_stop => nil
          | Dv_nraenv_core_to_nraenv dv =>
            let q := nraenv_core_to_nraenv q in
            compile_nraenv dv q
          | Dv_nraenv_core_to_nnrc_core dv =>
            let q := nraenv_core_to_nnrc_core q in
            compile_nnrc_core dv q
          | Dv_nraenv_core_to_nra dv =>
            let q := nraenv_core_to_nra q in
            compile_nra dv q
          end
      in
      (Q_nraenv_core q) :: queries

    with compile_nnrc_core (dv: nnrc_core_driver) (q: nnrc_core) : list query :=
      let queries :=
          match dv with
          | Dv_nnrc_core_stop => nil
          | Dv_nnrc_core_to_nnrs_core inputs dv =>
            let q := nnrc_core_to_nnrs_core inputs q in
            compile_nnrs_core dv q
          | Dv_nnrc_core_to_nnrc dv =>
            let q := nnrc_core_to_nnrc q in
            compile_nnrc dv q
          | Dv_nnrc_core_to_camp avoid dv =>
            let q := nnrc_core_to_camp avoid q in
            compile_camp dv q
          end
      in
      (Q_nnrc_core q) :: queries

    with compile_nnrc (dv: nnrc_driver) (q: nnrc) : list query :=
      let queries :=
          match dv with
          | Dv_nnrc_stop => nil
          | Dv_nnrc_optim opc dv =>
            let q := nnrc_optim opc q in
            compile_nnrc dv q
          | Dv_nnrc_to_nnrc_core dv =>
            let q := nnrc_to_nnrc_core q in
            compile_nnrc_core dv q
          | Dv_nnrc_to_nnrs inputs dv =>
            let q := nnrc_to_nnrs inputs q in
            compile_nnrs dv q
          | Dv_nnrc_to_nnrcmr vinit inputs_loc dv =>
            let q := nnrc_to_nnrcmr vinit inputs_loc q in
            compile_nnrcmr dv q
          | Dv_nnrc_to_dnnrc inputs_loc dv =>
            let q := nnrc_to_dnnrc inputs_loc q in
            compile_dnnrc dv q
          | Dv_nnrc_to_javascript dv =>
            let q := nnrc_to_javascript q in
            compile_javascript dv q
          | Dv_nnrc_to_java class_name imports dv =>
            let q := nnrc_to_java class_name imports q in
            compile_java dv q
          end
      in
      (Q_nnrc q) :: queries

    with compile_nnrcmr (dv: nnrcmr_driver) (q: nnrcmr) : list query :=
      let queries :=
          match dv with
          | Dv_nnrcmr_stop => nil
          | Dv_nnrcmr_optim dv =>
            let q := nnrcmr_optim q in
            compile_nnrcmr dv q
          | Dv_nnrcmr_to_spark_rdd queryname dv =>
            let q := nnrcmr_to_spark_rdd queryname q in
            compile_spark_rdd dv q
          | Dv_nnrcmr_to_nnrc dv =>
            let q_opt := nnrcmr_to_nnrc q in
            match q_opt with
            | Some q => compile_nnrc dv q
            | None => (Q_error "Unable to compile NNRCMR to NNRC") :: nil
            end
          | Dv_nnrcmr_to_dnnrc dv =>
            let q_opt := nnrcmr_to_dnnrc q in
            match q_opt with
            | Some q => compile_dnnrc dv q
            | None => (Q_error "Unable to compile NNRCMR to NNRC") :: nil
            end
          end
      in
      (Q_nnrcmr q) :: queries.

    Definition compile_camp_rule (dv: camp_rule_driver) (q: camp_rule) : list query :=
      let queries :=
          match dv with
          | Dv_camp_rule_stop => nil
          | Dv_camp_rule_to_camp dv =>
            let q := camp_rule_to_camp q in
            compile_camp dv q
          end
      in
      (Q_camp_rule q) :: queries.

    Definition compile_tech_rule (dv: tech_rule_driver) (q: tech_rule) : list query :=
      let queries :=
          match dv with
          | Dv_tech_rule_stop => nil
          | Dv_tech_rule_to_camp_rule dv =>
            let q := tech_rule_to_camp_rule q in
            compile_camp_rule dv q
          end
      in
      (Q_tech_rule q) :: queries.

    Definition compile_designer_rule (dv: designer_rule_driver) (q: designer_rule) : list query :=
      let queries :=
          match dv with
          | Dv_designer_rule_stop => nil
          | Dv_designer_rule_to_camp_rule dv =>
            let q := designer_rule_to_camp_rule q in
            compile_camp_rule dv q
          end
      in
      (Q_designer_rule q) :: queries.

    Definition compile_oql (dv: oql_driver) (q: oql) : list query :=
      let queries :=
          match dv with
          | Dv_oql_stop => nil
          | Dv_oql_to_nraenv dv =>
            let q := oql_to_nraenv q in
            compile_nraenv dv q
          end
      in
      (Q_oql q) :: queries.

    Definition compile_sql (dv: sql_driver) (q: sql) : list query :=
      let queries :=
          match dv with
          | Dv_sql_stop => nil
          | Dv_sql_to_nraenv dv =>
            let q := sql_to_nraenv q in
            compile_nraenv dv q
          end
      in
      (Q_sql q) :: queries.

    Definition compile_sqlpp (dv: sqlpp_driver) (q: sqlpp) : list query :=
      let queries :=
          match dv with
          | Dv_sqlpp_stop => nil
          | Dv_sqlpp_to_nraenv dv =>
            let q := sqlpp_to_nraenv q in
            compile_nraenv dv q
          end
      in
      (Q_sqlpp q) :: queries.

    Definition compile_lambda_nra (dv: lambda_nra_driver) (q: lambda_nra) : list query :=
      let queries :=
          match dv with
          | Dv_lambda_nra_stop => nil
          | Dv_lambda_nra_to_nraenv dv =>
            let q := lambda_nra_to_nraenv q in
            compile_nraenv dv q
          end
      in
      (Q_lambda_nra q) :: queries.

    Definition compile (dv: driver) (q: query) : list query :=
      match (dv, q) with
      | (Dv_camp_rule dv, Q_camp_rule q) => compile_camp_rule dv q
      | (Dv_tech_rule dv, Q_tech_rule q) => compile_tech_rule dv q
      | (Dv_designer_rule dv, Q_designer_rule q) => compile_designer_rule dv q
      | (Dv_camp dv, Q_camp q) => compile_camp dv q
      | (Dv_oql dv, Q_oql q) => compile_oql dv q
      | (Dv_sql dv, Q_sql q) => compile_sql dv q
      | (Dv_sqlpp dv, Q_sqlpp q) => compile_sqlpp dv q
      | (Dv_lambda_nra dv, Q_lambda_nra q) => compile_lambda_nra dv q
      | (Dv_nra dv, Q_nra q) => compile_nra dv q
      | (Dv_nraenv_core dv, Q_nraenv_core q) => compile_nraenv_core dv q
      | (Dv_nraenv dv, Q_nraenv q) => compile_nraenv dv q
      | (Dv_nnrc_core dv, Q_nnrc_core q) => compile_nnrc_core dv q
      | (Dv_nnrc dv, Q_nnrc q) => compile_nnrc dv q
      | (Dv_nnrs_core dv, Q_nnrs_core q) => compile_nnrs_core dv q
      | (Dv_nnrs dv, Q_nnrs q) => compile_nnrs dv q
      | (Dv_nnrs_imp dv, Q_nnrs_imp q) => compile_nnrs_imp dv q
      | (Dv_imp_qcert dv, Q_imp_qcert q) => compile_imp_qcert dv q
      | (Dv_imp_json dv, Q_imp_json q) => compile_imp_json dv q
      | (Dv_nnrcmr dv, Q_nnrcmr q) => compile_nnrcmr dv q
      | (Dv_dnnrc dv, Q_dnnrc q) => compile_dnnrc dv q
      | (Dv_dnnrc_typed dv, Q_dnnrc_typed q) => compile_dnnrc_typed dv q
      | (Dv_js_ast dv, Q_js_ast q) => compile_js_ast dv q
      | (Dv_javascript dv, Q_javascript q) => compile_javascript dv q
      | (Dv_java dv, Q_java q) => compile_java dv q
      | (Dv_spark_rdd dv, Q_spark_rdd q) => compile_spark_rdd dv q
      | (Dv_spark_df dv, Q_spark_df q) => compile_spark_df dv q
      | (Dv_error s, _) => (Q_error ("[Driver Error]" ++ s)) :: nil
      | (_, _) => (Q_error "incompatible query and driver") :: nil
      end.

  End CompDriverCompile.

  (** Driver builder *)
  Section CompDriverConfig.
  Definition push_translation config lang dv :=
    match lang with
    | L_camp_rule =>
      match dv with
      | Dv_camp dv => Dv_camp_rule (Dv_camp_rule_to_camp dv)
      | Dv_nraenv_core _
      | Dv_nraenv _
      | Dv_nra _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_tech_rule =>
      match dv with
      | Dv_camp_rule dv => Dv_tech_rule (Dv_tech_rule_to_camp_rule dv)
      | Dv_camp _
      | Dv_nraenv_core _
      | Dv_nraenv _
      | Dv_nra _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_designer_rule =>
      match dv with
      | Dv_camp_rule dv => Dv_designer_rule (Dv_designer_rule_to_camp_rule dv)
      | Dv_camp _
      | Dv_nraenv_core _
      | Dv_nraenv _
      | Dv_nra _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_camp =>
      match dv with
      | Dv_nraenv_core dv => Dv_camp (Dv_camp_to_nraenv_core dv)
      | Dv_nraenv dv => Dv_camp (Dv_camp_to_nraenv dv)
      | Dv_nra dv => Dv_camp (Dv_camp_to_nra dv)
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_oql =>
      match dv with
      | Dv_nraenv dv => Dv_oql (Dv_oql_to_nraenv dv)
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv_core _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_sql =>
      match dv with
      | Dv_nraenv dv => Dv_sql (Dv_sql_to_nraenv dv)
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv_core _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_sqlpp =>
      match dv with
      | Dv_nraenv dv => Dv_sqlpp (Dv_sqlpp_to_nraenv dv)
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv_core _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_lambda_nra =>
      match dv with
      | Dv_nraenv dv => Dv_lambda_nra (Dv_lambda_nra_to_nraenv dv)
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv_core _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nra =>
      match dv with
      | Dv_nnrc_core dv => Dv_nra (Dv_nra_to_nnrc_core dv)
      | Dv_nraenv_core dv => Dv_nra (Dv_nra_to_nraenv_core dv)
      | Dv_nra _
      | Dv_nraenv _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nraenv_core =>
      match dv with
      | Dv_nnrc_core dv => Dv_nraenv_core (Dv_nraenv_core_to_nnrc_core dv)
      | Dv_nra dv => Dv_nraenv_core (Dv_nraenv_core_to_nra dv)
      | Dv_nraenv dv => Dv_nraenv_core (Dv_nraenv_core_to_nraenv dv)
      | Dv_nraenv_core _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nraenv =>
      match dv with
      | Dv_nraenv_core dv => Dv_nraenv (Dv_nraenv_to_nraenv_core dv)
      | Dv_nraenv dv => Dv_nraenv (Dv_nraenv_optim (get_optim_config L_nraenv config.(comp_optim_config)) dv)
      | Dv_nnrc dv => Dv_nraenv (Dv_nraenv_to_nnrc dv)
      | Dv_nra _
      | Dv_nnrc_core _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nnrc_core =>
      match dv with
      | Dv_camp dv => Dv_nnrc_core (Dv_nnrc_core_to_camp (List.map fst (vdbindings_of_constants_config config.(comp_constants))) dv) (* XXX to check XXX *)
      | Dv_nnrc dv => Dv_nnrc_core (Dv_nnrc_core_to_nnrc dv)
      | Dv_nnrs_core dv => Dv_nnrc_core (Dv_nnrc_core_to_nnrs_core (vars_of_constants_config config.(comp_constants)) dv)
      | Dv_nnrc_core _
      | Dv_nraenv _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv_core _
      | Dv_dnnrc_typed _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nnrc =>
      match dv with
      | Dv_nnrs dv => Dv_nnrc (Dv_nnrc_to_nnrs (vars_of_constants_config config.(comp_constants)) dv)
      | Dv_nnrcmr dv => Dv_nnrc (Dv_nnrc_to_nnrcmr config.(comp_mr_vinit) (vdbindings_of_constants_config config.(comp_constants)) dv)
      | Dv_dnnrc dv => Dv_nnrc (Dv_nnrc_to_dnnrc (vdbindings_of_constants_config config.(comp_constants)) dv)
      | Dv_javascript dv => Dv_nnrc (Dv_nnrc_to_javascript dv)
      | Dv_java dv => Dv_nnrc (Dv_nnrc_to_java config.(comp_class_name) config.(comp_java_imports) dv)
      | Dv_nnrc dv => Dv_nnrc (Dv_nnrc_optim (get_optim_config L_nnrc config.(comp_optim_config)) dv)
      | Dv_nnrc_core dv => Dv_nnrc (Dv_nnrc_to_nnrc_core dv)
      | Dv_camp _
      | Dv_nraenv _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrs_core _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_js_ast _
      | Dv_nra _
      | Dv_nraenv_core _
      | Dv_dnnrc_typed _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nnrs_core =>
      match dv with
      | Dv_nnrs dv => Dv_nnrs_core (Dv_nnrs_core_to_nnrs dv)
      | Dv_camp _
      | Dv_nraenv_core _
      | Dv_nraenv _
      | Dv_nra _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
        Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
        Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nnrs =>
      match dv with
      | Dv_nnrs_imp dv => Dv_nnrs (Dv_nnrs_to_nnrs_imp dv)
      | Dv_camp _
      | Dv_nraenv_core _
      | Dv_nraenv _
      | Dv_nra _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_js_ast _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nnrs_imp =>
      match dv with
      | Dv_js_ast dv => Dv_nnrs_imp (Dv_nnrs_imp_to_js_ast (vars_of_constants_config config.(comp_constants)) dv)
      | Dv_imp_qcert dv => Dv_nnrs_imp (Dv_nnrs_imp_to_imp_qcert config.(comp_qname_lowercase) dv)
      | Dv_nnrs_imp dv => Dv_nnrs_imp (Dv_nnrs_imp_optim (get_optim_config L_nnrs_imp config.(comp_optim_config)) dv)
      | Dv_camp _
      | Dv_nraenv_core _
      | Dv_nraenv _
      | Dv_nra _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_imp_qcert =>
      match dv with
      | Dv_imp_qcert _ =>
          Dv_error ("XXX TODO: imp_qcert optimizer XXX")
      | Dv_imp_json dv =>
        Dv_imp_qcert (Dv_imp_qcert_to_imp_json dv)
      | Dv_camp _
      | Dv_nraenv_core _
      | Dv_nraenv _
      | Dv_nra _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_js_ast _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_imp_json =>
      match dv with
      | Dv_imp_json _ =>
          Dv_error ("XXX TODO: imp_qcert optimizer XXX")
      | Dv_js_ast dv =>
        Dv_imp_json (Dv_imp_json_to_js_ast dv)
      | Dv_camp _
      | Dv_nraenv_core _
      | Dv_nraenv _
      | Dv_nra _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_dnnrc_typed _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nnrcmr =>
      match dv with
      | Dv_spark_rdd dv => Dv_nnrcmr (Dv_nnrcmr_to_spark_rdd config.(comp_qname) dv)
      | Dv_nnrc dv => Dv_nnrcmr (Dv_nnrcmr_to_nnrc dv)
      | Dv_dnnrc dv => Dv_nnrcmr (Dv_nnrcmr_to_dnnrc dv)
      | Dv_nnrcmr dv => Dv_nnrcmr (Dv_nnrcmr_optim dv)
      | Dv_nraenv _
      | Dv_nnrc_core _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv_core _
      | Dv_dnnrc_typed _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_dnnrc =>
      match dv with
      | Dv_dnnrc_typed dv =>
          Dv_dnnrc (Dv_dnnrc_to_dnnrc_typed (tdbindings_of_constants_config config.(comp_constants)) dv)
      | Dv_dnnrc _
      | Dv_nraenv _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv_core _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _
      | Dv_spark_df _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_dnnrc_typed =>
      match dv with
      | Dv_spark_df dv =>
          Dv_dnnrc_typed (Dv_dnnrc_typed_to_spark_df (tdbindings_of_constants_config config.(comp_constants)) config.(comp_qname) dv)
      | Dv_dnnrc_typed dv =>
        Dv_dnnrc_typed (Dv_dnnrc_typed_optim dv)
      | Dv_nraenv _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv_core _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_js_ast _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark_rdd _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_js_ast =>
      match dv with
      | Dv_javascript dv =>
          Dv_js_ast (Dv_js_ast_to_javascript dv)
      | Dv_nraenv _
      | Dv_camp_rule _
      | Dv_tech_rule _
      | Dv_designer_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_sqlpp _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv_core _
      | Dv_nnrc_core _
      | Dv_nnrc _
      | Dv_nnrs_core _
      | Dv_nnrs _
      | Dv_nnrs_imp _
      | Dv_imp_qcert _
      | Dv_imp_json _
      | Dv_nnrcmr _
      | Dv_dnnrc _
      | Dv_js_ast _
      | Dv_spark_df _
      | Dv_dnnrc_typed _
      | Dv_java _
      | Dv_spark_rdd _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_javascript
    | L_java
    | L_spark_rdd
    | L_spark_df =>
      Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
    | L_error err =>
      Dv_error ("No compilation from error ("++err++")")
    end.

  Definition driver_of_language lang :=
    match lang with
    | L_camp_rule => Dv_camp_rule Dv_camp_rule_stop
    | L_tech_rule => Dv_tech_rule Dv_tech_rule_stop
    | L_designer_rule => Dv_designer_rule Dv_designer_rule_stop
    | L_camp => Dv_camp Dv_camp_stop
    | L_oql => Dv_oql Dv_oql_stop
    | L_sql => Dv_sql Dv_sql_stop
    | L_sqlpp => Dv_sqlpp Dv_sqlpp_stop
    | L_lambda_nra => Dv_lambda_nra Dv_lambda_nra_stop
    | L_nra => Dv_nra Dv_nra_stop
    | L_nraenv_core => Dv_nraenv_core Dv_nraenv_core_stop
    | L_nraenv => Dv_nraenv Dv_nraenv_stop
    | L_nnrc_core => Dv_nnrc_core Dv_nnrc_core_stop
    | L_nnrc => Dv_nnrc Dv_nnrc_stop
    | L_nnrs_core => Dv_nnrs_core Dv_nnrs_core_stop
    | L_nnrs => Dv_nnrs Dv_nnrs_stop
    | L_nnrs_imp => Dv_nnrs_imp Dv_nnrs_imp_stop
    | L_imp_qcert => Dv_imp_qcert Dv_imp_qcert_stop
    | L_imp_json => Dv_imp_json Dv_imp_json_stop
    | L_nnrcmr => Dv_nnrcmr Dv_nnrcmr_stop
    | L_dnnrc => Dv_dnnrc Dv_dnnrc_stop
    | L_dnnrc_typed => Dv_dnnrc_typed Dv_dnnrc_typed_stop
    | L_js_ast => Dv_js_ast Dv_js_ast_stop
    | L_javascript => Dv_javascript Dv_javascript_stop
    | L_java => Dv_java Dv_java_stop
    | L_spark_rdd => Dv_spark_rdd Dv_spark_rdd_stop
    | L_spark_df => Dv_spark_df Dv_spark_df_stop
    | L_error err => Dv_error ("No driver for error: "++err)
    end.

  Fixpoint driver_of_rev_path config dv rev_path :=
    match rev_path with
    | nil => dv
    | lang :: rev_path =>
        driver_of_rev_path config (push_translation config lang dv) rev_path
    end.

  Definition driver_of_path config path :=
    match List.rev path with
    | nil => Dv_error "Empty compilation path"
    | target :: rev_path =>
        driver_of_rev_path config (driver_of_language target) rev_path
    end.


  (* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

  Definition no_dv_error (dv: driver) : Prop :=
    match dv with
    | Dv_error _ => False
    | _ => True
    end.

  Inductive is_postfix_driver : driver -> driver -> Prop :=
  | is_postfix_eq :
      forall dv' dv, dv' = dv -> is_postfix_driver dv' dv
  | is_postfix_plus_one :
      forall dv' dv,
      forall config lang dv_plus_one,
        is_postfix_driver dv' dv ->
        push_translation config lang dv = dv_plus_one ->
        no_dv_error dv_plus_one ->
        is_postfix_driver dv' dv_plus_one.

  Global Instance is_postfix_driver_refl : Reflexive is_postfix_driver.
  Proof.
    constructor; trivial.
  Qed.

  Global Instance is_postfix_driver_trans : Transitive is_postfix_driver.
  Proof.
    unfold Transitive.
    intros dv'' dv' dv H_dv''_dv' H_dv'_dv.
    induction 0.
    - rewrite H in *; clear H.
      assumption.
    - apply (is_postfix_plus_one dv'' dv config lang);
        try assumption.
      apply IHH_dv'_dv.
      assumption.
  Qed.

  Definition is_driver_config (config: driver_config) (dv: driver) : Prop :=
      forall dv',
        is_postfix_driver dv' dv ->
        match dv' with
        | Dv_nnrc (Dv_nnrc_to_nnrs inputs _) =>
          inputs = (vars_of_constants_config config.(comp_constants))
        | Dv_nnrc_core (Dv_nnrc_core_to_nnrs_core inputs _) =>
          inputs = (vars_of_constants_config config.(comp_constants))
        | Dv_nnrc (Dv_nnrc_to_nnrcmr vinit vdbindings _) =>
          vinit = config.(comp_mr_vinit) /\ vdbindings = (vdbindings_of_constants_config config.(comp_constants))
        | Dv_nnrc (Dv_nnrc_to_dnnrc vdbindings _) =>
          vdbindings = (vdbindings_of_constants_config config.(comp_constants))
        | Dv_nnrc (Dv_nnrc_to_java class_name imports _) =>
          class_name = config.(comp_class_name) /\ imports = config.(comp_java_imports)
        | Dv_nraenv (Dv_nraenv_optim opc _) =>
          opc = (get_optim_config L_nraenv config.(comp_optim_config))
        | Dv_nnrc (Dv_nnrc_optim opc _) =>
          opc = (get_optim_config L_nnrc config.(comp_optim_config))
        | Dv_nnrc_core (Dv_nnrc_core_to_camp avoid _) =>
          avoid = (List.map fst (vdbindings_of_constants_config config.(comp_constants)))
        | Dv_nnrs (Dv_nnrs_to_nnrs_imp _) =>
          True (* inputs = (vars_of_constants_config config.(comp_constants)) *)
        | Dv_nnrs_imp (Dv_nnrs_imp_optim opc _) =>
          opc = (get_optim_config L_nnrs_imp config.(comp_optim_config))
        | Dv_nnrs_imp (Dv_nnrs_imp_to_js_ast inputs _) =>
          inputs = (vars_of_constants_config config.(comp_constants))
        | Dv_nnrs_imp (Dv_nnrs_imp_to_imp_qcert qname _) =>
          qname = config.(comp_qname_lowercase)
        | Dv_nnrcmr (Dv_nnrcmr_to_spark_rdd qname _) =>
          qname = config.(comp_qname)
        | Dv_dnnrc (Dv_dnnrc_to_dnnrc_typed tdbindings _) =>
          tdbindings = tdbindings_of_constants_config config.(comp_constants)
        | Dv_dnnrc_typed (Dv_dnnrc_typed_to_spark_df tdbindings qname _) =>
          (tdbindings = tdbindings_of_constants_config config.(comp_constants)) /\ qname = config.(comp_qname)
        | _ => True
        end.

  Lemma is_driver_config_trans:
    forall config dv dv',
      is_postfix_driver dv' dv ->
      is_driver_config config dv ->
      is_driver_config config dv'.
  Proof.
    intros config dv dv' H_is_postfix_dv' H_is_driver_config_dv'.
    unfold is_driver_config.
    intros dv'' H_is_postfix_dv''.
    apply (H_is_driver_config_dv' dv'').
    apply (is_postfix_driver_trans dv'' dv' dv);
    assumption.
  Qed.

  Definition pop_transition dv : language * option driver :=
    match dv with
    | Dv_camp_rule (Dv_camp_rule_stop) => (L_camp_rule, None)
    | Dv_camp_rule (Dv_camp_rule_to_camp dv) => (L_camp_rule, Some (Dv_camp dv))
    | Dv_tech_rule (Dv_tech_rule_stop) => (L_tech_rule, None)
    | Dv_tech_rule (Dv_tech_rule_to_camp_rule dv) => (L_tech_rule, Some (Dv_camp_rule dv))
    | Dv_designer_rule (Dv_designer_rule_stop) => (L_designer_rule, None)
    | Dv_designer_rule (Dv_designer_rule_to_camp_rule dv) => (L_designer_rule, Some (Dv_camp_rule dv))
    | Dv_camp (Dv_camp_stop) => (L_camp, None)
    | Dv_camp (Dv_camp_to_nraenv_core dv) => (L_camp, Some (Dv_nraenv_core dv))
    | Dv_camp (Dv_camp_to_nraenv dv) => (L_camp, Some (Dv_nraenv dv))
    | Dv_camp (Dv_camp_to_nra dv) => (L_camp, Some (Dv_nra dv))
    | Dv_oql (Dv_oql_stop) => (L_oql, None)
    | Dv_oql (Dv_oql_to_nraenv dv) => (L_oql, Some (Dv_nraenv dv))
    | Dv_sql (Dv_sql_stop) => (L_sql, None)
    | Dv_sql (Dv_sql_to_nraenv dv) => (L_sql, Some (Dv_nraenv dv))
    | Dv_sqlpp (Dv_sqlpp_stop) => (L_sqlpp, None)
    | Dv_sqlpp (Dv_sqlpp_to_nraenv dv) => (L_sqlpp, Some (Dv_nraenv dv))
    | Dv_lambda_nra (Dv_lambda_nra_stop) => (L_lambda_nra, None)
    | Dv_lambda_nra (Dv_lambda_nra_to_nraenv dv) => (L_lambda_nra, Some (Dv_nraenv dv))
    | Dv_nra (Dv_nra_stop) => (L_nra, None)
    | Dv_nra (Dv_nra_to_nnrc_core dv) => (L_nra, Some (Dv_nnrc_core dv))
    | Dv_nra (Dv_nra_to_nraenv_core dv) => (L_nra, Some (Dv_nraenv_core dv))
    | Dv_nraenv_core (Dv_nraenv_core_stop) => (L_nraenv_core, None)
    | Dv_nraenv_core (Dv_nraenv_core_to_nnrc_core dv) => (L_nraenv_core, Some (Dv_nnrc_core dv))
    | Dv_nraenv_core (Dv_nraenv_core_to_nra dv) => (L_nraenv_core, Some (Dv_nra dv))
    | Dv_nraenv_core (Dv_nraenv_core_to_nraenv dv) => (L_nraenv_core, Some (Dv_nraenv dv))
    | Dv_nraenv (Dv_nraenv_stop) => (L_nraenv, None)
    | Dv_nraenv (Dv_nraenv_optim opc dv) => (L_nraenv, Some (Dv_nraenv dv))
    | Dv_nraenv (Dv_nraenv_to_nnrc dv) => (L_nraenv, Some (Dv_nnrc dv))
    | Dv_nraenv (Dv_nraenv_to_nraenv_core dv) => (L_nraenv, Some (Dv_nraenv_core dv))
    | Dv_nnrc_core (Dv_nnrc_core_stop) => (L_nnrc_core, None)
    | Dv_nnrc_core (Dv_nnrc_core_to_nnrs_core inputs dv) => (L_nnrc_core, Some (Dv_nnrs_core dv))
    | Dv_nnrc_core (Dv_nnrc_core_to_nnrc dv) => (L_nnrc_core, Some (Dv_nnrc dv))
    | Dv_nnrc_core (Dv_nnrc_core_to_camp vdbindings dv) => (L_nnrc_core, Some (Dv_camp dv))
    | Dv_nnrc (Dv_nnrc_stop) => (L_nnrc, None)
    | Dv_nnrc (Dv_nnrc_to_nnrc_core dv) => (L_nnrc, Some (Dv_nnrc_core dv))
    | Dv_nnrc (Dv_nnrc_to_nnrs inputs dv) => (L_nnrc, Some (Dv_nnrs dv))
    | Dv_nnrc (Dv_nnrc_to_nnrcmr vinit vdbindings dv) => (L_nnrc, Some (Dv_nnrcmr dv))
    | Dv_nnrc (Dv_nnrc_to_dnnrc inputs_loc dv) => (L_nnrc, Some (Dv_dnnrc dv))
    | Dv_nnrc (Dv_nnrc_to_javascript dv) => (L_nnrc, Some (Dv_javascript dv))
    | Dv_nnrc (Dv_nnrc_to_java name java_imports dv) => (L_nnrc, Some (Dv_java dv))
    | Dv_nnrc (Dv_nnrc_optim opc dv) => (L_nnrc, Some (Dv_nnrc dv))
    | Dv_nnrs_core (Dv_nnrs_core_to_nnrs dv) => (L_nnrs_core, Some (Dv_nnrs dv))
    | Dv_nnrs_core (Dv_nnrs_core_stop) => (L_nnrs_core, None)
    | Dv_nnrs (Dv_nnrs_stop) => (L_nnrs, None)
    | Dv_nnrs (Dv_nnrs_to_nnrs_imp dv) => (L_nnrs, Some (Dv_nnrs_imp dv))
    | Dv_nnrs_imp (Dv_nnrs_imp_stop) => (L_nnrs_imp, None)
    | Dv_nnrs_imp (Dv_nnrs_imp_optim _ dv) => (L_nnrs_imp, Some (Dv_nnrs_imp dv))
    | Dv_nnrs_imp (Dv_nnrs_imp_to_js_ast inputs dv) => (L_nnrs_imp, Some (Dv_js_ast dv))
    | Dv_nnrs_imp (Dv_nnrs_imp_to_imp_qcert _ dv) => (L_nnrs_imp, Some (Dv_imp_qcert dv))
    | Dv_imp_qcert (Dv_imp_qcert_stop) => (L_imp_qcert, None)
    | Dv_imp_qcert (Dv_imp_qcert_to_imp_json dv) => (L_imp_qcert, Some (Dv_imp_json dv))
    | Dv_imp_json (Dv_imp_json_stop) => (L_imp_json, None)
    | Dv_imp_json (Dv_imp_json_to_js_ast dv) => (L_imp_json, Some (Dv_js_ast dv))
    | Dv_nnrcmr (Dv_nnrcmr_stop) => (L_nnrcmr, None)
    | Dv_nnrcmr (Dv_nnrcmr_to_spark_rdd name dv) => (L_nnrcmr, Some (Dv_spark_rdd dv))
    | Dv_nnrcmr (Dv_nnrcmr_to_nnrc dv) => (L_nnrcmr, Some (Dv_nnrc dv))
    | Dv_nnrcmr (Dv_nnrcmr_to_dnnrc dv) => (L_nnrcmr, Some (Dv_dnnrc dv))
    | Dv_nnrcmr (Dv_nnrcmr_optim dv) => (L_nnrcmr, Some (Dv_nnrcmr dv))
    | Dv_dnnrc (Dv_dnnrc_stop) => (L_dnnrc, None)
    | Dv_dnnrc (Dv_dnnrc_to_dnnrc_typed rtype dv) => (L_dnnrc_typed, Some (Dv_dnnrc_typed dv))
    | Dv_dnnrc_typed (Dv_dnnrc_typed_stop) => (L_dnnrc_typed, None)
    | Dv_dnnrc_typed (Dv_dnnrc_typed_optim dv) => (L_dnnrc_typed, Some (Dv_dnnrc_typed dv))
    | Dv_dnnrc_typed (Dv_dnnrc_typed_to_spark_df rtype _ dv) => (L_dnnrc_typed, Some (Dv_spark_df dv))
    | Dv_js_ast (Dv_js_ast_stop) => (L_js_ast, None)
    | Dv_js_ast (Dv_js_ast_to_javascript dv) => (L_js_ast, Some (Dv_javascript dv))
    | Dv_javascript (Dv_javascript_stop) => (L_javascript, None)
    | Dv_java (Dv_java_stop) => (L_java, None)
    | Dv_spark_rdd (Dv_spark_rdd_stop) => (L_spark_rdd, None)
    | Dv_spark_df (Dv_spark_df_stop) => (L_spark_df, None)
    | Dv_error err => (L_error err, None)
    end.

  Lemma pop_transition_lt_len dv lang dv' :
    pop_transition dv = (lang, Some dv') ->
    driver_length dv' < driver_length dv.
  Proof.
    destruct dv; simpl;
      try solve [match_destr; inversion 1; subst; simpl; auto 2 | inversion 1].
  Qed.

  Function target_language_of_driver dv { measure driver_length dv } :=
    match pop_transition dv with
    | (lang, None) => lang
    | (_, Some dv) => target_language_of_driver dv
    end.
  Proof.
    intros.
    eapply pop_transition_lt_len; eauto.
  Defined.

  Lemma target_language_of_driver_is_postfix_javascript:
      (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_javascript dv))) (Dv_javascript dv)).
  Proof.
    destruct dv.
    reflexivity.
  Qed.

  Lemma target_language_of_driver_is_postfix_js_ast:
      (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_js_ast dv))) (Dv_js_ast dv)).
  Proof.
    destruct dv;
    try reflexivity;
    rewrite target_language_of_driver_equation;
    simpl.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 nil
                 EmptyString
                 nil) (lang:=L_js_ast)
      ; [ eapply target_language_of_driver_is_postfix_javascript | | ]
      ; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_java:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_java dv))) (Dv_java dv)).
  Proof.
    destruct dv.
    reflexivity.
  Qed.

  Lemma target_language_of_driver_is_postfix_spark_rdd:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_spark_rdd dv))) (Dv_spark_rdd dv)).
  Proof.
    destruct dv.
    reflexivity.
  Qed.

  Lemma target_language_of_driver_is_postfix_spark_df:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_spark_df dv))) (Dv_spark_df dv)).
  Proof.
    destruct dv.
    reflexivity.
  Qed.

  Lemma target_language_of_driver_is_postfix_dnnrc_typed:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_dnnrc_typed dv))) (Dv_dnnrc_typed dv)).
  Proof.
    induction dv; simpl
    ; try reflexivity
    ; rewrite target_language_of_driver_equation
    ; simpl.
    - eapply is_postfix_plus_one with
      (config:=trivial_driver_config) (lang:=L_dnnrc_typed)
      ; [eassumption | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 s
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 (constants_config_of_tdbindings t)
                 EmptyString
                 nil) (lang:=L_dnnrc_typed)
      ; [ eapply target_language_of_driver_is_postfix_spark_df | | ]
      ; simpl; trivial.
      rewrite (constants_config_of_tdbindings_merges t); reflexivity.
  Qed.

  Lemma target_language_of_driver_is_postfix_dnnrc:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_dnnrc dv))) (Dv_dnnrc dv)).
  Proof.
    destruct dv; simpl.
    - reflexivity.
    - rewrite target_language_of_driver_equation
      ; simpl.
      eapply is_postfix_plus_one with
               (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 (constants_config_of_tdbindings t)
                 EmptyString
                 nil) (lang:=L_dnnrc)
      ; [eapply target_language_of_driver_is_postfix_dnnrc_typed | | ]; simpl; trivial.
      rewrite (constants_config_of_tdbindings_merges t); reflexivity.
  Qed.

  Lemma target_language_of_driver_is_postfix_imp_json:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_imp_json dv))) (Dv_imp_json dv)).
  Proof.
    induction dv; simpl.
    - reflexivity.
    - rewrite target_language_of_driver_equation
      ; simpl.
      eapply is_postfix_plus_one with
               (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 nil
                 EmptyString
                 nil) (lang:=L_imp_json)
      ; [eapply target_language_of_driver_is_postfix_js_ast | | ]; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_imp_qcert:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_imp_qcert dv))) (Dv_imp_qcert dv)).
  Proof.
    induction dv; simpl.
    - reflexivity.
    - rewrite target_language_of_driver_equation
      ; simpl.
      eapply is_postfix_plus_one with
               (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 nil
                 EmptyString
                 nil) (lang:=L_imp_qcert)
      ; [eapply target_language_of_driver_is_postfix_imp_json | | ]; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_nnrs_imp:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nnrs_imp dv))) (Dv_nnrs_imp dv)).
  Proof.
    induction dv; simpl.
    - reflexivity.
    - rewrite target_language_of_driver_equation
      ; simpl.
      eapply is_postfix_plus_one with
               (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 nil
                 EmptyString
                 ((existT _ L_nnrs_imp o)::nil)) (lang:=L_nnrs_imp)
      ; simpl; eauto.
    - rewrite target_language_of_driver_equation
      ; simpl.
      eapply is_postfix_plus_one with
               (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 (one_constant_config_of_avoid_list l)
                 EmptyString
                 nil) (lang:=L_nnrs_imp)
      ; [eapply target_language_of_driver_is_postfix_js_ast | | ]; simpl; trivial.
      rewrite vars_of_one_constant_config_of_avoid_list; reflexivity.
    - rewrite target_language_of_driver_equation
      ; simpl.
      eapply is_postfix_plus_one with
               (config:=mkDvConfig
                 s
                 s
                 EmptyString
                 nil
                 EmptyString
                 nil
                 EmptyString
                 nil) (lang:=L_nnrs_imp)
      ; [eapply target_language_of_driver_is_postfix_imp_qcert | | ]; simpl; trivial.
  Qed.


  Lemma target_language_of_driver_is_postfix_nnrs:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nnrs dv))) (Dv_nnrs dv)).
  Proof.
    destruct dv; simpl.
    - reflexivity.
    - rewrite target_language_of_driver_equation
      ; simpl.
      eapply is_postfix_plus_one with
               (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 nil
                 EmptyString
                 nil) (lang:=L_nnrs)
      ; [eapply target_language_of_driver_is_postfix_nnrs_imp | | ]; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_nnrs_core:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nnrs_core dv))) (Dv_nnrs_core dv)).
  Proof.
    destruct dv; simpl.
    - reflexivity.
    - rewrite target_language_of_driver_equation
      ; simpl.
      eapply is_postfix_plus_one with
           (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 nil
                 EmptyString
                 nil) (lang:=L_nnrs_core).
      + eapply target_language_of_driver_is_postfix_nnrs.
      + simpl; trivial.
      + simpl; trivial.
  Qed.

  Lemma pick_tdbindings_from_vdbindings (v:vdbindings):
    exists tdb:tdbindings,
      (vdbindings_of_tdbindings tdb = v).
  Proof.
    revert v.
    induction v.
    - exists nil; reflexivity.
    - destruct a.
      destruct d.
      + elim IHv; intros.
        exists ((s,Tlocal Unit) :: x).
        simpl.
        rewrite H; reflexivity.
      + elim IHv; intros.
        exists ((s,Tdistr Unit) :: x).
        simpl.
        rewrite H; reflexivity.
  Qed.

  Lemma target_language_of_driver_is_postfix_cnd:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_camp dv)))
                                  (Dv_camp dv))
    /\  (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nra dv)))
                                      (Dv_nra dv))
    /\  (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nraenv_core dv)))
                                      (Dv_nraenv_core dv))
    /\  (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nraenv dv)))
                                      (Dv_nraenv dv))
    /\  (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nnrc_core dv)))
                                      (Dv_nnrc_core dv))
    /\  (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nnrc dv)))
                                      (Dv_nnrc dv))
    (* /\  (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nnrs dv))) *)
    (*                                   (Dv_nnrs dv)) *)
    /\  (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nnrcmr dv)))
                                      (Dv_nnrcmr dv)).
  Proof.
    apply cnd_combined_ind
    ; simpl; try reflexivity; intros
    ; rewrite target_language_of_driver_equation
    ; simpl
    ; try solve [
            (eapply is_postfix_plus_one with
               (config:=trivial_driver_config) (lang:=L_camp);
             [eassumption | | ]; simpl; trivial)
          | (eapply is_postfix_plus_one with
               (config:=trivial_driver_config) (lang:=L_nra);
             [eassumption | | ]; simpl; trivial)
          | (eapply is_postfix_plus_one with
               (config:=trivial_driver_config) (lang:=L_nraenv_core);
             [eassumption | | ]; simpl; trivial)
          | (eapply is_postfix_plus_one with
               (config:=trivial_driver_config) (lang:=L_nraenv);
             [eassumption | | ]; simpl; trivial)
          | (eapply is_postfix_plus_one with
               (config:=trivial_driver_config) (lang:=L_nnrc_core);
             [eassumption | | ]; simpl; trivial)
          | (eapply is_postfix_plus_one with
               (config:=trivial_driver_config) (lang:=L_nnrc);
             [eassumption | | ]; simpl; trivial)
          (* | (eapply is_postfix_plus_one with *)
          (*      (config:=trivial_driver_config) (lang:=L_nnrs); *)
          (*    [eassumption | | ]; simpl; trivial) *)
          | (eapply is_postfix_plus_one with
               (config:=trivial_driver_config) (lang:=L_nnrcmr);
             [eassumption | | ]; simpl; trivial)
          ].
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 nil
                 EmptyString
                 ((existT _ L_nraenv o)::nil)) (lang:=L_nraenv);
        [eassumption | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 (one_constant_config_of_avoid_list l)
                 EmptyString
                 nil) (lang:=L_nnrc_core);
        [eapply target_language_of_driver_is_postfix_nnrs_core | | ]; simpl; trivial.
      simpl.
      subst.
      rewrite vars_of_one_constant_config_of_avoid_list; reflexivity.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 (one_constant_config_of_avoid_list l)
                 EmptyString
                 nil) (lang:=L_nnrc_core);
        [eassumption | | ]; simpl; trivial.
      (* unfold vars_of_constants_config in *; simpl. *)
      rewrite one_constant_config_of_avoid_list_extracts; reflexivity.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 nil
                 EmptyString
                 ((existT _ L_nnrc o)::nil)) (lang:=L_nnrc);
        [eassumption | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 (one_constant_config_of_avoid_list l)
                 EmptyString
                 nil) (lang:=L_nnrc);
        [eapply target_language_of_driver_is_postfix_nnrs | | ]; simpl; trivial.
      simpl.
      subst.
      rewrite vars_of_one_constant_config_of_avoid_list; reflexivity.
    - generalize (pick_tdbindings_from_vdbindings v0); intros.
      elim H0; intros.
      eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 v
                 (constants_config_of_tdbindings x)
                 EmptyString
                 nil) (lang:=L_nnrc);
        [eassumption | | ]; simpl; trivial.
      subst.
      rewrite vdbindings_of_constants_config_commutes; reflexivity.
    - generalize (pick_tdbindings_from_vdbindings v); intros.
      elim H; intros.
      eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 (constants_config_of_tdbindings x)
                 EmptyString
                 nil) (lang:=L_nnrc);
        [eapply target_language_of_driver_is_postfix_dnnrc | | ]; simpl; trivial.
      subst.
      rewrite vdbindings_of_constants_config_commutes; reflexivity.
    - eapply is_postfix_plus_one with
      (config:=trivial_driver_config) (lang:=L_nnrc);
        [eapply target_language_of_driver_is_postfix_javascript | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 s
                 nil
                 EmptyString
                 nil
                 s0
                 nil) (lang:=L_nnrc);
      [eapply target_language_of_driver_is_postfix_java | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 s
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 nil
                 EmptyString
                 nil) (lang:=L_nnrcmr);
        [eapply target_language_of_driver_is_postfix_spark_rdd | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 EmptyString
                 nil
                 EmptyString
                 nil
                 EmptyString
                 nil) (lang:=L_nnrcmr);
        [eapply target_language_of_driver_is_postfix_dnnrc | | ]; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_camp:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_camp dv))) (Dv_camp dv)).
  Proof.
    apply target_language_of_driver_is_postfix_cnd.
  Qed.

  Lemma target_language_of_driver_is_postfix_nra:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nra dv))) (Dv_nra dv)).
  Proof.
    apply target_language_of_driver_is_postfix_cnd.
  Qed.

  Lemma target_language_of_driver_is_postfix_nraenv_core:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nraenv_core dv))) (Dv_nraenv_core dv)).
  Proof.
    apply target_language_of_driver_is_postfix_cnd.
  Qed.

  Lemma target_language_of_driver_is_postfix_nraenv:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nraenv dv))) (Dv_nraenv dv)).
  Proof.
    apply target_language_of_driver_is_postfix_cnd.
  Qed.

  Lemma target_language_of_driver_is_postfix_nnrc_core:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nnrc_core dv))) (Dv_nnrc_core dv)).
  Proof.
    apply target_language_of_driver_is_postfix_cnd.
  Qed.

  Lemma target_language_of_driver_is_postfix_nnrc:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nnrc dv))) (Dv_nnrc dv)).
  Proof.
    apply target_language_of_driver_is_postfix_cnd.
  Qed.

  Lemma target_language_of_driver_is_postfix_nnrcmr:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nnrcmr dv))) (Dv_nnrcmr dv)).
  Proof.
    apply target_language_of_driver_is_postfix_cnd.
  Qed.

  Lemma target_language_of_driver_is_postfix_camp_rule:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_camp_rule dv))) (Dv_camp_rule dv)).
  Proof.
    destruct dv; simpl; try reflexivity
    ; rewrite target_language_of_driver_equation
    ; simpl
    ;  try solve [eapply is_postfix_plus_one with
                  (config:=trivial_driver_config) (lang:=L_camp_rule);
                  [apply target_language_of_driver_is_postfix_cnd | | ]; simpl; trivial].
  Qed.

  Lemma target_language_of_driver_is_postfix_tech_rule:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_tech_rule dv))) (Dv_tech_rule dv)).
  Proof.
    destruct dv; simpl; try reflexivity
    ; rewrite target_language_of_driver_equation
    ; simpl.
    eapply is_postfix_plus_one with
    (config:=trivial_driver_config) (lang:=L_tech_rule);
      [apply target_language_of_driver_is_postfix_camp_rule | | ]; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_designer_rule:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_designer_rule dv))) (Dv_designer_rule dv)).
  Proof.
    destruct dv; simpl; try reflexivity
    ; rewrite target_language_of_driver_equation
    ; simpl.
    eapply is_postfix_plus_one with
    (config:=trivial_driver_config) (lang:=L_designer_rule);
      [apply target_language_of_driver_is_postfix_camp_rule | | ]; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_sql:
    (forall o, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_sql o))) (Dv_sql o)).
  Proof.
    destruct o; simpl; try reflexivity
    ; rewrite target_language_of_driver_equation
    ; simpl.
    eapply is_postfix_plus_one with
    (config:=trivial_driver_config) (lang:=L_sql);
      [apply target_language_of_driver_is_postfix_nraenv | | ]; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_sqlpp:
    (forall o, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_sqlpp o))) (Dv_sqlpp o)).
  Proof.
    destruct o; simpl; try reflexivity
    ; rewrite target_language_of_driver_equation
    ; simpl.
    eapply is_postfix_plus_one with
    (config:=trivial_driver_config) (lang:=L_sqlpp);
      [apply target_language_of_driver_is_postfix_nraenv | | ]; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_oql:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_oql dv))) (Dv_oql dv)).
  Proof.
    destruct dv; simpl; try reflexivity
    ; rewrite target_language_of_driver_equation
    ; simpl.
    eapply is_postfix_plus_one with
    (config:=trivial_driver_config) (lang:=L_oql);
      [apply target_language_of_driver_is_postfix_nraenv | | ]; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_lambda_nra:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_lambda_nra dv))) (Dv_lambda_nra dv)).
  Proof.
    destruct dv; simpl; try reflexivity
    ; rewrite target_language_of_driver_equation
    ; simpl.
    eapply is_postfix_plus_one with
    (config:=trivial_driver_config) (lang:=L_lambda_nra);
      [apply target_language_of_driver_is_postfix_nraenv | | ]; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix:
    forall dv,
      no_dv_error dv ->
      let target := target_language_of_driver dv in
      is_postfix_driver (driver_of_language target) dv.
  Proof.
    Hint Resolve
         target_language_of_driver_is_postfix_js_ast
         target_language_of_driver_is_postfix_javascript
         target_language_of_driver_is_postfix_java
         target_language_of_driver_is_postfix_spark_rdd
         target_language_of_driver_is_postfix_spark_df
         target_language_of_driver_is_postfix_dnnrc_typed
         target_language_of_driver_is_postfix_dnnrc
         target_language_of_driver_is_postfix_camp
         target_language_of_driver_is_postfix_nra
         target_language_of_driver_is_postfix_nraenv_core
         target_language_of_driver_is_postfix_nraenv
         target_language_of_driver_is_postfix_nnrc_core
         target_language_of_driver_is_postfix_nnrc
         target_language_of_driver_is_postfix_nnrs_core
         target_language_of_driver_is_postfix_nnrs
         target_language_of_driver_is_postfix_nnrs_imp
         target_language_of_driver_is_postfix_imp_qcert
         target_language_of_driver_is_postfix_imp_json
         target_language_of_driver_is_postfix_nnrcmr
         target_language_of_driver_is_postfix_camp_rule
         target_language_of_driver_is_postfix_tech_rule
         target_language_of_driver_is_postfix_designer_rule
         target_language_of_driver_is_postfix_oql
         target_language_of_driver_is_postfix_sql
         target_language_of_driver_is_postfix_sqlpp
         target_language_of_driver_is_postfix_lambda_nra
    : postfix_hints.
    simpl.
    destruct dv; auto with postfix_hints.
    contradiction.
  Qed.

  Lemma push_translation_is_postfix:
    forall config lang dv,
      let dv' := push_translation config lang dv in
      no_dv_error dv' ->
      is_postfix_driver dv dv'.
  Proof.
    intros config lang dv.
    simpl.
    apply (is_postfix_plus_one dv dv config lang);
      reflexivity.
  Qed.

  Lemma driver_of_rev_path_app config dv rev_path1 rev_path2 :
    driver_of_rev_path config dv (rev_path1 ++ rev_path2) =
    driver_of_rev_path config (driver_of_rev_path config dv rev_path1) rev_path2.
  Proof.
    revert rev_path2 dv.
    induction rev_path1; simpl; trivial.
  Qed.

  Lemma driver_of_rev_path_completeness:
    forall dv dv',
    forall config,
      is_driver_config config dv ->
      is_postfix_driver dv' dv ->
        exists rev_path,
          driver_of_rev_path config dv' rev_path = dv.
  Proof.
    intros dv dv' config H_config.
    induction 1.
    - subst. exists nil; trivial.
    - intros.
      destruct (IHis_postfix_driver).
      + rewrite <- H0 in *; clear H0.
        apply (is_driver_config_trans config (push_translation config0 lang dv)); try assumption.
        apply push_translation_is_postfix.
        assumption.
      + exists (x++lang::nil).
        rewrite driver_of_rev_path_app.
        rewrite H2.
        rewrite <- H0 in *; clear H0.
        simpl.
        language_cases (destruct lang) Case;
          simpl; try reflexivity;
            destruct dv; simpl; try reflexivity;
              simpl in H_config.
        * destruct (H_config (Dv_nraenv (Dv_nraenv_optim (get_optim_config L_nraenv (comp_optim_config config0)) n)));
          reflexivity.
        * destruct (H_config ((Dv_nnrc_core (Dv_nnrc_core_to_camp (List.map fst (vdbindings_of_constants_config (comp_constants config0))) c))));
            reflexivity.
        * destruct (H_config (Dv_nnrc_core
       (Dv_nnrc_core_to_nnrs_core (vars_of_constants_config (comp_constants config0)) n)))
          ; reflexivity.
        * destruct (H_config (Dv_nnrc (Dv_nnrc_optim (get_optim_config L_nnrc (comp_optim_config config0)) n)));
          reflexivity.
        * destruct (H_config (Dv_nnrc (Dv_nnrc_to_nnrs (vars_of_constants_config (comp_constants config0)) n)));
            try reflexivity.
        * destruct (H_config (Dv_nnrc (Dv_nnrc_to_nnrcmr (comp_mr_vinit config0) (vdbindings_of_constants_config (comp_constants config0)) n)));
            try reflexivity.
          rewrite H0; rewrite H3; reflexivity.
        * destruct (H_config (Dv_nnrc (Dv_nnrc_to_dnnrc (vdbindings_of_constants_config (comp_constants config0)) d)));
            reflexivity.
        * destruct (H_config (Dv_nnrc (Dv_nnrc_to_java (comp_class_name config0) (comp_java_imports config0) j)));
            try reflexivity.
          rewrite H0; rewrite H3; reflexivity.
        * destruct (H_config (Dv_nnrs_imp (Dv_nnrs_imp_optim (get_optim_config L_nnrs_imp (comp_optim_config config0)) n)))
          ; try reflexivity.
        * destruct (H_config (Dv_nnrs_imp (Dv_nnrs_imp_to_imp_qcert config0.(comp_qname_lowercase) i)));
            try reflexivity.
        * destruct (H_config (Dv_nnrs_imp (Dv_nnrs_imp_to_js_ast (vars_of_constants_config (comp_constants config0)) j)));
            try reflexivity.
        * destruct (H_config (Dv_nnrcmr (Dv_nnrcmr_to_spark_rdd (comp_qname config0) s)));
            reflexivity.
        * destruct (H_config (Dv_dnnrc (Dv_dnnrc_to_dnnrc_typed (tdbindings_of_constants_config (comp_constants config0)) d)));
            reflexivity.
        * destruct (H_config (Dv_dnnrc_typed
                                (Dv_dnnrc_typed_to_spark_df (tdbindings_of_constants_config (comp_constants config0)) (comp_qname config0) s)));
            try reflexivity.
          rewrite H0; rewrite H3; reflexivity.
  Qed.


  Theorem driver_of_path_completeness:
    forall dv,
    forall config,
      no_dv_error dv ->
      is_driver_config config dv ->
      exists path,
        driver_of_path config path = dv.
  Proof.
    intros dv config H_no_dv_error H_dv_config.
    unfold driver_of_path.
    assert (is_postfix_driver (driver_of_language (target_language_of_driver dv)) dv) as Hpost;
      [ apply (target_language_of_driver_is_postfix dv H_no_dv_error) | ].
    generalize (driver_of_rev_path_completeness dv ((driver_of_language (target_language_of_driver dv))) config H_dv_config Hpost).
    intros H_exists.
    destruct H_exists.
    exists (List.rev ((target_language_of_driver dv) :: x)).
    rewrite List.rev_involutive.
    assumption.
  Qed.

  End CompDriverConfig.


  (** Paths builder *)
  Section CompPaths.
    Local Open Scope string_scope.

    Definition get_path_from_source_target (source:language) (target:language) : list language :=
      match source, target with
      (* From camp_rule: *)
      | L_camp_rule, L_camp_rule =>
        L_camp_rule
          :: nil
      | L_camp_rule, L_camp =>
        L_camp_rule
          :: L_camp
          :: nil
      | L_camp_rule, L_nra =>
        L_camp_rule
          :: L_camp
          :: L_nra
          :: nil
      | L_camp_rule, L_nraenv_core =>
        L_camp_rule
          :: L_camp
          :: L_nraenv_core
          :: nil
      | L_camp_rule, L_nraenv =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_camp_rule, L_nnrc_core =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_camp_rule, L_nnrc =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_camp_rule, L_javascript =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_camp_rule, L_java =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_camp_rule, L_nnrs =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_camp_rule, L_nnrs_core =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_camp_rule, L_nnrs_imp =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_camp_rule, L_imp_qcert =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_camp_rule, L_imp_json =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_camp_rule, L_js_ast =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_camp_rule, L_nnrcmr =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_camp_rule, L_spark_rdd =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_camp_rule, L_dnnrc =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_camp_rule, L_dnnrc_typed =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_camp_rule, L_spark_df =>
        L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From tech_rule: *)
      | L_tech_rule, L_tech_rule =>
        L_tech_rule
          :: nil
      | L_tech_rule, L_camp_rule =>
        L_tech_rule
          :: L_camp_rule
          :: nil
      | L_tech_rule, L_camp =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: nil
      | L_tech_rule, L_nra =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nra
          :: nil
      | L_tech_rule, L_nraenv_core =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv_core
          :: nil
      | L_tech_rule, L_nraenv =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_tech_rule, L_nnrc_core =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_tech_rule, L_nnrc =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_tech_rule, L_javascript =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_tech_rule, L_java =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_tech_rule, L_nnrs =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_tech_rule, L_nnrs_core =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_tech_rule, L_nnrs_imp =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_tech_rule, L_imp_qcert =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_tech_rule, L_imp_json =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_tech_rule, L_js_ast =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_tech_rule, L_nnrcmr =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_tech_rule, L_spark_rdd =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_tech_rule, L_dnnrc =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_tech_rule, L_dnnrc_typed =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_tech_rule, L_spark_df =>
        L_tech_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From designer_rule: *)
      | L_designer_rule, L_designer_rule =>
        L_designer_rule
          :: nil
      | L_designer_rule, L_camp_rule =>
        L_designer_rule
          :: L_camp_rule
          :: nil
      | L_designer_rule, L_camp =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: nil
      | L_designer_rule, L_nra =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nra
          :: nil
      | L_designer_rule, L_nraenv_core =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv_core
          :: nil
      | L_designer_rule, L_nraenv =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_designer_rule, L_nnrc_core =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_designer_rule, L_nnrc =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_designer_rule, L_javascript =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_designer_rule, L_java =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_designer_rule, L_nnrs =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_designer_rule, L_nnrs_core =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_designer_rule, L_nnrs_imp =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_designer_rule, L_imp_qcert =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_designer_rule, L_imp_json =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_designer_rule, L_js_ast =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_designer_rule, L_nnrcmr =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_designer_rule, L_spark_rdd =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_designer_rule, L_dnnrc =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_designer_rule, L_dnnrc_typed =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_designer_rule, L_spark_df =>
        L_designer_rule
          :: L_camp_rule
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From camp: *)
      | L_camp, L_camp =>
        L_camp
          :: nil
      | L_camp, L_nra =>
        L_camp
          :: L_nra
          :: nil
      | L_camp, L_nraenv_core =>
        L_camp
          :: L_nraenv_core
          :: nil
      | L_camp, L_nraenv =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_camp, L_nnrc_core =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_camp, L_nnrc =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_camp, L_javascript =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_camp, L_java =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_camp, L_nnrs =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_camp, L_nnrs_core =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_camp, L_nnrs_imp =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_camp, L_imp_qcert =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_camp, L_imp_json =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_camp, L_js_ast =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_camp, L_nnrcmr =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_camp, L_spark_rdd =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_camp, L_dnnrc =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_camp, L_dnnrc_typed =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_camp, L_spark_df =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From oql: *)
      | L_oql, L_oql =>
        L_oql
          :: nil
      | L_oql, L_nraenv =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_oql, L_nraenv_core =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nraenv_core
          :: nil
      | L_oql, L_nra =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nraenv_core
          :: L_nra
          :: nil
      | L_oql, L_nnrc =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_oql, L_nnrc_core =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_oql, L_camp =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: nil
      | L_oql, L_javascript =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_oql, L_java =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_oql, L_nnrs =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_oql, L_nnrs_core =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_oql, L_nnrs_imp =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_oql, L_imp_qcert =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_oql, L_imp_json =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_oql, L_js_ast =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_oql, L_nnrcmr =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_oql, L_spark_rdd =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_oql, L_dnnrc =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_oql, L_dnnrc_typed =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_oql, L_spark_df =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From sql: *)
      | L_sql, L_sql =>
        L_sql
          :: nil
      | L_sql, L_nraenv =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_sql, L_nraenv_core =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nraenv_core
          :: nil
      | L_sql, L_nra =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nraenv_core
          :: L_nra
          :: nil
      | L_sql, L_nnrc_core =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_sql, L_nnrc =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_sql, L_camp =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: nil
      | L_sql, L_javascript =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_sql, L_java =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_sql, L_nnrs =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_sql, L_nnrs_core =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_sql, L_nnrs_imp =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_sql, L_imp_qcert =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_sql, L_imp_json =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_sql, L_js_ast =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_sql, L_nnrcmr =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_sql, L_spark_rdd =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_sql, L_dnnrc =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_sql, L_dnnrc_typed =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_sql, L_spark_df =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From sqlpp: *)
      | L_sqlpp, L_sqlpp =>
        L_sqlpp
          :: nil
      | L_sqlpp, L_nraenv =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_sqlpp, L_nraenv_core =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nraenv_core
          :: nil
      | L_sqlpp, L_nra =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nraenv_core
          :: L_nra
          :: nil
      | L_sqlpp, L_nnrc_core =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_sqlpp, L_nnrc =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_sqlpp, L_camp =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: nil
      | L_sqlpp, L_javascript =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_sqlpp, L_java =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_sqlpp, L_nnrs =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_sqlpp, L_nnrs_core =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_sqlpp, L_nnrs_imp =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_sqlpp, L_imp_qcert =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_sqlpp, L_imp_json =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_sqlpp, L_js_ast =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_sqlpp, L_nnrcmr =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_sqlpp, L_spark_rdd =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_sqlpp, L_dnnrc =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_sqlpp, L_dnnrc_typed =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_sqlpp, L_spark_df =>
        L_sqlpp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From lambda_nra: *)
      | L_lambda_nra, L_lambda_nra =>
        L_lambda_nra
          :: nil
      | L_lambda_nra, L_nraenv =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_lambda_nra, L_nraenv_core =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nraenv_core
          :: nil
      | L_lambda_nra, L_nra =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nraenv_core
          :: L_nra
          :: nil
      | L_lambda_nra, L_nnrc_core =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_lambda_nra, L_nnrc =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_lambda_nra, L_camp =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: nil
      | L_lambda_nra, L_javascript =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_lambda_nra, L_java =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_lambda_nra, L_nnrs =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_lambda_nra, L_nnrs_core =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_lambda_nra, L_nnrs_imp =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_lambda_nra, L_imp_qcert =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_lambda_nra, L_imp_json =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_lambda_nra, L_js_ast =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_lambda_nra, L_nnrcmr =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_lambda_nra, L_spark_rdd =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_lambda_nra, L_dnnrc =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_lambda_nra, L_dnnrc_typed =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_lambda_nra, L_spark_df =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From nra: *)
      | L_nra, L_nra =>
        L_nra
          :: nil
      | L_nra, L_nraenv_core =>
        L_nra
          :: L_nraenv_core
          :: nil
      | L_nra, L_nraenv =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_nra, L_nnrc =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_nra, L_nnrc_core =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_nra, L_camp =>
        L_nra
          :: L_nnrc_core
          :: L_camp
          :: nil
      | L_nra, L_javascript =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_nra, L_java =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_nra, L_nnrs =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_nra, L_nnrs_core =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_nra, L_nnrs_imp =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_nra, L_imp_qcert =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_nra, L_imp_json =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_nra, L_js_ast =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_nra, L_nnrcmr =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_nra, L_spark_rdd =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_nra, L_dnnrc =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_nra, L_dnnrc_typed =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_nra, L_spark_df =>
        L_nra
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From nraenv_core: *)
      | L_nraenv_core, L_nraenv_core =>
        L_nraenv_core
          :: nil
      | L_nraenv_core, L_nra =>
        L_nraenv_core
          :: L_nra
          :: nil
      | L_nraenv_core, L_nraenv =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_nraenv_core, L_nnrc =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_nraenv_core, L_nnrc_core =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_nraenv_core, L_camp =>
        L_nraenv_core
          :: L_nnrc_core
          :: L_camp
          :: nil
      | L_nraenv_core, L_javascript =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_nraenv_core, L_java =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_nraenv_core, L_nnrs =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_nraenv_core, L_nnrs_core =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_nraenv_core, L_nnrs_imp =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_nraenv_core, L_imp_qcert =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_nraenv_core, L_imp_json =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_nraenv_core, L_js_ast =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_nraenv_core, L_nnrcmr =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_nraenv_core, L_spark_rdd =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_nraenv_core, L_dnnrc =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_nraenv_core, L_dnnrc_typed =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_nraenv_core, L_spark_df =>
        L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From nraenv: *)
      | L_nraenv, L_nraenv =>
        L_nraenv
          :: L_nraenv
          :: nil
      | L_nraenv, L_nraenv_core =>
        L_nraenv
          :: L_nraenv
          :: L_nraenv_core
          :: nil
      | L_nraenv, L_nra =>
        L_nraenv
          :: L_nraenv
          :: L_nraenv_core
          :: L_nra
          :: nil
      | L_nraenv, L_nnrc =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_nraenv, L_nnrc_core =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_nraenv, L_camp =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: nil
      | L_nraenv, L_javascript =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_nraenv, L_java =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_nraenv, L_nnrs =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_nraenv, L_nnrs_core =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_nraenv, L_nnrs_imp =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_nraenv, L_imp_qcert =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_nraenv, L_imp_json =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_nraenv, L_js_ast =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_nraenv, L_nnrcmr =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_nraenv, L_spark_rdd =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_nraenv, L_dnnrc =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_nraenv, L_dnnrc_typed =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_nraenv, L_spark_df =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From nnrc: *)
      | L_nnrc_core, L_nnrc_core =>
        L_nnrc_core
          :: nil
      | L_nnrc_core, L_nnrc =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_nnrc_core, L_camp =>
        L_nnrc_core
          :: L_camp
          :: nil
      | L_nnrc_core, L_nraenv_core =>
        L_nnrc_core
          :: L_camp
          :: L_nraenv_core
          :: nil
      | L_nnrc_core, L_nraenv =>
        L_nnrc_core
          :: L_camp
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_nnrc_core, L_nra =>
        L_nnrc_core
          :: L_camp
          :: L_nra
          :: nil
      | L_nnrc_core, L_javascript =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_nnrc_core, L_java =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_nnrc_core, L_nnrs =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_nnrc_core, L_nnrs_core =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_nnrc_core, L_nnrs_imp =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_nnrc_core, L_imp_qcert =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_nnrc_core, L_imp_json =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_nnrc_core, L_js_ast =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_nnrc_core, L_nnrcmr =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_nnrc_core, L_spark_rdd =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_nnrc_core, L_dnnrc =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_nnrc_core, L_dnnrc_typed =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_nnrc_core, L_spark_df =>
        L_nnrc_core
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From nnrc: *)
      | L_nnrc, L_nnrc =>
        L_nnrc
          :: L_nnrc
          :: nil
      | L_nnrc, L_nnrc_core =>
        L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_nnrc, L_camp =>
        L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: nil
      | L_nnrc, L_nraenv_core =>
        L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: L_nraenv_core
          :: nil
      | L_nnrc, L_nraenv =>
        L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_nnrc, L_nra =>
        L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: L_nra
          :: nil
      | L_nnrc, L_javascript =>
        L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_nnrc, L_java =>
        L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_nnrc, L_nnrs =>
        L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_nnrc, L_nnrs_core =>
        L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_nnrc, L_nnrs_imp =>
        L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_nnrc, L_imp_qcert =>
        L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_nnrc, L_imp_json =>
        L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_nnrc, L_js_ast =>
        L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_nnrc, L_nnrcmr =>
        L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_nnrc, L_spark_rdd =>
        L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_nnrc, L_dnnrc =>
        L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: nil
      | L_nnrc, L_dnnrc_typed =>
        L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_nnrc, L_spark_df =>
        L_nnrc
          :: L_nnrc
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From nnrs: *)
      | L_nnrs, L_nnrs =>
        L_nnrs
          :: nil
      | L_nnrs, L_nnrs_imp =>
        L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_nnrs, L_imp_qcert =>
        L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_nnrs, L_imp_json =>
        L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_nnrs, L_js_ast =>
        L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_nnrs, L_javascript =>
        L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      (* From nnrs_core *)
      | L_nnrs_core, L_nnrs_core =>
        L_nnrs_core
          :: nil
      | L_nnrs_core, L_nnrs =>
        L_nnrs_core
          :: L_nnrs
          :: nil
      | L_nnrs_core, L_nnrs_imp =>
        L_nnrs_core
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_nnrs_core, L_imp_qcert =>
        L_nnrs_core
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_nnrs_core, L_imp_json =>
        L_nnrs_core
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_nnrs_core, L_js_ast =>
        L_nnrs_core
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_nnrs_core, L_javascript =>
        L_nnrs_core
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      (* From nnrs_imp: *)
      | L_nnrs_imp, L_nnrs_imp =>
        L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_nnrs_imp, L_imp_qcert =>
        L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_nnrs_imp, L_imp_json =>
        L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_nnrs_imp, L_js_ast =>
        L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_nnrs_imp, L_javascript =>
        L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      (* From imp_qcert: *)
      | L_imp_qcert, L_imp_qcert =>
        L_imp_qcert
          :: nil
      | L_imp_qcert, L_imp_json =>
        L_imp_qcert
          :: L_imp_json
          :: nil
      | L_imp_qcert, L_js_ast =>
        L_imp_qcert
          :: L_imp_json
          :: L_js_ast
          :: nil
      | L_imp_qcert, L_javascript =>
        L_imp_qcert
          :: L_imp_json
          :: L_js_ast
          :: L_javascript
          :: nil
      (* From imp_json: *)
      | L_imp_json, L_imp_json =>
        L_imp_json
          :: nil
      | L_imp_json, L_js_ast =>
        L_imp_json
          :: L_js_ast
          :: nil
      | L_imp_json, L_javascript =>
        L_imp_json
          :: L_js_ast
          :: L_javascript
          :: nil
      (* From nnrcmr: *)
      | L_nnrcmr, L_nnrcmr =>
        L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_nnrcmr, L_spark_rdd =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_spark_rdd
          :: nil
      | L_nnrcmr, L_dnnrc =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_dnnrc
          :: nil
      | L_nnrcmr, L_dnnrc_typed =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_nnrcmr, L_spark_df =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      | L_nnrcmr, L_nnrc_core =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc_core
          :: nil
      | L_nnrcmr, L_nnrc =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_nnrcmr, L_nnrs =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: nil
      | L_nnrcmr, L_nnrs_core =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_nnrs_core
          :: nil
      | L_nnrcmr, L_nnrs_imp =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: nil
      | L_nnrcmr, L_imp_qcert =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: nil
      | L_nnrcmr, L_imp_json =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_imp_qcert
          :: L_imp_json
          :: nil
      | L_nnrcmr, L_js_ast =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: nil
      | L_nnrcmr, L_javascript =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_nnrs
          :: L_nnrs_imp
          :: L_nnrs_imp
          :: L_js_ast
          :: L_javascript
          :: nil
      | L_nnrcmr, L_java =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_nnrcmr, L_camp =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: nil
      | L_nnrcmr, L_nraenv_core =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: L_nraenv_core
          :: nil
      | L_nnrcmr, L_nraenv =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: L_nraenv_core
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_nnrcmr, L_nra =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_nnrc_core
          :: L_camp
          :: L_nra
          :: nil
      (* From dnnrc: *)
      | L_dnnrc, L_dnnrc =>
        L_dnnrc
          :: nil
      | L_dnnrc, L_dnnrc_typed =>
        L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_dnnrc, L_spark_df =>
        L_dnnrc
          :: L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From dnnrc_typed: *)
      | L_dnnrc_typed, L_dnnrc_typed =>
        L_dnnrc_typed
          :: L_dnnrc_typed
          :: nil
      | L_dnnrc_typed, L_spark_df =>
        L_dnnrc_typed
          :: L_dnnrc_typed
          :: L_spark_df
          :: nil
      (* From javascript ast *)
      | L_js_ast, L_js_ast =>
        L_js_ast :: nil
      | L_js_ast, L_javascript =>
        L_js_ast
          :: L_javascript
          :: nil
      (* From javascript *)
      | L_javascript, L_javascript =>
        L_javascript :: nil
      (* From java *)
      | L_java, L_java =>
        L_java :: nil
      (* From spark_df *)
      | L_spark_df, L_spark_df =>
        L_spark_df :: nil
      (* From spark_rdd *)
      | L_spark_rdd, L_spark_rdd =>
        L_spark_rdd :: nil
      | _, _ =>
        let err :=
            "No default path defined from "++(name_of_language source)++" to "++(name_of_language target)
        in
        L_error err :: nil
      end.

    Proposition get_path_from_source_target_correct:
      forall source target,
        forall config,
          match get_path_from_source_target source target with
          | L_error _ :: nil => True
          | path =>
            match driver_of_path config path with
            | Dv_error _ => False
            | _ =>
              match path with
              | nil => False
              | source' :: _ =>
                match List.rev path with
                | nil => False
                | target' :: _ =>
                  (source = source') /\ (target = target')
                end
              end
            end
          end.
    Proof.
      destruct source; destruct target;
        intros; try solve [ simpl; split; reflexivity ].
    Qed.

    Definition exists_path_from_source_target source target
      := match get_path_from_source_target source target with
         | L_error _ :: nil => False
         | path => True
         end.

    Lemma exists_path_from_source_target_refl
          source :
      no_L_error source ->
      exists_path_from_source_target source source.
    Proof.
      unfold exists_path_from_source_target.
      destruct source; try solve [simpl; trivial].
    Qed.

    Lemma exists_path_from_source_target_trans
             source middle target:
      exists_path_from_source_target source middle ->
      exists_path_from_source_target middle target ->
      exists_path_from_source_target source target.
    Proof.
      unfold exists_path_from_source_target.
      case_eq source; case_eq target; simpl; trivial
      ; case_eq middle; simpl; try tauto.
    Qed.

    Global Instance exists_path_from_source_target_trans' :
      Transitive exists_path_from_source_target.
    Proof.
      red; intros.
      eapply exists_path_from_source_target_trans; eauto.
    Qed.

    Lemma exists_path_from_source_target_completeness_javascript :
        (forall dv,
            exists_path_from_source_target L_javascript (target_language_of_driver (Dv_javascript dv))).
    Proof.
      destruct dv
    ; simpl; try reflexivity; intros.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_javascript : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_java :
        (forall dv,
            exists_path_from_source_target L_java (target_language_of_driver (Dv_java dv))).
    Proof.
      destruct dv
    ; simpl; try reflexivity; intros.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_java : exists_path_hints.

    Ltac prove_exists_path_complete
      := simpl; try reflexivity; intros
         ; rewrite target_language_of_driver_equation
         ; simpl
         ; trivial
         ; try solve [etransitivity; eauto with exists_path_hints; reflexivity].

    Lemma exists_path_from_source_target_completeness_js_ast :
        (forall dv,
            exists_path_from_source_target L_js_ast (target_language_of_driver (Dv_js_ast dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_js_ast : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_imp_json :
      (forall dv,
          exists_path_from_source_target L_imp_json (target_language_of_driver (Dv_imp_json dv))).
    Proof.
      induction dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_imp_json : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_imp_qcert :
      (forall dv,
          exists_path_from_source_target L_imp_qcert (target_language_of_driver (Dv_imp_qcert dv))).
    Proof.
      induction dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_imp_qcert : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_nnrs_imp :
      (forall dv,
          exists_path_from_source_target L_nnrs_imp (target_language_of_driver (Dv_nnrs_imp dv))).
    Proof.
      induction dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_nnrs_imp : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_nnrs :
      (forall dv,
          exists_path_from_source_target L_nnrs (target_language_of_driver (Dv_nnrs dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_nnrs : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_nnrs_core :
      (forall dv,
          exists_path_from_source_target L_nnrs_core (target_language_of_driver (Dv_nnrs_core dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_nnrs_core : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_spark_df :
      (forall dv,
          exists_path_from_source_target L_spark_df (target_language_of_driver (Dv_spark_df dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_spark_df : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_dnnrc_typed :
      (forall dv,
          exists_path_from_source_target L_dnnrc_typed (target_language_of_driver (Dv_dnnrc_typed dv))).
    Proof.
      induction dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_dnnrc_typed : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_dnnrc :
      (forall dv,
          exists_path_from_source_target L_dnnrc (target_language_of_driver (Dv_dnnrc dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_dnnrc : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_spark_rdd :
      (forall dv,
          exists_path_from_source_target L_spark_rdd (target_language_of_driver (Dv_spark_rdd dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_spark_rdd : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_cnd :
        (forall dv,
            exists_path_from_source_target L_camp (target_language_of_driver (Dv_camp dv)))
        /\
        (forall dv,
            exists_path_from_source_target L_nra (target_language_of_driver (Dv_nra dv)))
        /\
        (forall dv,
            exists_path_from_source_target L_nraenv_core (target_language_of_driver (Dv_nraenv_core dv)))
        /\
        (forall dv,
            exists_path_from_source_target L_nraenv (target_language_of_driver (Dv_nraenv dv)))
        /\
        (forall dv,
            exists_path_from_source_target L_nnrc_core (target_language_of_driver (Dv_nnrc_core dv)))
        /\
        (forall dv,
            exists_path_from_source_target L_nnrc (target_language_of_driver (Dv_nnrc dv)))
        /\
        (forall dv,
            exists_path_from_source_target L_nnrcmr (target_language_of_driver (Dv_nnrcmr dv))).
  Proof.
    apply cnd_combined_ind; prove_exists_path_complete.
  Qed.

  Lemma exists_path_from_source_target_completeness_camp :
    (forall dv,
        exists_path_from_source_target L_camp (target_language_of_driver (Dv_camp dv))).
  Proof.
    apply exists_path_from_source_target_completeness_cnd.
  Qed.
  Lemma exists_path_from_source_target_completeness_nra:
    (forall dv,
        exists_path_from_source_target L_nra (target_language_of_driver (Dv_nra dv))).
  Proof.
    apply exists_path_from_source_target_completeness_cnd.
  Qed.
  Lemma exists_path_from_source_target_completeness_nraenv_core :
    (forall dv,
        exists_path_from_source_target L_nraenv_core (target_language_of_driver (Dv_nraenv_core dv))).
  Proof.
    apply exists_path_from_source_target_completeness_cnd.
  Qed.
  Lemma exists_path_from_source_target_completeness_nraenv :
    (forall dv,
        exists_path_from_source_target L_nraenv (target_language_of_driver (Dv_nraenv dv))).
  Proof.
    apply exists_path_from_source_target_completeness_cnd.
  Qed.
  Lemma exists_path_from_source_target_completeness_nnrc_core :
    (forall dv,
        exists_path_from_source_target L_nnrc_core (target_language_of_driver (Dv_nnrc_core dv))).
  Proof.
    apply exists_path_from_source_target_completeness_cnd.
  Qed.
  Lemma exists_path_from_source_target_completeness_nnrc :
    (forall dv,
        exists_path_from_source_target L_nnrc (target_language_of_driver (Dv_nnrc dv))).
  Proof.
    apply exists_path_from_source_target_completeness_cnd.
  Qed.
  Lemma exists_path_from_source_target_completeness_nnrcmr :
    (forall dv,
        exists_path_from_source_target L_nnrcmr (target_language_of_driver (Dv_nnrcmr dv))).
  Proof.
    apply exists_path_from_source_target_completeness_cnd.
  Qed.

  Hint Resolve exists_path_from_source_target_completeness_camp : exists_path_hints.
  Hint Resolve exists_path_from_source_target_completeness_nra : exists_path_hints.
  Hint Resolve exists_path_from_source_target_completeness_nraenv_core : exists_path_hints.
  Hint Resolve exists_path_from_source_target_completeness_nraenv : exists_path_hints.
  Hint Resolve exists_path_from_source_target_completeness_nnrc_core : exists_path_hints.
  Hint Resolve exists_path_from_source_target_completeness_nnrc : exists_path_hints.
  Hint Resolve exists_path_from_source_target_completeness_nnrcmr : exists_path_hints.

  Lemma exists_path_from_source_target_completeness_camp_rule :
    (forall dv,
        exists_path_from_source_target L_camp_rule (target_language_of_driver (Dv_camp_rule dv))).
  Proof.
    destruct dv; prove_exists_path_complete.
  Qed.

  Hint Resolve exists_path_from_source_target_completeness_camp_rule : exists_path_hints.

  Lemma exists_path_from_source_target_completeness_tech_rule :
    (forall dv,
        exists_path_from_source_target L_tech_rule (target_language_of_driver (Dv_tech_rule dv))).
  Proof.
    destruct dv; prove_exists_path_complete.
  Qed.

  Hint Resolve exists_path_from_source_target_completeness_tech_rule : exists_path_hints.

  Lemma exists_path_from_source_target_completeness_designer_rule :
    (forall dv,
        exists_path_from_source_target L_designer_rule (target_language_of_driver (Dv_designer_rule dv))).
  Proof.
    destruct dv; prove_exists_path_complete.
  Qed.

  Hint Resolve exists_path_from_source_target_completeness_designer_rule : exists_path_hints.

  Lemma exists_path_from_source_target_completeness_oql :
    (forall dv,
        exists_path_from_source_target L_oql (target_language_of_driver (Dv_oql dv))).
  Proof.
    destruct dv; prove_exists_path_complete.
  Qed.

  Hint Resolve exists_path_from_source_target_completeness_oql : exists_path_hints.

  Lemma exists_path_from_source_target_completeness_sql :
    (forall dv,
        exists_path_from_source_target L_sql (target_language_of_driver (Dv_sql dv))).
  Proof.
    destruct dv; prove_exists_path_complete.
  Qed.

  Hint Resolve exists_path_from_source_target_completeness_sql : exists_path_hints.

  Lemma exists_path_from_source_target_completeness_sqlpp :
    (forall dv,
        exists_path_from_source_target L_sqlpp (target_language_of_driver (Dv_sqlpp dv))).
  Proof.
    destruct dv; prove_exists_path_complete.
  Qed.

  Hint Resolve exists_path_from_source_target_completeness_sqlpp : exists_path_hints.

  Lemma exists_path_from_source_target_completeness_lambda_nra :
    (forall dv,
        exists_path_from_source_target L_lambda_nra (target_language_of_driver (Dv_lambda_nra dv))).
  Proof.
    destruct dv; prove_exists_path_complete.
  Qed.

  Hint Resolve exists_path_from_source_target_completeness_lambda_nra : exists_path_hints.

  Proposition get_path_from_source_target_completeness:
    forall dv,
      no_dv_error dv ->
      let source := language_of_driver dv in
      let target := target_language_of_driver dv in
      exists_path_from_source_target source target.
  Proof.
    destruct dv; simpl
    ;  auto with exists_path_hints.
  Qed.

  (* Comp *)
  (* XXX TODO : use driver *)
  Definition get_driver_from_source_target (conf: driver_config) (source:language) (target:language) : driver :=
    let path := get_path_from_source_target source target in
    driver_of_path conf path.

  (* Some macros, that aren't really just about source-target *)

  Definition compile_from_source_target (conf: driver_config) (source:language) (target:language) (q: query) : query :=
    let path := get_path_from_source_target source target in
      let dv := driver_of_path conf path in
      match List.rev (compile dv q) with
      | nil => Q_error "No compilation result!"
      | target :: _ => target
      end.

  (* Used in CompTest: *)
  Definition camp_rule_to_nraenv_optim (q: camp_rule) : nraenv :=
    nraenv_optim_default (nraenv_core_to_nraenv (camp_to_nraenv_core (camp_rule_to_camp q))).
  Definition camp_rule_to_nnrc_optim (q: camp_rule) : nnrc :=
    nnrc_optim_default (nraenv_to_nnrc (nraenv_optim_default (nraenv_core_to_nraenv (camp_to_nraenv_core (camp_rule_to_camp q))))).

  (* Used in CALib: *)
  Definition nraenv_optim_to_nnrc_optim (q:nraenv) : nnrc :=
    nnrc_optim_default (nraenv_to_nnrc (nraenv_optim_default q)).
  Definition nraenv_optim_to_nnrc_optim_to_dnnrc (inputs_loc:vdbindings) (q:nraenv) : dnnrc :=
    nnrc_to_dnnrc inputs_loc (nnrc_optim_default (nraenv_to_nnrc (nraenv_optim_default q))).
  Definition nraenv_optim_to_nnrc_optim_to_nnrcmr_optim (inputs_loc:vdbindings) (q:nraenv) : nnrcmr :=
    nnrcmr_optim (nnrc_to_nnrcmr init_vinit inputs_loc (nnrc_optim_default (nraenv_to_nnrc (nraenv_optim_default q)))).

  (* Used in queryTests: *)
  Definition camp_rule_to_nraenv_to_nnrc_optim (q:camp_rule) : nnrc :=
    nnrc_optim_default (nraenv_to_nnrc (nraenv_optim_default (nraenv_core_to_nraenv (camp_to_nraenv_core (camp_rule_to_camp q))))).
  Definition camp_rule_to_nraenv_to_nnrc_optim_to_dnnrc
             (inputs_loc:vdbindings) (q:camp_rule) : dnnrc :=
    nnrc_to_dnnrc inputs_loc (nnrc_optim_default (nraenv_to_nnrc (nraenv_optim_default (nraenv_core_to_nraenv (camp_to_nraenv_core (camp_rule_to_camp q)))))).
  Definition camp_rule_to_nraenv_to_nnrc_optim_to_javascript (q:camp_rule) : string :=
    nnrc_to_javascript (nnrc_optim_default (nraenv_to_nnrc (nraenv_optim_default (nraenv_core_to_nraenv (camp_to_nraenv_core (camp_rule_to_camp q)))))).
  Definition camp_rule_to_nnrcmr (inputs_loc:vdbindings) (q:camp_rule) : nnrcmr :=
    nnrcmr_optim (nnrc_to_nnrcmr init_vinit inputs_loc (camp_rule_to_nraenv_to_nnrc_optim q)).

  (* *)

  Definition get_source_from_path path :=
    match path with
    | lang :: _ => lang
    | nil => L_error "empty path"
    end.

  Definition get_target_from_path path :=
    match List.rev path with
    | lang :: _ => lang
    | nil => L_error "empty path"
    end.

  Lemma get_source_target_from_path_rev path :
    get_source_from_path path = get_target_from_path (List.rev path).
  Proof.
    unfold get_target_from_path.
    rewrite List.rev_involutive.
    reflexivity.
  Qed.

  Lemma get_target_source_from_path_rev path :
    get_target_from_path path = get_source_from_path (List.rev path).
  Proof.
    reflexivity.
  Qed.

  Definition remove_source_optim path :=
    match path with
    | L_camp_rule :: L_camp_rule :: path => L_camp_rule :: path
    | L_camp :: L_camp :: path => L_camp :: path
    | L_oql :: L_oql :: path => L_oql :: path
    | L_sql :: L_sql :: path => L_sql :: path
    | L_lambda_nra :: L_lambda_nra :: path => L_lambda_nra :: path
    | L_nra :: L_nra :: path => L_nra :: path
    | L_nraenv_core :: L_nraenv_core :: path => L_nraenv_core :: path
    | L_nraenv :: L_nraenv :: path => L_nraenv :: path
    | L_nnrc_core :: L_nnrc_core :: path => L_nnrc_core :: path
    | L_nnrc :: L_nnrc :: path => L_nnrc :: path
    | L_nnrcmr :: L_nnrcmr :: path => L_nnrcmr :: path
    | L_dnnrc :: L_dnnrc :: path => L_dnnrc :: path
    | L_dnnrc_typed :: L_dnnrc_typed :: path => L_dnnrc_typed :: path
    | L_js_ast :: L_js_ast :: path => L_js_ast :: path
    | L_javascript :: L_javascript :: path => L_javascript :: path
    | L_java :: L_java :: path => L_java :: path
    | L_spark_rdd :: L_spark_rdd :: path => L_spark_rdd :: path
    | L_spark_df :: L_spark_df :: path => L_spark_df :: path
    | _ => path
    end.

  Lemma remove_source_optim_correct path :
    let path' := remove_source_optim path in
    get_source_from_path path = get_source_from_path path' /\
    get_target_from_path path = get_target_from_path path'.
  Proof.
    simpl.
    split;
      unfold get_target_from_path;
      destruct path; simpl; try reflexivity;
      destruct l; simpl; try reflexivity;
      try solve [
        destruct path; try reflexivity;
        destruct l; simpl; try reflexivity;
        destruct (List.rev path); simpl; try reflexivity ].
  Qed.

  Definition remove_target_optim path :=
    List.rev (remove_source_optim (List.rev path)).

  Lemma remove_target_optim_correct path :
    let path' := remove_target_optim path in
    get_source_from_path path = get_source_from_path path' /\
    get_target_from_path path = get_target_from_path path'.
  Proof.
    simpl.
    rewrite (get_source_target_from_path_rev path).
    rewrite (get_source_target_from_path_rev (remove_target_optim path)).
    rewrite (get_target_source_from_path_rev path).
    rewrite (get_target_source_from_path_rev (remove_target_optim path)).
    unfold remove_target_optim.
    repeat rewrite List.rev_involutive.
    generalize (remove_source_optim_correct (List.rev path)); simpl; tauto.
  Qed.

  End CompPaths.

  Section Verified.
    Definition compile_nraenv_to_imp_qcert_verified (conf:driver_config) (q:query) : query :=
      let dv := driver_of_path conf (L_nraenv::L_nnrc::L_nnrc_core::L_nnrc::L_nnrs::L_nnrs_imp::L_imp_qcert::nil) in
      match List.rev (compile dv q) with
      | nil => Q_error "No compilation result!"
      | target :: _ => target
      end.

    Lemma compile_nraenv_to_imp_qcert_verified_yields_result conf q :
      exists q', compile_nraenv_to_imp_qcert_verified conf (Q_nraenv q) = Q_imp_qcert q'.
    Proof.
      unfold compile_nraenv_to_imp_qcert_verified.
      simpl.
      exists (nnrs_imp_to_imp_qcert (comp_qname_lowercase conf)
         (nnrs_to_nnrs_imp
            (nnrc_to_nnrs (vars_of_constants_config (comp_constants conf))
               (NNRCLet init_venv (NNRCConst (drec nil))
                  (NNRCLet init_vid (NNRCConst dunit)
                     (nnrc_to_nnrc_base (NRAEnvtoNNRC.nraenv_to_nnrc q init_vid init_venv))))))).
      reflexivity.
    Qed.

  End Verified.

End CompDriver.
