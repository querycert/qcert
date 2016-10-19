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

Section CompDriver.

  Require Import String.
  Require Import Morphisms.


  (* Basic *)
  Require Import BasicSystem.
  Require Import TypingRuntime.

  (* ASTs *)
  Require Import ODMGRuntime.
  Require Import SQL.
  Require Import LambdaAlg.
  Require Import CAMPRuntime.
  Require Import NRARuntime.
  Require Import NRAEnvRuntime.
  Require Import NNRCRuntime.
  Require Import NNRCMRRuntime.
  Require Import CloudantMR.
  Require Import DNNRC Dataset.

  (* Translations *)
  Require Import PatterntoNRAEnv RuletoNRAEnv OQLtoNRAEnv.
  Require Import RuletoNRA PatterntoNRA NRAtoNNRC NRAEnvtoNNRC.
  Require Import LambdaAlgtoNRAEnv.
  Require Import NNRCtoJavascript.
  Require Import NNRCtoJava.
  Require Import NNRCtoNNRCMR.
  Require Import NNRCtoPattern.
  Require Import NNRCMRtoNNRC.
  Require Import NNRCMRtoSpark.
  Require Import NNRCMRtoCloudant.
  Require Import NNRCMRtoDNNRC.
  Require Import CloudantMRtoJavascript.
  Require Import NNRCtoDNNRC.
  Require Import TDNRCInfer DNNRCtoScala DNNRCDatasetRewrites.

  (* Optimizations *)
  Require Import TOptimEnvFunc.
  Require Import TRewFunc.
  Require Import DNNRCDatasetRewrites.
  Require Import OptimizerLogger.

  (* Foreign Support *)
  Require Import ForeignToReduceOps.
  Require Import ForeignToSpark.
  Require Import ForeignCloudant ForeignToCloudant.
  Require Import ForeignToJavascript.
  Require Import ForeignToScala.
  Require Import ForeignCloudant.

  (* Compiler Driver *)
  Require Import CompLang CompEnv.

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
  Context {nraenv_logger:optimizer_logger string algenv}.
  Context {nnrc_logger:optimizer_logger string nrc}.
  Context {ftojs:foreign_to_javascript}.
  Context {ftos:foreign_to_scala}.
  Context {ftospark:foreign_to_spark}.

  (* Translation functions *)

  Definition rule_to_nraenv (q:rule) : nraenv := RuletoNRAEnv.translate_rule_to_algenv q.

  Definition rule_to_camp (q:rule) : camp := Rule.rule_to_pattern q.

  Definition rule_to_nra (q:rule) : nra := alg_of_rule q.

  Definition oql_to_nraenv (q:oql) : nraenv := OQLtoNRAEnv.translate_oql_to_algenv q.

  Definition sql_to_nraenv (q:sql) : nraenv := SQL.sql_to_nraenv q.

  Definition lambda_nra_to_nraenv (q:lambda_nra) := algenv_of_lalg q.

  Definition camp_to_nraenv (q:camp) : nraenv := PatterntoNRAEnv.translate_pat_to_algenv q.

  Definition camp_to_nra (q:camp) : nra := alg_of_pat q.

  Definition nraenv_optim (q: nraenv) : nraenv := TOptimEnvFunc.toptim_nraenv q.

  Definition nraenv_to_nnrc (q: nraenv) : nnrc :=
    algenv_to_nnrc q init_vid init_venv.

  Definition nraenv_to_nra (q: nraenv) : nra := alg_of_algenv q.

  Definition nra_to_nraenv (q: nra) : nraenv := algenv_of_alg q.

  Definition nra_optim (q: nra) : nra :=
    let nraenv_opt := (nraenv_optim (algenv_of_alg q)) in
    if is_nra_fun nraenv_opt then
      deenv_alg nraenv_opt
    else
      alg_of_algenv nraenv_opt.

  Definition nra_to_nnrc (q: nra) : nnrc := nra_to_nnrc q init_vid.

  Definition nnrc_optim (q: nnrc) : nnrc := trew q.

  Definition nnrc_to_camp (avoid: list var) (q: nnrc) : camp := nrcToPat_let avoid q. (* XXX avoid ? XXX *)

  (* Java equivalent: NnrcToNrcmr.convert *)
  Definition nnrc_to_nnrcmr_comptop (vinit: var) (q: nnrc) : nnrcmr :=
    let q : nnrc := nrc_subst q init_vid (NRCConst dunit) in
    let q : nnrc := nnrc_optim q in
    let q_free_vars := (* bdistinct !!! *) nrc_free_vars q in
    let inputs_loc :=
        (init_vid, Vlocal)
          ::(vinit, Vlocal)
          ::(mkDistNames q_free_vars)
    in
    nnrc_to_nnrcmr_chain q
                         init_vinit
                         inputs_loc.

  Definition nnrc_to_nnrcmr (vinit: var) (inputs_loc: vdbindings) (q: nnrc) : nnrcmr :=
    (* XXX TODO: Handling of vid? XXX *)
    (* let q : nnrc := nrc_subst q init_vid (NRCConst dunit) in *)
    (* let q : nnrc := nnrc_optim q in *)
    let inputs_loc :=
        (init_vid, Vlocal) (* XXX suppr vid? XXX *)
          ::(vinit, Vlocal)
          :: inputs_loc
    in
    nnrc_to_nnrcmr_chain q
                         init_vinit
                         inputs_loc.

  Definition nnrcmr_optim (q: nnrcmr) : nnrcmr := trew_nnrcmr (mr_optimize q).

  Definition nnrcmr_to_nnrc (q: nnrcmr) : option nnrc := nnrc_of_nrcmr q.

  Definition nnrcmr_to_dnnrc_dataset (q: nnrcmr) : option dnnrc_dataset := dnnrc_of_nrcmr tt q.

  Definition nnrcmr_to_nnrcmr_cldmr_prepare (q: nnrcmr) : nnrcmr :=
    let q := foreign_to_cloudant_prepare_nrcmr q in
    let q := nnrcmr_optim q in                              (* XXXXXXXXXXX optim XXXXXXXX *)
    let q := foreign_to_cloudant_prepare_nrcmr q in
    nrcmr_rename_for_cloudant q.

  Definition nnrcmr_prepared_to_cldmr (h:list (string*string)) (q: nnrcmr) : cldmr :=
    NNRCMRtoNNRCMRCloudantTop h q.

  Definition nnrcmr_to_cldmr  (h:list (string*string)) (q: nnrcmr) : cldmr :=
    nnrcmr_prepared_to_cldmr h (nnrcmr_to_nnrcmr_cldmr_prepare q).

  Definition nnrcmr_to_nnrcmr_spark_prepare (q: nnrcmr) : nnrcmr :=
    let q := foreign_to_spark_prepare_nrcmr q in
    let q := nnrcmr_optim q in                              (* XXXXXXXXXXX optim XXXXXXXX *)
    let q := foreign_to_spark_prepare_nrcmr q in
    nrcmr_rename_for_spark q.

  Definition nnrcmr_prepared_to_spark (rulename: string) (q: nnrcmr) : spark :=
    nrcmrToSparkTopDataFromFileTop rulename init_vinit q. (* XXX init_vinit should be a parameter? *)

  Definition nnrcmr_to_spark (rulename: string) (q: nnrcmr) : spark :=
    nnrcmr_prepared_to_spark rulename (nnrcmr_to_nnrcmr_spark_prepare q).

  Definition cldmr_to_cloudant (rulename:string) (h:list (string*string)) (q:cldmr) : cloudant :=
    mapReducePairstoCloudant h q rulename.

  Definition nnrc_to_dnnrc_dataset (inputs_loc: vdbindings) (q: nnrc) : dnnrc_dataset :=
    nrc_to_dnrc tt inputs_loc q.

  Definition nnrc_to_javascript (q: nnrc) : javascript := (* XXX Check XXX *)
    nrcToJSTop q.

  Require Import ForeignToJava.
  Context {ftojava:foreign_to_java}.
  Definition nnrc_to_java (class_name:string) (imports:string) (q: nnrc) : java := (* XXX Check XXX *)
    nrcToJavaTop class_name imports q.

  Definition dnnrc_dataset_to_dnnrc_typed_dataset
             (e: dnnrc_dataset) (inputType: rtype)
    : option dnnrc_typed_dataset :=
    dnnrc_infer_type e inputType.

  Definition dnnrc_typed_dataset_to_spark2
             (inputType:rtype) (name:string) (q:dnnrc_typed_dataset) : string :=
    @dnrcToSpark2Top _ _ bm _ unit inputType name q.

  Definition dnnrc_typed_dataset_optim (q:dnnrc_typed_dataset) : dnnrc_typed_dataset :=
    dnnrcToDatasetRewrite q.

  (* Drivers *)

  Inductive javascript_driver : Set :=
    | Dv_javascript_stop : javascript_driver.

  Inductive java_driver : Set :=
    | Dv_java_stop : java_driver.

  Inductive spark_driver : Set :=
    | Dv_spark_stop : spark_driver.

  Inductive spark2_driver : Set :=
    | Dv_spark2_stop : spark2_driver.

  Inductive cloudant_driver : Set :=
    | Dv_cloudant_stop : cloudant_driver.

  Inductive cldmr_driver : Set :=
    | Dv_cldmr_stop : cldmr_driver
    | Dv_cldmr_to_cloudant : (* rulename *) string -> (* h *) list (string*string) -> cloudant_driver -> cldmr_driver.

  Inductive dnnrc_typed_dataset_driver : Set :=
    | Dv_dnnrc_typed_dataset_stop : dnnrc_typed_dataset_driver
    | Dv_dnnrc_typed_dataset_optim : dnnrc_typed_dataset_driver -> dnnrc_typed_dataset_driver
    | Dv_dnnrc_typed_dataset_to_spark2 : rtype -> string -> spark2_driver -> dnnrc_typed_dataset_driver
  .

  Inductive dnnrc_dataset_driver : Set :=
    | Dv_dnnrc_dataset_stop : dnnrc_dataset_driver
    | Dv_dnnrc_dataset_to_dnnrc_typed_dataset : rtype -> dnnrc_typed_dataset_driver -> dnnrc_dataset_driver
  .

(*  Unset Elimination Schemes. *)
  Inductive camp_driver : Set :=
    | Dv_camp_stop : camp_driver
    | Dv_camp_to_nraenv : nraenv_driver -> camp_driver
    | Dv_camp_to_nra : nra_driver -> camp_driver

  with nra_driver : Set :=
    | Dv_nra_stop : nra_driver
    | Dv_nra_optim : nra_driver -> nra_driver
    | Dv_nra_to_nnrc : nnrc_driver -> nra_driver
    | Dv_nra_to_nraenv : nraenv_driver -> nra_driver

  with nraenv_driver : Set :=
    | Dv_nraenv_stop : nraenv_driver
    | Dv_nraenv_optim : nraenv_driver -> nraenv_driver
    | Dv_nraenv_to_nnrc : nnrc_driver -> nraenv_driver
    | Dv_nraenv_to_nra : nra_driver -> nraenv_driver

  with nnrc_driver : Set :=
    | Dv_nnrc_stop : nnrc_driver
    | Dv_nnrc_optim : nnrc_driver -> nnrc_driver
    | Dv_nnrc_to_nnrcmr : (* vinit *) var -> (* (* inputs_loc *) vdbindings -> *) nnrcmr_driver -> nnrc_driver
    | Dv_nnrc_to_dnnrc_dataset : (* inputs_loc *) vdbindings -> dnnrc_dataset_driver -> nnrc_driver
    | Dv_nnrc_to_javascript : javascript_driver -> nnrc_driver
    | Dv_nnrc_to_java : (* class_name *) string -> (* imports *) string -> java_driver -> nnrc_driver
    | Dv_nnrc_to_camp : (* avoid *) list var -> camp_driver -> nnrc_driver

  with nnrcmr_driver : Set :=
    | Dv_nnrcmr_stop : nnrcmr_driver
    | Dv_nnrcmr_optim : nnrcmr_driver -> nnrcmr_driver
    | Dv_nnrcmr_to_spark : (* rulename *) string -> spark_driver -> nnrcmr_driver
    | Dv_nnrcmr_to_nnrc : nnrc_driver -> nnrcmr_driver
    | Dv_nnrcmr_to_dnnrc_dataset : dnnrc_dataset_driver -> nnrcmr_driver
    | Dv_nnrcmr_to_cldmr : (* h *) list (string*string) -> cldmr_driver -> nnrcmr_driver.

(*  Set Elimination Scheme. *)

  Scheme camp_driver_ind' := Induction for camp_driver Sort Prop
                            with nra_driver_ind' := Induction for nra_driver Sort Prop
                                                   with nraenv_driver_ind' := Induction for nraenv_driver Sort Prop
                                                                             with nnrc_driver_ind' := Induction for nnrc_driver Sort Prop
                                                                                                     with nnrcmr_driver_ind' := Induction for nnrcmr_driver Sort Prop.

  Combined Scheme cnd_combined_ind
           from camp_driver_ind', nra_driver_ind', nraenv_driver_ind', nnrc_driver_ind', nnrcmr_driver_ind'.

  Inductive rule_driver : Set :=
    | Dv_rule_stop : rule_driver
    | Dv_rule_to_camp : camp_driver -> rule_driver
    | Dv_rule_to_nraenv : nraenv_driver -> rule_driver
    | Dv_rule_to_nra : nra_driver -> rule_driver.

  Inductive oql_driver : Set :=
    | Dv_oql_stop : oql_driver
    | Dv_oql_to_nraenv : nraenv_driver -> oql_driver.

  Inductive sql_driver : Set :=
    | Dv_sql_stop : sql_driver
    | Dv_sql_to_nraenv : nraenv_driver -> sql_driver.

  Inductive lambda_nra_driver : Set :=
    | Dv_lambda_nra_stop : lambda_nra_driver
    | Dv_lambda_nra_to_nraenv : nraenv_driver -> lambda_nra_driver.

  Inductive driver
    : Set :=
  | Dv_rule : rule_driver -> driver
  | Dv_camp : camp_driver -> driver
  | Dv_oql : oql_driver -> driver
  | Dv_sql : sql_driver -> driver
  | Dv_lambda_nra : lambda_nra_driver -> driver
  | Dv_nra : nra_driver -> driver
  | Dv_nraenv : nraenv_driver -> driver
  | Dv_nnrc : nnrc_driver -> driver
  | Dv_nnrcmr : nnrcmr_driver -> driver
  | Dv_cldmr : cldmr_driver -> driver
  | Dv_dnnrc_dataset : dnnrc_dataset_driver -> driver
  | Dv_dnnrc_typed_dataset : dnnrc_typed_dataset_driver -> driver
  | Dv_javascript : javascript_driver -> driver
  | Dv_java : java_driver -> driver
  | Dv_spark : spark_driver -> driver
  | Dv_spark2 : spark2_driver -> driver
  | Dv_cloudant : cloudant_driver -> driver
  | Dv_error : string -> driver.


  Tactic Notation "driver_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "Dv_rule"%string
    | Case_aux c "Dv_camp"%string
    | Case_aux c "Dv_oql"%string
    | Case_aux c "Dv_sql"%string
    | Case_aux c "Dv_lambda_nra"%string
    | Case_aux c "Dv_nra"%string
    | Case_aux c "Dv_nraenv"%string
    | Case_aux c "Dv_nnrc"%string
    | Case_aux c "Dv_nnrcmr"%string
    | Case_aux c "Dv_cldmr"%string
    | Case_aux c "Dv_dnnrc_dataset"%string
    | Case_aux c "Dv_dnnrc_typed_dataset"%string
    | Case_aux c "Dv_javascript"%string
    | Case_aux c "Dv_java"%string
    | Case_aux c "Dv_spark"%string
    | Case_aux c "Dv_spark2"%string
    | Case_aux c "Dv_cloudant"%string
    | Case_aux c "Dv_error"%string ].

  (* Compilers function *)

  Section CompDriverUtil.

  Definition language_of_driver (dv: driver) :=
    match dv with
    | Dv_nra _ => L_nra
    | Dv_nraenv _ => L_nraenv
    | Dv_nnrc _ => L_nnrcmr
    | Dv_nnrcmr _ => L_nnrcmr
    | Dv_rule _ => L_rule
    | Dv_camp _ => L_camp
    | Dv_oql _ => L_oql
    | Dv_sql _ => L_sql
    | Dv_lambda_nra _ => L_lambda_nra
    | Dv_cldmr _ => L_cldmr
    | Dv_dnnrc_dataset  _ => L_dnnrc_dataset
    | Dv_dnnrc_typed_dataset _ => L_dnnrc_typed_dataset
    | Dv_javascript _ => L_javascript
    | Dv_java _ => L_java
    | Dv_spark _ => L_spark
    | Dv_spark2 _ => L_spark2
    | Dv_cloudant _ => L_cloudant
    | Dv_error err => L_error ("language of "++err)
    end.

  Definition name_of_driver dv :=
    name_of_language (language_of_driver dv).

  Definition driver_length_javascript (dv: javascript_driver) :=
  match dv with
  | Dv_javascript_stop => 1
  end.

  Definition driver_length_java (dv: java_driver) :=
    match dv with
    | Dv_java_stop => 1
    end.

  Definition driver_length_spark (dv: spark_driver) :=
    match dv with
    | Dv_spark_stop => 1
    end.

  Definition driver_length_spark2 (dv: spark2_driver) :=
    match dv with
    | Dv_spark2_stop => 1
    end.

  Definition driver_length_cloudant (dv: cloudant_driver) :=
    match dv with
    | Dv_cloudant_stop => 1
    end.

  Definition driver_length_cldmr (dv: cldmr_driver) :=
    match dv with
    | Dv_cldmr_stop => 1
    | Dv_cldmr_to_cloudant rulename h dv => 1 + driver_length_cloudant dv
    end.

  Fixpoint driver_length_dnnrc_typed_dataset {ftyping: foreign_typing} (dv: dnnrc_typed_dataset_driver) :=
    match dv with
    | Dv_dnnrc_typed_dataset_stop => 1
    | Dv_dnnrc_typed_dataset_optim dv => 1 + driver_length_dnnrc_typed_dataset dv
    | Dv_dnnrc_typed_dataset_to_spark2 rt rulename dv => 1 + driver_length_spark2 dv
    end.

  Definition driver_length_dnnrc_dataset (dv: dnnrc_dataset_driver) :=
    match dv with
    | Dv_dnnrc_dataset_stop => 1
    | Dv_dnnrc_dataset_to_dnnrc_typed_dataset _ dv => 1 + driver_length_dnnrc_typed_dataset dv
    end.

  Fixpoint driver_length_camp (dv: camp_driver) :=
    match dv with
    | Dv_camp_stop => 1
    | Dv_camp_to_nraenv dv => 1 + driver_length_nraenv dv
    | Dv_camp_to_nra dv => 1 + driver_length_nra dv
    end

  with driver_length_nra (dv: nra_driver)  :=
    match dv with
    | Dv_nra_stop => 1
    | Dv_nra_optim dv => 1 + driver_length_nra dv
    | Dv_nra_to_nnrc dv => 1 + driver_length_nnrc dv
    | Dv_nra_to_nraenv dv => 1 + driver_length_nraenv dv
    end

  with driver_length_nraenv (dv: nraenv_driver) :=
    match dv with
    | Dv_nraenv_stop => 1
    | Dv_nraenv_optim dv => 1 + driver_length_nraenv dv
    | Dv_nraenv_to_nnrc dv => 1 + driver_length_nnrc dv
    | Dv_nraenv_to_nra dv => 1 + driver_length_nra dv
    end

  with driver_length_nnrc (dv: nnrc_driver) :=
    match dv with
    | Dv_nnrc_stop => 1
    | Dv_nnrc_optim dv => 1 + driver_length_nnrc dv
    | Dv_nnrc_to_nnrcmr vinit (* inputs_loc *) dv => 1 + driver_length_nnrcmr dv
    | Dv_nnrc_to_dnnrc_dataset inputs_loc dv => 1 + driver_length_dnnrc_dataset dv
    | Dv_nnrc_to_javascript dv => 1 + driver_length_javascript dv
    | Dv_nnrc_to_java class_name imports dv => 1 + driver_length_java dv
    | Dv_nnrc_to_camp avoid dv => 1 + driver_length_camp dv
    end

  with driver_length_nnrcmr (dv: nnrcmr_driver) :=
    match dv with
    | Dv_nnrcmr_stop => 1
    | Dv_nnrcmr_optim dv => 1 + driver_length_nnrcmr dv
    | Dv_nnrcmr_to_spark rulename dv => 1 + driver_length_spark dv
    | Dv_nnrcmr_to_nnrc dv => 1 + driver_length_nnrc dv
    | Dv_nnrcmr_to_cldmr h dv => 1 + driver_length_cldmr dv
    | Dv_nnrcmr_to_dnnrc_dataset dv => 1 + driver_length_dnnrc_dataset dv
    end.

  Definition driver_length_rule (dv: rule_driver) :=
    match dv with
    | Dv_rule_stop => 1
    | Dv_rule_to_camp dv => 1 + driver_length_camp dv
    | Dv_rule_to_nraenv dv => 1 + driver_length_nraenv dv
    | Dv_rule_to_nra dv => 1 + driver_length_nra dv
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

  Definition driver_length_lambda_nra (dv: lambda_nra_driver) :=
    match dv with
    | Dv_lambda_nra_stop => 1
    | Dv_lambda_nra_to_nraenv dv => 1 + driver_length_nraenv dv
    end.

  Definition driver_length (dv: driver)  :=
    match dv with
    | Dv_rule dv => driver_length_rule dv
    | Dv_camp dv => driver_length_camp dv
    | Dv_oql dv => driver_length_oql dv
    | Dv_sql dv => driver_length_sql dv
    | Dv_lambda_nra dv => driver_length_lambda_nra dv
    | Dv_nra dv => driver_length_nra dv
    | Dv_nraenv dv => driver_length_nraenv dv
    | Dv_nnrc dv => driver_length_nnrc dv
    | Dv_nnrcmr dv => driver_length_nnrcmr dv
    | Dv_cldmr dv => driver_length_cldmr dv
    | Dv_dnnrc_dataset dv => driver_length_dnnrc_dataset dv
    | Dv_dnnrc_typed_dataset dv => driver_length_dnnrc_typed_dataset dv
    | Dv_javascript dv => driver_length_javascript dv
    | Dv_java dv => driver_length_java dv
    | Dv_spark dv => driver_length_spark dv
    | Dv_spark2 dv => driver_length_spark2 dv
    | Dv_cloudant dv => driver_length_cloudant dv
    | Dv_error s => 1
    end.


  End CompDriverUtil.

  Section CompDriverCompile.
  Definition compile_javascript (dv: javascript_driver) (q: javascript) : list query :=
    let queries :=
        match dv with
        | Dv_javascript_stop => nil
        end
    in
    (Q_javascript q) :: queries.

  Definition compile_java (dv: java_driver) (q: java) : list query :=
    let queries :=
        match dv with
        | Dv_java_stop => nil
        end
    in
    (Q_java q) :: queries.

  Definition compile_spark (dv: spark_driver) (q: spark) : list query :=
    let queries :=
        match dv with
        | Dv_spark_stop => nil
        end
    in
    (Q_spark q) :: queries.

  Definition compile_spark2 (dv: spark2_driver) (q: spark2) : list query :=
    let queries :=
        match dv with
        | Dv_spark2_stop => nil
        end
    in
    (Q_spark2 q) :: queries.

  Definition compile_cloudant (dv: cloudant_driver) (q: cloudant) : list query :=
    let queries :=
        match dv with
        | Dv_cloudant_stop => nil
        end
    in
    (Q_cloudant q) :: queries.

  Definition compile_cldmr (dv: cldmr_driver) (q: cldmr) : list query :=
    let queries :=
        match dv with
        | Dv_cldmr_stop => nil
        | Dv_cldmr_to_cloudant rulename h dv =>
          let q := cldmr_to_cloudant rulename h q in
          compile_cloudant dv q
        end
    in
    (Q_cldmr q) :: queries.

  Fixpoint compile_dnnrc_typed_dataset (dv: dnnrc_typed_dataset_driver) (q: dnnrc_typed_dataset) : list query :=
    let queries :=
        match dv with
        | Dv_dnnrc_typed_dataset_stop => nil
        | Dv_dnnrc_typed_dataset_optim dv =>
          let q := dnnrc_typed_dataset_optim q in
          compile_dnnrc_typed_dataset dv q
        | Dv_dnnrc_typed_dataset_to_spark2 rt rulename dv =>
          let q := dnnrc_typed_dataset_to_spark2 rt rulename q in
          compile_spark2 dv q
        end
    in
    (Q_dnnrc_typed_dataset q) :: queries.

  Definition compile_dnnrc_dataset (dv: dnnrc_dataset_driver) (q: dnnrc_dataset) : list query :=
    let queries :=
        match dv with
        | Dv_dnnrc_dataset_stop => nil
        | Dv_dnnrc_dataset_to_dnnrc_typed_dataset rt dv =>
          let q := dnnrc_dataset_to_dnnrc_typed_dataset q rt in
          match q with
          | Some q => compile_dnnrc_typed_dataset dv q
          | None => (Q_error "Type checking failed for dnnrc query") :: nil
          end
        end
    in
    (Q_dnnrc_dataset q) :: queries.

  Fixpoint compile_camp (dv: camp_driver) (q: camp) : list query :=
    let queries :=
        match dv with
        | Dv_camp_stop => nil
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
        | Dv_nra_optim dv =>
          let q := nra_optim q in
          compile_nra dv q
        | Dv_nra_to_nnrc dv =>
          let q := nra_to_nnrc q in
          compile_nnrc dv q
        | Dv_nra_to_nraenv dv =>
          let q := nra_to_nraenv q in
          compile_nraenv dv q
        end
    in
    (Q_nra q) :: queries

  with compile_nraenv (dv: nraenv_driver) (q: nraenv) : list query :=
    let queries :=
        match dv with
        | Dv_nraenv_stop => nil
        | Dv_nraenv_optim dv =>
          let q := nraenv_optim q in
          compile_nraenv dv q
        | Dv_nraenv_to_nnrc dv =>
          let q := nraenv_to_nnrc q in
          compile_nnrc dv q
        | Dv_nraenv_to_nra dv =>
          let q := nraenv_to_nra q in
          compile_nra dv q
        end
    in
    (Q_nraenv q) :: queries

  with compile_nnrc (dv: nnrc_driver) (q: nnrc) : list query :=
    let queries :=
        match dv with
        | Dv_nnrc_stop => nil
        | Dv_nnrc_optim dv =>
          let q := nnrc_optim q in
          compile_nnrc dv q
        | Dv_nnrc_to_nnrcmr vinit (* inputs_loc *) dv =>
          let q := nnrc_to_nnrcmr_comptop vinit (* inputs_loc *) q in
          compile_nnrcmr dv q
        | Dv_nnrc_to_dnnrc_dataset inputs_loc dv =>
          let q := nnrc_to_dnnrc_dataset inputs_loc q in
          compile_dnnrc_dataset dv q
        | Dv_nnrc_to_javascript dv =>
          let q := nnrc_to_javascript q in
          compile_javascript dv q
        | Dv_nnrc_to_java class_name imports dv =>
          let q := nnrc_to_java class_name imports q in
          compile_java dv q
        | Dv_nnrc_to_camp avoid dv =>
          let q := nnrc_to_camp avoid q in
          compile_camp dv q
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
        | Dv_nnrcmr_to_spark rulename dv =>
          let q := nnrcmr_to_spark rulename q in
          compile_spark dv q
        | Dv_nnrcmr_to_nnrc dv =>
          let q_opt := nnrcmr_to_nnrc q in
          match q_opt with
          | Some q => compile_nnrc dv q
          | None => (Q_error "Unable to compile NNRCMR to NNRC") :: nil
          end
        | Dv_nnrcmr_to_cldmr h dv =>
          let q := nnrcmr_to_cldmr h q in
          compile_cldmr dv q
        | Dv_nnrcmr_to_dnnrc_dataset dv =>
          let q_opt := nnrcmr_to_dnnrc_dataset q in
          match q_opt with
          | Some q => compile_dnnrc_dataset dv q
          | None => (Q_error "Unable to compile NNRCMR to NNRC") :: nil
          end
        end
    in
    (Q_nnrcmr q) :: queries.

  Definition compile_rule (dv: rule_driver) (q: rule) : list query :=
    let queries :=
        match dv with
        | Dv_rule_stop => nil
        | Dv_rule_to_camp dv =>
          let q := rule_to_camp q in
          compile_camp dv q
        | Dv_rule_to_nraenv dv =>
          let q := rule_to_nraenv q in
          compile_nraenv dv q
        | Dv_rule_to_nra dv =>
          let q := rule_to_nra q in
          compile_nra dv q
        end
    in
    (Q_rule q) :: queries.

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
    | (Dv_rule dv, Q_rule q) => compile_rule dv q
    | (Dv_camp dv, Q_camp q) => compile_camp dv q
    | (Dv_oql dv, Q_oql q) => compile_oql dv q
    | (Dv_sql dv, Q_sql q) => compile_sql dv q
    | (Dv_lambda_nra dv, Q_lambda_nra q) => compile_lambda_nra dv q
    | (Dv_nra dv, Q_nra q) => compile_nra dv q
    | (Dv_nraenv dv, Q_nraenv q) => compile_nraenv dv q
    | (Dv_nnrc dv, Q_nnrc q) => compile_nnrc dv q
    | (Dv_nnrcmr dv, Q_nnrcmr q) => compile_nnrcmr dv q
    | (Dv_cldmr dv, Q_cldmr q) => compile_cldmr dv q
    | (Dv_dnnrc_dataset dv, Q_dnnrc_dataset q) => compile_dnnrc_dataset dv q
    | (Dv_dnnrc_typed_dataset dv, Q_dnnrc_typed_dataset q) => compile_dnnrc_typed_dataset dv q
    | (Dv_javascript dv, Q_javascript q) => compile_javascript dv q
    | (Dv_java dv, Q_java q) => compile_java dv q
    | (Dv_spark dv, Q_spark q) => compile_spark dv q
    | (Dv_spark2 dv, Q_spark2 q) => compile_spark2 dv q
    | (Dv_cloudant dv, Q_cloudant q) => compile_cloudant dv q
    | (Dv_error s, _) => (Q_error ("[Driver Error]" ++ s)) :: nil
    | (_, _) => (Q_error "incompatible query and driver") :: nil
    end.

  End CompDriverCompile.

  (* Compilers config *)

  Section CompDriverConfig.
  Record driver_config :=
    mkDvConfig
      { comp_qname : string;
        comp_class_name : string; (* Class name different from rule name in Java case *)
        comp_brand_rel : list (string * string) (* brand_relation *);
        comp_input_type : rtype (* input type for inference *);
        comp_mr_vinit : var;
        comp_vdbindings : vdbindings;
        comp_java_imports : string; }.

  Definition push_translation config lang dv :=
    match lang with
    | L_rule =>
      match dv with
      | Dv_camp dv => Dv_rule (Dv_rule_to_camp dv)
      | Dv_nraenv dv => Dv_rule (Dv_rule_to_nraenv dv)
      | Dv_nra dv => Dv_rule (Dv_rule_to_nra dv)
      | Dv_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_camp =>
      match dv with
      | Dv_nraenv dv => Dv_camp (Dv_camp_to_nraenv dv)
      | Dv_nra dv => Dv_camp (Dv_camp_to_nra dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_oql =>
      match dv with
      | Dv_nraenv dv => Dv_oql (Dv_oql_to_nraenv dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
  | L_sql =>
      match dv with
      | Dv_nraenv dv => Dv_sql (Dv_sql_to_nraenv dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_lambda_nra =>
      match dv with
      | Dv_nraenv dv => Dv_lambda_nra (Dv_lambda_nra_to_nraenv dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nra =>
      match dv with
      | Dv_nnrc dv => Dv_nra (Dv_nra_to_nnrc dv)
      | Dv_nraenv dv => Dv_nra (Dv_nra_to_nraenv dv)
      | Dv_nra dv => Dv_nra (Dv_nra_optim dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nraenv =>
      match dv with
      | Dv_nnrc dv => Dv_nraenv (Dv_nraenv_to_nnrc dv)
      | Dv_nra dv => Dv_nraenv (Dv_nraenv_to_nra dv)
      | Dv_nraenv dv => Dv_nraenv (Dv_nraenv_optim dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nnrc =>
      match dv with
      | Dv_nnrcmr dv => Dv_nnrc (Dv_nnrc_to_nnrcmr config.(comp_mr_vinit) (* config.(comp_vdbindings) *) dv)
      | Dv_dnnrc_dataset dv => Dv_nnrc (Dv_nnrc_to_dnnrc_dataset config.(comp_vdbindings) dv)
      | Dv_javascript dv => Dv_nnrc (Dv_nnrc_to_javascript dv)
      | Dv_java dv => Dv_nnrc (Dv_nnrc_to_java config.(comp_class_name) config.(comp_java_imports) dv)
      | Dv_camp dv => Dv_nnrc (Dv_nnrc_to_camp (List.map fst config.(comp_vdbindings)) dv) (* XXX to check XXX *)
      | Dv_nnrc dv => Dv_nnrc (Dv_nnrc_optim dv)
      | Dv_rule _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv _
      | Dv_cldmr _
      | Dv_dnnrc_typed_dataset _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_nnrcmr =>
      match dv with
      | Dv_spark dv => Dv_nnrcmr (Dv_nnrcmr_to_spark config.(comp_qname) dv)
      | Dv_nnrc dv => Dv_nnrcmr (Dv_nnrcmr_to_nnrc dv)
      | Dv_dnnrc_dataset dv => Dv_nnrcmr (Dv_nnrcmr_to_dnnrc_dataset dv)
      | Dv_cldmr dv => Dv_nnrcmr (Dv_nnrcmr_to_cldmr config.(comp_brand_rel) dv)
      | Dv_nnrcmr dv => Dv_nnrcmr (Dv_nnrcmr_optim dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark2 _
      | Dv_cloudant _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_cldmr =>
      match dv with
      | Dv_cloudant dv => Dv_cldmr (Dv_cldmr_to_cloudant config.(comp_qname) config.(comp_brand_rel) dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_dnnrc_dataset =>
      match dv with
      | Dv_dnnrc_typed_dataset dv =>
        Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_dnnrc_typed_dataset config.(comp_input_type) dv)
      | Dv_dnnrc_dataset _
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_dnnrc_typed_dataset =>
      match dv with
      | Dv_spark2 dv =>
        Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_spark2 config.(comp_input_type) config.(comp_qname) dv)
      | Dv_dnnrc_typed_dataset dv =>
        Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_optim dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_sql _
      | Dv_lambda_nra _
      | Dv_nra _
      | Dv_nraenv _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_cloudant _ =>
          Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
      | Dv_error err =>
          Dv_error ("Cannot compile to error ("++err++")")
      end
    | L_javascript
    | L_java
    | L_spark
    | L_spark2
    | L_cloudant =>
      Dv_error ("No compilation path from "++(name_of_language lang)++" to "++(name_of_driver dv))
    | L_error err =>
      Dv_error ("No compilation from error ("++err++")")
    end.

  Definition driver_of_language lang :=
    match lang with
    | L_rule => Dv_rule Dv_rule_stop
    | L_camp => Dv_camp Dv_camp_stop
    | L_oql => Dv_oql Dv_oql_stop
    | L_sql => Dv_sql Dv_sql_stop
    | L_lambda_nra => Dv_lambda_nra Dv_lambda_nra_stop
    | L_nra => Dv_nra Dv_nra_stop
    | L_nraenv => Dv_nraenv Dv_nraenv_stop
    | L_nnrc => Dv_nnrc Dv_nnrc_stop
    | L_nnrcmr => Dv_nnrcmr Dv_nnrcmr_stop
    | L_cldmr => Dv_cldmr Dv_cldmr_stop
    | L_dnnrc_dataset => Dv_dnnrc_dataset Dv_dnnrc_dataset_stop
    | L_dnnrc_typed_dataset => Dv_dnnrc_typed_dataset Dv_dnnrc_typed_dataset_stop
    | L_javascript => Dv_javascript Dv_javascript_stop
    | L_java => Dv_java Dv_java_stop
    | L_spark => Dv_spark Dv_spark_stop
    | L_spark2 => Dv_spark2 Dv_spark2_stop
    | L_cloudant => Dv_cloudant Dv_cloudant_stop
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

  Definition fix_driver dv q :=
    match (dv, q) with
    | (Dv_rule (Dv_rule_to_nraenv dv), Q_camp q) => Dv_camp (Dv_camp_to_nraenv dv)
    | (Dv_rule (Dv_rule_to_nra dv), Q_camp q) => Dv_camp (Dv_camp_to_nra dv)
    | (Dv_camp (Dv_camp_to_nraenv dv), Q_rule q) => Dv_rule (Dv_rule_to_nraenv dv)
    | (Dv_camp (Dv_camp_to_nra dv), Q_rule q) => Dv_rule (Dv_rule_to_nra dv)
    | (_, _) => dv
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
        | Dv_nnrc (Dv_nnrc_to_nnrcmr vinit (* vdbindings *) _) =>
          vinit = config.(comp_mr_vinit) (* /\ vdbindings = config.(comp_vdbindings) *)
        | Dv_nnrc (Dv_nnrc_to_dnnrc_dataset vdbindings _) =>
          vdbindings = config.(comp_vdbindings)
        | Dv_nnrc (Dv_nnrc_to_java class_name imports _) =>
          class_name = config.(comp_class_name) /\ imports = config.(comp_java_imports)
        | Dv_nnrc (Dv_nnrc_to_camp avoid _) =>
          avoid = (List.map fst config.(comp_vdbindings))
        | Dv_nnrcmr (Dv_nnrcmr_to_spark qname _) =>
          qname = config.(comp_qname)
        | Dv_nnrcmr (Dv_nnrcmr_to_cldmr brand_rel _) =>
          brand_rel = config.(comp_brand_rel)
        | Dv_cldmr (Dv_cldmr_to_cloudant qname brand_rel _) =>
          qname = config.(comp_qname) /\ brand_rel = config.(comp_brand_rel)
        | Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_dnnrc_typed_dataset input_type _) =>
          input_type = config.(comp_input_type)
        | Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_spark2 input_type qname _) =>
          input_type = config.(comp_input_type) /\ qname = config.(comp_qname)
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
    | Dv_rule (Dv_rule_stop) => (L_rule, None)
    | Dv_rule (Dv_rule_to_camp dv) => (L_rule, Some (Dv_camp dv))
    | Dv_rule (Dv_rule_to_nraenv dv) => (L_rule, Some (Dv_nraenv dv))
    | Dv_rule (Dv_rule_to_nra dv) => (L_rule, Some (Dv_nra dv))
    | Dv_camp (Dv_camp_stop) => (L_camp, None)
    | Dv_camp (Dv_camp_to_nraenv dv) => (L_camp, Some (Dv_nraenv dv))
    | Dv_camp (Dv_camp_to_nra dv) => (L_camp, Some (Dv_nra dv))
    | Dv_oql (Dv_oql_stop) => (L_oql, None)
    | Dv_oql (Dv_oql_to_nraenv dv) => (L_oql, Some (Dv_nraenv dv))
    | Dv_sql (Dv_sql_stop) => (L_sql, None)
    | Dv_sql (Dv_sql_to_nraenv dv) => (L_sql, Some (Dv_nraenv dv))
    | Dv_lambda_nra (Dv_lambda_nra_stop) => (L_lambda_nra, None)
    | Dv_lambda_nra (Dv_lambda_nra_to_nraenv dv) => (L_lambda_nra, Some (Dv_nraenv dv))
    | Dv_nra (Dv_nra_stop) => (L_nra, None)
    | Dv_nra (Dv_nra_to_nnrc dv) => (L_nra, Some (Dv_nnrc dv))
    | Dv_nra (Dv_nra_to_nraenv dv) => (L_nra, Some (Dv_nraenv dv))
    | Dv_nra (Dv_nra_optim dv) => (L_nra, Some (Dv_nra dv))
    | Dv_nraenv (Dv_nraenv_stop) => (L_nraenv, None)
    | Dv_nraenv (Dv_nraenv_to_nnrc dv) => (L_nraenv, Some (Dv_nnrc dv))
    | Dv_nraenv (Dv_nraenv_to_nra dv) => (L_nraenv, Some (Dv_nra dv))
    | Dv_nraenv (Dv_nraenv_optim dv) => (L_nraenv, Some (Dv_nraenv dv))
    | Dv_nnrc (Dv_nnrc_stop) => (L_nnrc, None)
    | Dv_nnrc (Dv_nnrc_to_nnrcmr vinit (* vdbindings *) dv) => (L_nnrc, Some (Dv_nnrcmr dv))
    | Dv_nnrc (Dv_nnrc_to_dnnrc_dataset inputs_loc dv) => (L_nnrc, Some (Dv_dnnrc_dataset dv))
    | Dv_nnrc (Dv_nnrc_to_javascript dv) => (L_nnrc, Some (Dv_javascript dv))
    | Dv_nnrc (Dv_nnrc_to_java name java_imports dv) => (L_nnrc, Some (Dv_java dv))
    | Dv_nnrc (Dv_nnrc_to_camp vdbindings dv) => (L_nnrc, Some (Dv_camp dv))
    | Dv_nnrc (Dv_nnrc_optim dv) => (L_nnrc, Some (Dv_nnrc dv))
    | Dv_nnrcmr (Dv_nnrcmr_stop) => (L_nnrcmr, None)
    | Dv_nnrcmr (Dv_nnrcmr_to_spark name dv) => (L_nnrcmr, Some (Dv_spark dv))
    | Dv_nnrcmr (Dv_nnrcmr_to_nnrc dv) => (L_nnrcmr, Some (Dv_nnrc dv))
    | Dv_nnrcmr (Dv_nnrcmr_to_dnnrc_dataset dv) => (L_nnrcmr, Some (Dv_dnnrc_dataset dv))
    | Dv_nnrcmr (Dv_nnrcmr_to_cldmr brand_rel dv) => (L_nnrcmr, Some (Dv_cldmr dv))
    | Dv_nnrcmr (Dv_nnrcmr_optim dv) => (L_nnrcmr, Some (Dv_nnrcmr dv))
    | Dv_cldmr (Dv_cldmr_stop) => (L_cldmr, None)
    | Dv_cldmr (Dv_cldmr_to_cloudant name brand_rel dv) => (L_cldmr, Some (Dv_cloudant dv))
    | Dv_dnnrc_dataset (Dv_dnnrc_dataset_stop) => (L_dnnrc_dataset, None)
    | Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_dnnrc_typed_dataset rtype dv) => (L_dnnrc_typed_dataset, Some (Dv_dnnrc_typed_dataset dv)) (* XXX TO BE CHECKED XXX *)
    | Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_stop) => (L_dnnrc_typed_dataset, None)
    | Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_optim dv) => (L_dnnrc_typed_dataset, Some (Dv_dnnrc_typed_dataset dv)) (* XXX TO BE CHECKED XXX *)
    | Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_spark2 rtype _ dv) => (L_dnnrc_typed_dataset, Some (Dv_spark2 dv))
    | Dv_javascript (Dv_javascript_stop) => (L_javascript, None)
    | Dv_java (Dv_java_stop) => (L_java, None)
    | Dv_spark (Dv_spark_stop) => (L_spark, None)
    | Dv_spark2 (Dv_spark2_stop) => (L_spark2, None)
    | Dv_cloudant (Dv_cloudant_stop) => (L_cloudant, None)
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

  Definition trivial_driver_config : driver_config
    := mkDvConfig
         EmptyString
         EmptyString
         nil
         ⊥
         EmptyString
         nil
         EmptyString.

  Lemma target_language_of_driver_is_postfix_javascript:
      (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_javascript dv))) (Dv_javascript dv)).
    Proof.
      destruct dv.
      reflexivity.
    Qed.

    Lemma target_language_of_driver_is_postfix_java:
      (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_java dv))) (Dv_java dv)).
    Proof.
      destruct dv.
      reflexivity.
    Qed.

    Lemma target_language_of_driver_is_postfix_spark:
      (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_spark dv))) (Dv_spark dv)).
    Proof.
      destruct dv.
      reflexivity.
    Qed.

    Lemma target_language_of_driver_is_postfix_spark2:
      (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_spark2 dv))) (Dv_spark2 dv)).
    Proof.
      destruct dv.
      reflexivity.
    Qed.

    Lemma target_language_of_driver_is_postfix_cloudant:
      (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_cloudant dv))) (Dv_cloudant dv)).
    Proof.
      destruct dv.
      reflexivity.
    Qed.

    Lemma target_language_of_driver_is_postfix_cldmr:
      (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_cldmr dv))) (Dv_cldmr dv)).
    Proof.
      destruct dv; simpl
      ; try reflexivity
      ; rewrite target_language_of_driver_equation
      ; simpl.
      - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 s
                 EmptyString
                 l
                 ⊥
                 EmptyString
                 nil
                 EmptyString) (lang:=L_cldmr)
      ; [ eapply target_language_of_driver_is_postfix_cloudant | | ]
      ; simpl; trivial.
    Qed.


  Lemma target_language_of_driver_is_postfix_dnnrc_typed_dataset:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_dnnrc_typed_dataset dv))) (Dv_dnnrc_typed_dataset dv)).
  Proof.
    induction dv; simpl
    ; try reflexivity
    ; rewrite target_language_of_driver_equation
    ; simpl.
    - eapply is_postfix_plus_one with
      (config:=trivial_driver_config) (lang:=L_dnnrc_typed_dataset)
      ; [eassumption | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 s
                 EmptyString
                 nil
                 r
                 EmptyString
                 nil
                 EmptyString) (lang:=L_dnnrc_typed_dataset)
      ; [ eapply target_language_of_driver_is_postfix_spark2 | | ]
      ; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_dnnrc_dataset:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_dnnrc_dataset dv))) (Dv_dnnrc_dataset dv)).
  Proof.
    destruct dv; simpl.
    - reflexivity.
    - rewrite target_language_of_driver_equation
      ; simpl.
      eapply is_postfix_plus_one with
               (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 nil
                 r
                 EmptyString
                 nil
                 EmptyString) (lang:=L_dnnrc_dataset)
      ; [eapply target_language_of_driver_is_postfix_dnnrc_typed_dataset | | ]; simpl; trivial.
  Qed.

  Lemma target_language_of_driver_is_postfix_cnd:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_camp dv)))
                                  (Dv_camp dv))
    /\  (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nra dv)))
                                      (Dv_nra dv))
    /\  (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nraenv dv)))
                                      (Dv_nraenv dv))
    /\  (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nnrc dv)))
                                      (Dv_nnrc dv))
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
               (config:=trivial_driver_config) (lang:=L_nraenv);
             [eassumption | | ]; simpl; trivial)
          | (eapply is_postfix_plus_one with
               (config:=trivial_driver_config) (lang:=L_nnrc);
             [eassumption | | ]; simpl; trivial)
          | (eapply is_postfix_plus_one with
               (config:=trivial_driver_config) (lang:=L_nnrcmr);
             [eassumption | | ]; simpl; trivial)
          ].
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 nil
                 ⊥
                 v
                 nil
                 EmptyString) (lang:=L_nnrc);
        [eassumption | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 nil
                 ⊥
                 EmptyString
                 v
                 EmptyString) (lang:=L_nnrc);
        [eapply target_language_of_driver_is_postfix_dnnrc_dataset | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=trivial_driver_config) (lang:=L_nnrc);
        [eapply target_language_of_driver_is_postfix_javascript | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 s
                 nil
                 ⊥
                 EmptyString
                 nil
                 s0) (lang:=L_nnrc);
        [eapply target_language_of_driver_is_postfix_java | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 nil
                 ⊥
                 EmptyString
                 (List.map (fun x => (x,Vlocal)) l)
                 EmptyString) (lang:=L_nnrc);
        [eassumption | | ]; simpl; trivial.
      rewrite List.map_map.
      simpl.
      rewrite List.map_id.
      trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 s
                 EmptyString
                 nil
                 ⊥
                 EmptyString
                 nil
                 EmptyString) (lang:=L_nnrcmr);
        [eapply target_language_of_driver_is_postfix_spark | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 nil
                 ⊥
                 EmptyString
                 nil
                 EmptyString) (lang:=L_nnrcmr);
        [eapply target_language_of_driver_is_postfix_dnnrc_dataset | | ]; simpl; trivial.
    - eapply is_postfix_plus_one with
      (config:=mkDvConfig
                 EmptyString
                 EmptyString
                 l
                 ⊥
                 EmptyString
                 nil
                 EmptyString) (lang:=L_nnrcmr);
        [eapply target_language_of_driver_is_postfix_cldmr | | ]; simpl; trivial.
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

  Lemma target_language_of_driver_is_postfix_nraenv:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_nraenv dv))) (Dv_nraenv dv)).
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

  Lemma target_language_of_driver_is_postfix_rule:
    (forall dv, is_postfix_driver (driver_of_language (target_language_of_driver (Dv_rule dv))) (Dv_rule dv)).
  Proof.
    destruct dv; simpl; try reflexivity
    ; rewrite target_language_of_driver_equation
    ; simpl
    ;  try solve [eapply is_postfix_plus_one with
                  (config:=trivial_driver_config) (lang:=L_rule);
                  [apply target_language_of_driver_is_postfix_cnd | | ]; simpl; trivial].
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
         target_language_of_driver_is_postfix_javascript
         target_language_of_driver_is_postfix_java
         target_language_of_driver_is_postfix_spark
         target_language_of_driver_is_postfix_spark2
         target_language_of_driver_is_postfix_cloudant
         target_language_of_driver_is_postfix_cldmr
         target_language_of_driver_is_postfix_dnnrc_typed_dataset
         target_language_of_driver_is_postfix_dnnrc_dataset
         target_language_of_driver_is_postfix_camp
         target_language_of_driver_is_postfix_nra
         target_language_of_driver_is_postfix_nraenv
         target_language_of_driver_is_postfix_nnrc
         target_language_of_driver_is_postfix_nnrcmr
         target_language_of_driver_is_postfix_rule
         target_language_of_driver_is_postfix_oql
         target_language_of_driver_is_postfix_sql
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
        * destruct (H_config ((Dv_nnrc (Dv_nnrc_to_camp (List.map fst (comp_vdbindings config0)) c))));
            reflexivity.
        * destruct (H_config (Dv_nnrc (Dv_nnrc_to_nnrcmr (comp_mr_vinit config0) n)));
            reflexivity.
        * destruct (H_config (Dv_nnrc (Dv_nnrc_to_dnnrc_dataset (comp_vdbindings config0) d)));
            reflexivity.
        * destruct (H_config (Dv_nnrc (Dv_nnrc_to_java (comp_class_name config0) (comp_java_imports config0) j)));
            try reflexivity.
          rewrite H0; rewrite H3; reflexivity.
        * destruct (H_config (Dv_nnrcmr (Dv_nnrcmr_to_cldmr (comp_brand_rel config0) c)));
            reflexivity.
        * destruct (H_config (Dv_nnrcmr (Dv_nnrcmr_to_spark (comp_qname config0) s)));
            reflexivity.
        * destruct (H_config (Dv_cldmr (Dv_cldmr_to_cloudant (comp_qname config0) (comp_brand_rel config0) c)));
            try reflexivity.
          rewrite H0; rewrite H3; reflexivity.
        * destruct (H_config (Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_dnnrc_typed_dataset (comp_input_type config0) d)));
            reflexivity.
        * destruct (H_config (Dv_dnnrc_typed_dataset
                                (Dv_dnnrc_typed_dataset_to_spark2 (comp_input_type config0) (comp_qname config0) s)));
            try reflexivity.
          rewrite H0; rewrite H3; reflexivity.
  Qed.

  Theorem driver_of_path_completeness:
    forall dv,
    forall config,
      no_dv_error dv ->
      is_driver_config config dv ->
      exists target_lang path,
        driver_of_path config (path ++ target_lang :: nil) = dv.
  Proof.
    intros dv config H_no_dv_error H_dv_config.
    unfold driver_of_path.
    exists (target_language_of_driver dv).
    assert (is_postfix_driver (driver_of_language (target_language_of_driver dv)) dv) as Hpost;
      [ apply (target_language_of_driver_is_postfix dv H_no_dv_error) | ].
    generalize (driver_of_rev_path_completeness dv ((driver_of_language (target_language_of_driver dv))) config H_dv_config Hpost).
    intros H_exists.
    destruct H_exists.
    exists (List.rev x).
    rewrite List.rev_unit.
    rewrite List.rev_involutive.
    assumption.
  Qed.

  End CompDriverConfig.

  Section CompPaths.
    Local Open Scope string_scope.

    Definition get_path_from_source_target (source:language) (target:language) : list language :=
      match source, target with
      (* From rule: *)
      | L_rule, L_rule =>
        L_rule
          :: nil
      | L_rule, L_camp =>
        L_rule
          :: L_camp
          :: nil
      | L_rule, L_nra =>
        L_rule
          :: L_nra
          :: L_nra
          :: nil
      | L_rule, L_nraenv =>
        L_rule
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_rule, L_nnrc =>
        L_rule
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_rule, L_javascript =>
        L_rule
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_javascript
          :: nil
      | L_rule, L_java =>
        L_rule
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_rule, L_nnrcmr =>
        L_rule
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_rule, L_spark =>
        L_rule
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark
          :: nil
      | L_rule, L_cldmr =>
        L_rule
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: nil
      | L_rule, L_cloudant =>
        L_rule
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: L_cloudant
          :: nil
      | L_rule, L_dnnrc_dataset =>
        L_rule
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: nil
      | L_rule, L_dnnrc_typed_dataset =>
        L_rule
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: nil
      | L_rule, L_spark2 =>
        L_rule
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: L_spark2
          :: nil
      (* From camp: *)
      | L_camp, L_camp =>
        L_camp
          :: nil
      | L_camp, L_nra =>
        L_camp
          :: L_nra
          :: L_nra
          :: nil
      | L_camp, L_nraenv =>
        L_camp
          :: L_nraenv
          :: L_nraenv
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
      | L_camp, L_nnrcmr =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_camp, L_spark =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark
          :: nil
      | L_camp, L_cldmr =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: nil
      | L_camp, L_cloudant =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: L_cloudant
          :: nil
      | L_camp, L_dnnrc_dataset =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: nil
      | L_camp, L_dnnrc_typed_dataset =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: nil
      | L_camp, L_spark2 =>
        L_camp
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: L_spark2
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
      | L_oql, L_nra =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nra
          :: nil
      | L_oql, L_nnrc =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_oql, L_camp =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_camp
          :: nil
      | L_oql, L_javascript =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
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
      | L_oql, L_nnrcmr =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_oql, L_spark =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark
          :: nil
      | L_oql, L_cldmr =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: nil
      | L_oql, L_cloudant =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: L_cloudant
          :: nil
      | L_oql, L_dnnrc_dataset =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: nil
      | L_oql, L_dnnrc_typed_dataset =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: nil
      | L_oql, L_spark2 =>
        L_oql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: L_spark2
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
      | L_sql, L_nra =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nra
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
          :: L_camp
          :: nil
      | L_sql, L_javascript =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
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
      | L_sql, L_nnrcmr =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_sql, L_spark =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark
          :: nil
      | L_sql, L_cldmr =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: nil
      | L_sql, L_cloudant =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: L_cloudant
          :: nil
      | L_sql, L_dnnrc_dataset =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: nil
      | L_sql, L_dnnrc_typed_dataset =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: nil
      | L_sql, L_spark2 =>
        L_sql
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: L_spark2
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
      | L_lambda_nra, L_nra =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nra
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
          :: L_camp
          :: nil
      | L_lambda_nra, L_javascript =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
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
      | L_lambda_nra, L_nnrcmr =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_lambda_nra, L_spark =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark
          :: nil
      | L_lambda_nra, L_cldmr =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: nil
      | L_lambda_nra, L_cloudant =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: L_cloudant
          :: nil
      | L_lambda_nra, L_dnnrc_dataset =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: nil
      | L_lambda_nra, L_dnnrc_typed_dataset =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: nil
      | L_lambda_nra, L_spark2 =>
        L_lambda_nra
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: L_spark2
          :: nil
      (* From nra: *)
      | L_nra, L_nra =>
        L_nra
          :: L_nra
          :: nil
      | L_nra, L_nraenv =>
        L_nra
          :: L_nra
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_nra, L_nnrc =>
        L_nra
          :: L_nra
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_nra, L_camp =>
        L_nra
          :: L_nra
          :: L_nnrc
          :: L_nnrc
          :: L_camp
          :: nil
      | L_nra, L_javascript =>
        L_nra
          :: L_nra
          :: L_nnrc
          :: L_nnrc
          :: L_javascript
          :: nil
      | L_nra, L_java =>
        L_nra
          :: L_nra
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_nra, L_nnrcmr =>
        L_nra
          :: L_nra
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_nra, L_spark =>
        L_nra
          :: L_nra
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark
          :: nil
      | L_nra, L_cldmr =>
        L_nra
          :: L_nra
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: nil
      | L_nra, L_cloudant =>
        L_nra
          :: L_nra
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: L_cloudant
          :: nil
      | L_nra, L_dnnrc_dataset =>
        L_nra
          :: L_nra
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: nil
      | L_nra, L_dnnrc_typed_dataset =>
        L_nra
          :: L_nra
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: nil
      | L_nra, L_spark2 =>
        L_nra
          :: L_nra
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: L_spark2
          :: nil
      (* From nraenv: *)
      | L_nraenv, L_nraenv =>
        L_nraenv
          :: L_nraenv
          :: nil
      | L_nraenv, L_nra =>
        L_nraenv
          :: L_nraenv
          :: L_nra
          :: nil
      | L_nraenv, L_nnrc =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: nil
      | L_nraenv, L_camp =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_camp
          :: nil
      | L_nraenv, L_javascript =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_javascript
          :: nil
      | L_nraenv, L_java =>
        L_nraenv
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_nraenv, L_nnrcmr =>
        L_nraenv
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_nraenv, L_spark =>
        L_nraenv
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark
          :: nil
      | L_nraenv, L_cldmr =>
        L_nraenv
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: nil
      | L_nraenv, L_cloudant =>
        L_nraenv
          :: L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: L_cloudant
          :: nil
      | L_nraenv, L_dnnrc_dataset =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: nil
      | L_nraenv, L_dnnrc_typed_dataset =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: nil
      | L_nraenv, L_spark2 =>
        L_nraenv
          :: L_nraenv
          :: L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: L_spark2
          :: nil
      (* From nnrc: *)
      | L_nnrc, L_nnrc =>
        L_nnrc
          :: L_nnrc
          :: nil
      | L_nnrc, L_camp =>
        L_nnrc
          :: L_nnrc
          :: L_camp
          :: nil
      | L_nnrc, L_nraenv =>
        L_nnrc
          :: L_nnrc
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_nnrc, L_nra =>
        L_nnrc
          :: L_nnrc
          :: L_camp
          :: L_nra
          :: L_nra
          :: nil
      | L_nnrc, L_javascript =>
        L_nnrc
          :: L_nnrc
          :: L_javascript
          :: nil
      | L_nnrc, L_java =>
        L_nnrc
          :: L_nnrc
          :: L_java
          :: nil
      | L_nnrc, L_nnrcmr =>
        L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_nnrc, L_spark =>
        L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_spark
          :: nil
      | L_nnrc, L_cldmr =>
        L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: nil
      | L_nnrc, L_cloudant =>
        L_nnrc
          :: L_nnrc
          :: L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: L_cloudant
          :: nil
      | L_nnrc, L_dnnrc_dataset =>
        L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: nil
      | L_nnrc, L_dnnrc_typed_dataset =>
        L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: nil
      | L_nnrc, L_spark2 =>
        L_nnrc
          :: L_nnrc
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: L_spark2
          :: nil
      (* From nnrcmr: *)
      | L_nnrcmr, L_nnrcmr =>
        L_nnrcmr
          :: L_nnrcmr
          :: nil
      | L_nnrcmr, L_spark =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_spark
          :: nil
      | L_nnrcmr, L_cldmr =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: nil
      | L_nnrcmr, L_cloudant =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_cldmr
          :: L_cloudant
          :: nil
      | L_nnrcmr, L_dnnrc_dataset =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_dnnrc_dataset
          :: nil
      | L_nnrcmr, L_dnnrc_typed_dataset =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: nil
      | L_nnrcmr, L_spark2 =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: L_spark2
          :: nil
      | L_nnrcmr, L_nnrc =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: nil
      | L_nnrcmr, L_javascript =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
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
          :: L_camp
          :: nil
      | L_nnrcmr, L_nraenv =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_camp
          :: L_nraenv
          :: L_nraenv
          :: nil
      | L_nnrcmr, L_nra =>
        L_nnrcmr
          :: L_nnrcmr
          :: L_nnrc
          :: L_nnrc
          :: L_camp
          :: L_nra
          :: L_nra
          :: nil
      (* From cldmr: *)
      | L_cldmr, L_cldmr =>
        L_cldmr
          :: nil
      | L_cldmr, L_cloudant =>
        L_cldmr
          :: L_cloudant
          :: nil
      (* From dnnrc_dataset: *)
      | L_dnnrc_dataset, L_dnnrc_dataset =>
        L_dnnrc_dataset
          :: nil
      | L_dnnrc_dataset, L_dnnrc_typed_dataset =>
        L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: nil
      | L_dnnrc_dataset, L_spark2 =>
        L_dnnrc_dataset
          :: L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: L_spark2
          :: nil
      (* From dnnrc_typed_dataset: *)
      | L_dnnrc_typed_dataset, L_dnnrc_typed_dataset =>
        L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: nil
      | L_dnnrc_typed_dataset, L_spark2 =>
        L_dnnrc_typed_dataset
          :: L_dnnrc_typed_dataset
          :: L_spark2
          :: nil
      (* From javascript *)
      | L_javascript, L_javascript =>
        L_javascript :: nil
      (* From java *)
      | L_java, L_java =>
        L_java :: nil
      (* From spark2 *)
      | L_spark2, L_spark2 =>
        L_spark2 :: nil
      (* From spark *)
      | L_spark, L_spark =>
        L_spark :: nil
      | L_cloudant, L_cloudant =>
        L_cloudant :: nil
      | _, _ =>
        let err :=
            "No default path defined from "++(name_of_language source)++" to "++(name_of_language target)
        in
        L_error err :: nil
      end.

    Property get_path_from_source_target_correct:
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

    Definition no_L_error (lang: language) : Prop :=
    match lang with
    | L_error _ => False
    | _ => True
    end.

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
      destruct source; simpl; trivial.
    Qed.

    Property exists_path_from_source_target_trans
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

    Lemma exists_path_from_source_target_completeness_cloudant :
      (forall dv,
          exists_path_from_source_target L_cloudant (target_language_of_driver (Dv_cloudant dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.
    
    Hint Resolve exists_path_from_source_target_completeness_cloudant : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_cldmr :
      (forall dv,
          exists_path_from_source_target L_cldmr (target_language_of_driver (Dv_cldmr dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.
    
    Hint Resolve exists_path_from_source_target_completeness_cldmr : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_spark2 :
      (forall dv,
          exists_path_from_source_target L_spark2 (target_language_of_driver (Dv_spark2 dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.
    
    Hint Resolve exists_path_from_source_target_completeness_spark2 : exists_path_hints.
    
    Lemma exists_path_from_source_target_completeness_dnnrc_typed_dataset :
      (forall dv,
          exists_path_from_source_target L_dnnrc_typed_dataset (target_language_of_driver (Dv_dnnrc_typed_dataset dv))).
    Proof.
      induction dv; prove_exists_path_complete.
    Qed.
    
    Hint Resolve exists_path_from_source_target_completeness_dnnrc_typed_dataset : exists_path_hints.
    
    Lemma exists_path_from_source_target_completeness_dnnrc_dataset :
      (forall dv,
          exists_path_from_source_target L_dnnrc_dataset (target_language_of_driver (Dv_dnnrc_dataset dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.
    
    Hint Resolve exists_path_from_source_target_completeness_dnnrc_dataset : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_spark :
      (forall dv,
          exists_path_from_source_target L_spark (target_language_of_driver (Dv_spark dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.
    
    Hint Resolve exists_path_from_source_target_completeness_spark : exists_path_hints.
    
    Lemma exists_path_from_source_target_completeness_cnd :
        (forall dv,
            exists_path_from_source_target L_camp (target_language_of_driver (Dv_camp dv)))
        /\ 
        (forall dv,
            exists_path_from_source_target L_nra (target_language_of_driver (Dv_nra dv)))
        /\ 
        (forall dv,
            exists_path_from_source_target L_nraenv (target_language_of_driver (Dv_nraenv dv)))
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
    Lemma exists_path_from_source_target_completeness_nraenv :
      (forall dv,
          exists_path_from_source_target L_nraenv (target_language_of_driver (Dv_nraenv dv))).
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
    Hint Resolve exists_path_from_source_target_completeness_nraenv : exists_path_hints.
    Hint Resolve exists_path_from_source_target_completeness_nnrc : exists_path_hints.
    Hint Resolve exists_path_from_source_target_completeness_nnrcmr : exists_path_hints.

    Lemma exists_path_from_source_target_completeness_rule :
        (forall dv,
            exists_path_from_source_target L_rule (target_language_of_driver (Dv_rule dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_rule : exists_path_hints.

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

    Lemma exists_path_from_source_target_completeness_lambda_nra :
        (forall dv,
            exists_path_from_source_target L_lambda_nra (target_language_of_driver (Dv_lambda_nra dv))).
    Proof.
      destruct dv; prove_exists_path_complete.
    Qed.

    Hint Resolve exists_path_from_source_target_completeness_lambda_nra : exists_path_hints.

    Property exists_path_from_source_target_completeness:
      forall dv,
        no_dv_error dv ->
        let source := language_of_driver dv in
        let target := target_language_of_driver dv in
        exists_path_from_source_target source target.
    Proof.
      destruct dv; simpl
      ;  auto with exists_path_hints.
      - etransitivity; [ | eauto with exists_path_hints ].
        reflexivity.
    Qed.

    (* Comp *)
    (* XXX TODO : use driver *)
    Definition get_driver_from_source_target (conf: driver_config) (source:language) (target:language) : driver :=
      let path := get_path_from_source_target source target in
      driver_of_path conf path.

    (* Some macros, that aren't really just about source-target *)

    Definition default_dv_config :=
      mkDvConfig
        (* comp_qname = *) "query"
        (* class_name = *) "query"
        (* comp_brand_rel = *) nil
        (* comp_input_type = *) RType.Unit
        (* comp_mr_vinit = *) init_vinit
        (* comp_vdbindings = *) nil
        (* comp_java_imports = *) "".

    Definition compile_from_source_target (conf: driver_config) (source:language) (target:language) (q: query) : query :=
      let path := get_path_from_source_target source target in
      let dv := driver_of_path conf path in
      match List.rev (compile dv q) with
      | nil => Q_error "No compilation result!"
      | target :: _ => target
      end.


    (* Used in CompTest: *)
    Definition rule_to_nraenv_optim (q: rule) : nraenv :=
      (nraenv_optim (rule_to_nraenv q)).
    Definition rule_to_nnrc_optim (q: rule) : nnrc :=
      nnrc_optim (nraenv_to_nnrc (nraenv_optim (rule_to_nraenv q))).

    (* Used in CALib: *)
    Definition nraenv_optim_to_nnrc_optim (q:nraenv) : nnrc :=
      nnrc_optim (nraenv_to_nnrc (nraenv_optim q)).
    Definition nraenv_optim_to_nnrc_optim_to_dnnrc (inputs_loc:vdbindings) (q:nraenv) : dnnrc_dataset :=
      nnrc_to_dnnrc_dataset inputs_loc (nnrc_optim (nraenv_to_nnrc (nraenv_optim q))).
    Definition nraenv_optim_to_nnrc_optim_to_nnrcmr_comptop_optim (q:nraenv) : nrcmr :=
      nnrcmr_optim (nnrc_to_nnrcmr_comptop init_vinit (nnrc_optim (nraenv_to_nnrc (nraenv_optim q)))).


    (* Used in queryTests: *)
    Definition rule_to_nraenv_to_nnrc_optim (q:rule) : nnrc :=
      nnrc_optim (nraenv_to_nnrc (nraenv_optim (rule_to_nraenv q))).
    Definition rule_to_nraenv_to_nnrc_optim_to_dnnrc
               (inputs_loc:vdbindings) (q:rule) : dnnrc_dataset :=
      nnrc_to_dnnrc_dataset inputs_loc (nnrc_optim (nraenv_to_nnrc (nraenv_optim (rule_to_nraenv q)))).
    Definition rule_to_nraenv_to_nnrc_optim_to_javascript (q:rule) : string :=
      nnrc_to_javascript (nnrc_optim (nraenv_to_nnrc (nraenv_optim (rule_to_nraenv q)))).
    Definition rule_to_nnrcmr (q:rule) : nnrcmr :=
      nnrcmr_optim (nnrc_to_nnrcmr_comptop init_vinit (rule_to_nraenv_to_nnrc_optim q)).
    Definition rule_to_cldmr (h:list (string*string)) (q:rule) : cldmr :=
      nnrcmr_to_cldmr h (nnrcmr_optim (nnrc_to_nnrcmr_comptop init_vinit (rule_to_nraenv_to_nnrc_optim q))).

  End CompPaths.

End CompDriver.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
