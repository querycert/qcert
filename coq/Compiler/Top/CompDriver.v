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
Require Import DNNRC SparkIR.
Require Import CAMPRuntime.
Require Import ODMGRuntime.

Require Import CompilerRuntime.
Module CompDriver(runtime:CompilerRuntime).

  Require Import RuletoNRA PatterntoNRA PatterntoNRAEnv NRAtoNNRC NRAEnvtoNNRC.
  Require Import CompCore.
  Require Import TRewFunc.
  Require Import CompUtil.
  Require Import CompFront.
  Require Import NNRCtoJavascript.
  Require Import NNRCtoJava.
  Require Import NNRCtoNNRCMR.
  Require Import NNRCMRtoNNRC.
  Require Import NNRCMRtoSpark ForeignToSpark.
  Require Import NNRCMRtoCloudant ForeignToCloudant.
  Require Import NNRCMRtoDNNRC.
  Require Import CloudantMRtoJavascript.
  Require Import NNRCtoDNNRC.
  Require Import TDNRCInfer DNNRCtoScala DNNRCSparkIRRewrites.

  Module CF := CompFront runtime.
  Module CC := CompCore runtime.

  Local Open Scope list_scope.


  (* Languages *)

  Definition rule := rule.
  Definition camp := pat.
  Definition oql := oql_expr.
  Definition nra := alg.
  Definition nraenv := algenv.
  Definition nnrc := nrc.
  Definition nnrcmr := nrcmr.
  Definition cldmr := cld_mrl.
  Definition dnnrc_dataset := dnrc _ unit dataset.
  Definition dnnrc_typed_dataset := dnrc _ unit (* (type_annotation unit) *) dataset. (* XXXXXXX TODO XXXX *)
  Definition javascript := string.
  Definition java := string.
  Definition spark := string.
  Definition spark2 := string.
  Definition cloudant := (list (string * string) * (string * list string))%type.

  Inductive query : Set :=
    | Q_rule : rule -> query
    | Q_camp : camp -> query
    | Q_oql : oql -> query
    | Q_nra : nra -> query
    | Q_nraenv : nraenv -> query
    | Q_nnrc : nnrc -> query
    | Q_nnrcmr : nnrcmr -> query
    | Q_cldmr : cldmr -> query
    | Q_dnnrc_dataset : dnnrc_dataset -> query
    | Q_dnnrc_typed_dataset : dnnrc_typed_dataset -> query
    | Q_javascript : javascript -> query
    | Q_java : java -> query
    | Q_spark : spark -> query
    | Q_spark2 : spark2 -> query
    | Q_cloudant : cloudant -> query
    | Q_error : string -> query.

  (* Translation functions *)

  Definition oql_to_nraenv (q:oql) : nraenv := CF.translate_oql_to_algenv q.

  Definition rule_to_nraenv (q:rule) : nraenv := CF.translate_rule_to_algenv q.

  Definition rule_to_camp (q:rule) : camp := rule_to_pattern q.

  Definition rule_to_nra (q:rule) : nra := alg_of_rule q.

  Definition camp_to_nraenv (q:camp) : nraenv := CF.translate_pat_to_algenv q.

  Definition camp_to_nra (q:camp) : nra := alg_of_pat q.

  Definition nraenv_optim (q: nraenv) : nraenv := CC.toptimize_algenv_typed_opt q.

  Definition nraenv_compiler (q: nraenv) : nnrc := CC.tcompile_nraenv_to_nnrc_typed_opt q.

  Definition nraenv_to_nnrc (q: nraenv) : nnrc := algenv_to_nnrc q init_vid init_venv.

  Definition nraenv_to_nra (q: nraenv) : nra := alg_of_algenv q.

  Definition nra_to_nraenv (q: nra) : nraenv := algenv_of_alg q.

  Definition nra_optim (q: nra) : nra :=
    let nraenv_opt := (CC.toptimize_algenv_typed_opt (algenv_of_alg q)) in
    if is_nra_fun nraenv_opt then
      deenv_alg nraenv_opt
    else
      alg_of_algenv nraenv_opt.

  Definition nra_to_nnrc (q: nra) : nnrc := nra_to_nnrc q init_vid.

  Definition nnrc_optim (q: nnrc) : nnrc := trew q.

  Definition nnrc_to_nnrcmr (inputs_loc: vdbindings) (q: nnrc) : nnrcmr :=
    let inputs_loc :=
        (init_vid, Vlocal)
          ::(init_vinit, Vlocal)
          :: inputs_loc
    in
    nnrc_to_nnrcmr_chain q
                         init_vinit
                         inputs_loc.

  Definition nnrcmr_optim (q: nnrcmr) : nnrcmr := mr_optimize q.

  Definition nnrcmr_to_nnrc (q: nnrcmr) : option nnrc := nnrc_of_nrcmr q.

  Definition nnrcmr_to_dnnrc_dataset (q: nnrcmr) : option dnnrc_dataset := dnnrc_of_nrcmr tt q.

  Definition nnrcmr_to_cldmr  (h:list (string*string)) (q: nnrcmr) : cldmr :=
    let q := foreign_to_cloudant_prepare_nrcmr q in
    let q := mr_optimize q in                              (* XXXXXXXXXXX optim XXXXXXXX *)
    let q := foreign_to_cloudant_prepare_nrcmr q in
    let q := nrcmr_rename_for_cloudant q in
    NNRCMRtoNNRCMRCloudantTop h q.

  Definition nnrcmr_to_spark (rulename: string) (q: nrcmr) : spark :=
    let q := foreign_to_spark_prepare_nrcmr q in
    let q := mr_optimize q in                              (* XXXXXXXXXXX optim XXXXXXXX *)
    let q := foreign_to_spark_prepare_nrcmr q in
    let q := nrcmr_rename_for_spark q in
    nrcmrToSparkTopDataFromFileTop rulename init_vinit q. (* XXX init_vinit should be a parameter? *)

  Definition cldmr_to_cloudant (rulename:string) (h:list (string*string)) (q:cldmr) : cloudant :=
    mapReducePairstoCloudant h q rulename.

  Definition nnrc_to_dnnrc_dataset (q: nnrc) : dnnrc_dataset :=
    @nrc_to_dnrc_dataset _ _ unit tt mkDistLoc q.

  Definition nnrc_to_javascript (q: nnrc) : javascript := (* XXX Check XXX *)
    nrcToJSTop q.

  Definition nnrc_to_java (class_name:string) (imports:string) (q: nnrc) : java := (* XXX Check XXX *)
    nrcToJavaTop class_name imports q.



  (* Drivers *)

  Inductive rule_driver : Set :=
    | Dv_rule : rule_driver
    | Dv_rule_to_camp : camp_driver -> rule_driver
    | Dv_rule_to_nraenv : nraenv_driver -> rule_driver
    | Dv_rule_to_nra : nra_driver -> rule_driver

  with camp_driver : Set :=
    | Dv_camp : camp_driver
    | Dv_camp_to_nraenv : nraenv_driver -> camp_driver
    | Dv_camp_to_nra : nra_driver -> camp_driver

  with oql_driver : Set :=
    | Dv_oql : oql_driver
    | Dv_oql_to_nraenv : nraenv_driver -> oql_driver

  with nra_driver : Set :=
    | Dv_nra : nra_driver
    | Dv_nra_optim : nra_driver -> nra_driver
    | Dv_nra_to_nnrc : nnrc_driver -> nra_driver
    | Dv_nra_to_nraenv : nraenv_driver -> nra_driver

  with nraenv_driver : Set :=
    | Dv_nraenv : nraenv_driver
    | Dv_nraenv_optim : nraenv_driver -> nraenv_driver
    | Dv_nraenv_to_nnrc : nnrc_driver -> nraenv_driver
    | Dv_nraenv_to_nra : nra_driver -> nraenv_driver

  with nnrc_driver : Set :=
    | Dv_nnrc : nnrc_driver
    | Dv_nnrc_optim : nnrc_driver -> nnrc_driver
    | Dv_nnrc_to_nnrcmr : (* inputs_loc *) vdbindings ->nnrcmr_driver -> nnrc_driver
    | Dv_nnrc_to_dnnrc_dataset : dnnrc_dataset_driver -> nnrc_driver
    | Dv_nnrc_to_javascript : javascript_driver -> nnrc_driver
    | Dv_nnrc_to_java : (* class_name *) string -> (* imports *) string -> java_driver -> nnrc_driver

  with nnrcmr_driver : Set :=
    | Dv_nnrcmr : nnrcmr_driver
    | Dv_nnrcmr_optim : nnrcmr_driver -> nnrcmr_driver
    | Dv_nnrcmr_to_spark : (* rulename *) string -> spark_driver -> nnrcmr_driver
    | Dv_nnrcmr_to_nnrc : nnrc_driver -> nnrcmr_driver
    | Dv_nnrcmr_to_dnnrc_dataset : dnnrc_dataset_driver -> nnrcmr_driver
    | Dv_nnrcmr_to_cldmr : (* h *) list (string*string) -> cldmr_driver -> nnrcmr_driver

  with cldmr_driver : Set :=
    | Dv_cldmr : cldmr_driver
    | Dv_cldmr_to_cloudant : (* rulename *) string -> (* h *) list (string*string) -> cloudant_driver -> cldmr_driver

  with dnnrc_dataset_driver : Set :=
    | Dv_dnnrc_dataset : dnnrc_dataset_driver
    (* XXX TODO XXX *)
    (* | Dv_dnnrc_dataset_to_dnnrc_typed_dataset : dnnrc_typed_dataset -> dnnrc_dataset_driver *)

  with dnnrc_typed_dataset_driver : Set :=
    | Dv_dnnrc_typed_dataset : dnnrc_typed_dataset_driver
    (* XXX TODO XXX *)
    (* | Dv_dnnrc_typed_dataset_optim : dnnrc_typed_dataset_driver -> dnnrc_typed_dataset_driver *)
    (* | Dv_dnnrc_typed_dataset_to_spark2 : spark2_driver -> dnnrc_typed_dataset_driver *)

  with javascript_driver : Set :=
    | Dv_javascript : javascript_driver

  with java_driver : Set :=
    | Dv_java : java_driver

  with spark_driver : Set :=
    | Dv_spark : spark_driver

  with spark2_driver : Set :=
    | Dv_spark2 : spark2_driver

  with cloudant_driver : Set :=
    | Dv_cloudant : cloudant_driver.

  (* Compilers function *)

  Fixpoint compile_rule (dv: rule_driver) (q: rule) : list query :=
    let queries :=
        match dv with
        | Dv_rule => nil
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
    (Q_rule q) :: queries

  with compile_camp (dv: camp_driver) (q: camp) : list query :=
    let queries :=
        match dv with
        | Dv_camp => nil
        | Dv_camp_to_nraenv dv =>
          let q := camp_to_nraenv q in
          compile_nraenv dv q
        | Dv_camp_to_nra dv =>
          let q := camp_to_nra q in
          compile_nra dv q
        end
    in
    (Q_camp q) :: queries

  with compile_oql (dv: oql_driver) (q: oql) : list query :=
    let queries :=
        match dv with
        | Dv_oql => nil
        | Dv_oql_to_nraenv dv =>
          let q := oql_to_nraenv q in
          compile_nraenv dv q
        end
    in
    (Q_oql q) :: queries

  with compile_nra (dv: nra_driver) (q: nra) : list query :=
    let queries :=
        match dv with
        | Dv_nra => nil
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
        | Dv_nraenv => nil
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
        | Dv_nnrc => nil
        | Dv_nnrc_optim dv =>
          let q := nnrc_optim q in
          compile_nnrc dv q
        | Dv_nnrc_to_nnrcmr inputs_loc dv =>
          let q := nnrc_to_nnrcmr inputs_loc q in
          compile_nnrcmr dv q
        | Dv_nnrc_to_dnnrc_dataset dv =>
          let q := nnrc_to_dnnrc_dataset q in
          compile_dnnrc_dataset dv q
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
        | Dv_nnrcmr => nil
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
    (Q_nnrcmr q) :: queries

  with compile_cldmr (dv: cldmr_driver) (q: cldmr) : list query :=
    let queries :=
        match dv with
        | Dv_cldmr => nil
        | Dv_cldmr_to_cloudant rulename h dv =>
          let q := cldmr_to_cloudant rulename h q in
          compile_cloudant dv q
        end
    in
    (Q_cldmr q) :: queries

  with compile_dnnrc_dataset (dv: dnnrc_dataset_driver) (q: dnnrc_dataset) : list query :=
    let queries :=
        match dv with
        | Dv_dnnrc_dataset => nil
        end
    in
    (Q_dnnrc_dataset q) :: queries

  with compile_dnnrc_typed_dataset (dv: dnnrc_typed_dataset_driver) (q: dnnrc_typed_dataset) : list query :=
    let queries :=
        match dv with
        | Dv_dnnrc_typed_dataset => nil
        end
    in
    (Q_dnnrc_typed_dataset q) :: queries

  with compile_javascript (dv: javascript_driver) (q: javascript) : list query :=
    let queries :=
        match dv with
        | Dv_javascript => nil
        end
    in
    (Q_javascript q) :: queries

  with compile_java (dv: java_driver) (q: java) : list query :=
    let queries :=
        match dv with
        | Dv_java => nil
        end
    in
    (Q_java q) :: queries

  with compile_spark (dv: spark_driver) (q: spark) : list query :=
    let queries :=
        match dv with
        | Dv_spark => nil
        end
    in
    (Q_spark q) :: queries

  with compile_spark2 (dv: spark2_driver) (q: spark2) : list query :=
    let queries :=
        match dv with
        | Dv_spark2 => nil
        end
    in
    (Q_spark2 q) :: queries

  with compile_cloudant (dv: cloudant_driver) (q: cloudant) : list query :=
    let queries :=
        match dv with
        | Dv_cloudant => nil
        end
    in
    (Q_cloudant q) :: queries.


End CompDriver.



(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
