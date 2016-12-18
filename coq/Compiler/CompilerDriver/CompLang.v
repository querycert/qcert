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

Section CompLang.

  Require Import String.
  Require Import NRARuntime.
  Require Import NRAEnvRuntime.
  Require Import NNRCRuntime.
  Require Import NNRCMRRuntime.
  Require Import CldMR.
  Require Import DNNRC Dataset.
  Require Import CAMPRuntime.
  Require Import ODMGRuntime.

  Require Import BasicSystem.

  Require Import NNRCMRtoDNNRC.
  Require Import TDNRCInfer.
  Require Import LambdaNRA.
  Require Import SQL.
  
  Require Rule.

  Definition vdbindings := vdbindings.

  (* Languages *)
  Context {ft:foreign_type}.
  Context {bm:brand_model}.

  Context {fr:foreign_runtime}.
  Context {fredop:foreign_reduce_op}.

  Definition rule := rule.
  Definition camp := pat.
  Definition oql := oql.
  Definition sql := sql.
  Definition lambda_nra := lalg.
  Definition nra := alg.
  Definition nraenv_core := algenv.
  Definition nraenv := nraenv.
  Definition nnrc_core := nnrc_core.
  Definition nnrc := nnrc.
  Definition nnrcmr := nnrcmr.
  Definition cldmr := cld_mrl.
  Definition dnnrc_dataset := dnnrc _ unit dataset.
  Definition dnnrc_typed_dataset {bm:brand_model} := dnnrc _ (type_annotation unit) dataset.
  Definition javascript := string.
  Definition java := string.
  Definition spark := string.
  Definition spark2 := string.
  Definition cloudant := (list (string * string) * (string * list string))%type.

  Inductive language : Set :=
    | L_rule : language
    | L_camp : language
    | L_oql : language
    | L_sql : language
    | L_lambda_nra : language
    | L_nra : language
    | L_nraenv_core : language
    | L_nraenv : language
    | L_nnrc_core : language
    | L_nnrc : language
    | L_nnrcmr : language
    | L_cldmr : language
    | L_dnnrc_dataset : language
    | L_dnnrc_typed_dataset : language
    | L_javascript : language
    | L_java : language
    | L_spark : language
    | L_spark2 : language
    | L_cloudant : language
    | L_error : string -> language.

  Inductive query : Set :=
    | Q_rule : rule -> query
    | Q_camp : camp -> query
    | Q_oql : oql -> query
    | Q_sql : sql -> query
    | Q_lambda_nra : lambda_nra -> query
    | Q_nra : nra -> query
    | Q_nraenv_core : nraenv_core -> query
    | Q_nraenv : nraenv -> query
    | Q_nnrc_core : nnrc_core -> query
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

  Tactic Notation "query_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "Q_rule"%string
    | Case_aux c "Q_camp"%string
    | Case_aux c "Q_oql"%string
    | Case_aux c "Q_sql"%string
    | Case_aux c "Q_lambda_nra"%string
    | Case_aux c "Q_nra"%string
    | Case_aux c "Q_nraenv_core"%string
    | Case_aux c "Q_nraenv"%string
    | Case_aux c "Q_nnrc_core"%string
    | Case_aux c "Q_nnrc"%string
    | Case_aux c "Q_nnrcmr"%string
    | Case_aux c "Q_cldmr"%string
    | Case_aux c "Q_dnnrc_dataset"%string
    | Case_aux c "Q_dnnrc_typed_dataset"%string
    | Case_aux c "Q_javascript"%string
    | Case_aux c "Q_java"%string
    | Case_aux c "Q_spark"%string
    | Case_aux c "Q_spark2"%string
    | Case_aux c "Q_cloudant"%string
    | Case_aux c "Q_error"%string].


  Section CompLangUtil.

  Definition language_of_name_case_sensitive name : language:=
    match name with
    | "rule"%string => L_rule
    | "camp"%string => L_camp
    | "oql"%string => L_oql
    | "sql"%string => L_sql
    | "lambda_nra"%string => L_lambda_nra
    | "nra"%string => L_nra
    | "nraenv_core"%string => L_nraenv_core
    | "nraenv"%string => L_nraenv
    | "nnrc_core"%string => L_nnrc_core
    | "nnrc"%string => L_nnrc
    | "nnrcmr"%string => L_nnrcmr
    | "cldmr"%string => L_cldmr
    | "dnnrc"%string => L_dnnrc_dataset
    | "dnnrc_typed"%string => L_dnnrc_typed_dataset
    | "js"%string | "rhino"%string | "javascript"%string => L_javascript
    | "java"%string => L_java
    | "spark"%string => L_spark
    | "spark2"%string => L_spark2
    | "cloudant"%string => L_cloudant
    | "error"%string => L_error ""
    | _ => L_error ("'"++name++"' is not a language name")
    end.

  Definition name_of_language lang :=
    match lang with
    | L_rule => "rule"%string
    | L_camp => "camp"%string
    | L_oql => "oql"%string
    | L_sql => "sql"%string
    | L_lambda_nra => "lambda_nra"%string
    | L_nra => "nra"%string
    | L_nraenv_core => "nraenv_core"%string
    | L_nraenv => "nraenv"%string
    | L_nnrc_core => "nnrc_core"%string
    | L_nnrc => "nnrc"%string
    | L_nnrcmr => "nnrcmr"%string
    | L_cldmr => "cldmr"%string
    | L_dnnrc_dataset => "dnnrc"%string
    | L_dnnrc_typed_dataset => "dnnrc_typed"%string
    | L_javascript => "js"%string
    | L_java => "java"%string
    | L_spark => "spark"%string
    | L_spark2 => "spark2"%string
    | L_cloudant => "cloudant"%string
    | L_error _ => "error"%string
    end.

  Definition language_of_query q :=
    match q with
    | Q_rule _ => L_rule
    | Q_camp _ => L_camp
    | Q_oql _ => L_oql
    | Q_sql _ => L_sql
    | Q_lambda_nra _ => L_lambda_nra
    | Q_nra _ => L_nra
    | Q_nraenv_core _ => L_nraenv_core
    | Q_nraenv _ => L_nraenv
    | Q_nnrc_core _ => L_nnrc_core
    | Q_nnrc _ => L_nnrc
    | Q_nnrcmr _ => L_nnrcmr
    | Q_cldmr _ => L_cldmr
    | Q_dnnrc_dataset _ => L_dnnrc_dataset
    | Q_dnnrc_typed_dataset _ => L_dnnrc_typed_dataset
    | Q_javascript _ => L_javascript
    | Q_java _ => L_java
    | Q_spark _ => L_spark
    | Q_spark2 _ => L_spark2
    | Q_cloudant _ => L_cloudant
    | Q_error err =>
      L_error ("No language corresponding to error query '"++err++"'")
    end.

  Definition name_of_query q :=
    name_of_language (language_of_query q).


  End CompLangUtil.

End CompLang.

Tactic Notation "language_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "L_rule"%string
  | Case_aux c "L_camp"%string
  | Case_aux c "L_oql"%string
  | Case_aux c "L_sql"%string
  | Case_aux c "L_lambda_nra"%string
  | Case_aux c "L_nra"%string
  | Case_aux c "L_nraenv_core"%string
  | Case_aux c "L_nraenv"%string
  | Case_aux c "L_nnrc_core"%string
  | Case_aux c "L_nnrc"%string
  | Case_aux c "L_nnrcmr"%string
  | Case_aux c "L_cldmr"%string
  | Case_aux c "L_dnnrc_dataset"%string
  | Case_aux c "L_dnnrc_typed_dataset"%string
  | Case_aux c "L_javascript"%string
  | Case_aux c "L_java"%string
  | Case_aux c "L_spark"%string
  | Case_aux c "L_spark2"%string
  | Case_aux c "L_cloudant"%string
  | Case_aux c "L_error"%string].


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
