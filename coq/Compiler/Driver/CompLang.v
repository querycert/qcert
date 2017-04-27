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
  Require Import List.
  
  Require Import EquivDec.

  Section Lang.
    Inductive language : Set :=
    | L_camp_rule : language
    | L_tech_rule : language
    | L_designer_rule : language
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
    | L_spark_rdd : language
    | L_spark_dataset : language
    | L_cloudant : language
    | L_error : string -> language.

    Lemma language_eq_dec : EqDec language eq.
    Proof.
      repeat red.
      destruct x; destruct y; try solve[right; inversion 1]; try (left; reflexivity).
      - destruct (string_dec s s0).
        + left; f_equal; subst; reflexivity.
        + right; intro; apply n; inversion H; trivial.
    Defined.
  
    Global Instance language_eqdec : EqDec language eq := language_eq_dec.

    Definition language_of_name_case_sensitive name : language:=
      match name with
      | "camp_rule"%string => L_camp_rule
      | "tech_rule"%string => L_tech_rule
      | "designer_rule"%string => L_designer_rule
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
      | "spark_rdd"%string => L_spark_rdd
      | "spark_dataset"%string => L_spark_dataset
      | "cloudant"%string => L_cloudant
      | "error"%string => L_error ""
      | _ => L_error ("'"++name++"' is not a language name")
      end.

    Definition name_of_language lang :=
      match lang with
      | L_camp_rule => "camp_rule"%string
      | L_tech_rule => "tech_rule"%string
      | L_designer_rule => "designer_rule"%string
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
      | L_spark_rdd => "spark_rdd"%string
      | L_spark_dataset => "spark_dataset"%string
      | L_cloudant => "cloudant"%string
      | L_error _ => "error"%string
      end.

    Definition lang_desc : Set := (language * string).

    Inductive language_kind : Set :=
    | FrontEnd : language_kind
    | CoreEnd : language_kind
    | DistrEnd : language_kind
    | BackEnd : language_kind.

    Lemma language_kind_eq_dec : EqDec language_kind eq.
    Proof.
      repeat red.
      destruct x; destruct y; try solve[right; inversion 1]; left; reflexivity.
    Defined.
  
    Global Instance language_kind_eqdec : EqDec language_kind eq := language_kind_eq_dec.

    Open Scope string.
    Definition language_descriptions :=
      (L_sql,FrontEnd,"SQL", "SQL.Lang.SQL", "Structured Query Language")
        :: (L_oql,FrontEnd,"OQL", "OQL.Lang.OQL", "Object Query Language")
        :: (L_lambda_nra,FrontEnd,"λNRA", "LambdaNRA.Lang.LambdaNRA", "Lambda Nested Relational Algebra")
        :: (L_tech_rule,FrontEnd,"TechRule", "TechRule.Lang.TechRule", "Technical Rules")
        :: (L_designer_rule,FrontEnd,"DesignRule","DesignRule.Lang.DesignRule","Designer Rules")
        :: (L_camp_rule,FrontEnd,"CAMPRule","CAMPRule.Lang.CAMPRule","Rules for CAMP")
        :: (L_camp,CoreEnd,"CAMP","CAMP.Lang.CAMP","Calculus of Aggregating Matching Patterns")
        :: (L_nra,CoreEnd,"NRA","NRA.Lang.NRA","Nested Relational Algebra")
        :: (L_nraenv_core,CoreEnd,"cNRAᵉ","NRAEnv.Core.cNRAEnv","Core Nested Relational Algebra with Environments")
        :: (L_nraenv,CoreEnd,"NRAᵉ","NRAEnv.Lang.NRAEnv","Nested Relational Algebra with Environments")
        :: (L_nnrc_core,CoreEnd,"cNNRC","NNRC.Core.cNNRC","Core Named Nested Relational Calculus")
        :: (L_nnrc,CoreEnd,"NNRC","NNRC.Lang.NNRC","Named Nested Relational Calculus")
        :: (L_nnrcmr,DistrEnd,"NNRCMR","NNRCMR.Lang.NNRCMR","Named Nested Relational Calculus with Map/Reduce")
        :: (L_cldmr,DistrEnd,"CldMR","CldMR.Lang.CldMR","Named Nested Relational Calculus with Cloudant Map/Reduce")
        :: (L_dnnrc_dataset,DistrEnd,"DNNRC","DNNRC.Lang.DNNRC","Distributed Named Nested Relational Calculus")
        :: (L_dnnrc_typed_dataset,DistrEnd,"tDNNRC","DNNRC.Lang.DNNRC","Typed Distributed Named Nested Relational Calculus")
        :: (L_javascript,BackEnd,"JS","JS.Lang.JS","JavaScript")
        :: (L_java,BackEnd,"Java","Java.Lang.Java","Java")
        :: (L_spark_rdd,BackEnd,"SparkRDD","SparkRDD.Lang.SparkRDD","Spark (RDD API)")
        :: (L_spark_dataset,BackEnd,"SparkDF","SparkDF.Lang.SparkDF","Spark (Dataframe API)")
        :: (L_cloudant,BackEnd,"Cloudant","Cloudant.Lang.Cloudant","Cloudant Map/Reduce Views")
        :: nil.

    Definition add_id_to_language_description (ld:language * language_kind * string * string * string) :=
      match ld with
      | (lang,kind,label,illoc,desc) =>
        (lang,name_of_language lang,kind,label,illoc,desc)
      end.

    Definition language_descriptions_with_ids :=
      map add_id_to_language_description language_descriptions.

    (* Eval vm_compute in languages_descriptions_with_ids. *)

    Definition check_kind (the_kind:language_kind)
               (ld:language * string * language_kind * string * string * string)
      :=
      match ld with
      | (lang,id,kind,label,illoc,desc) =>
        if (language_kind_eq_dec kind the_kind) then true else false
      end.
    
    Record export_desc :=
      mkExportDesc
      { frontend : list(language * string * language_kind * string * string * string);
        coreend : list(language * string * language_kind * string * string * string);
        distrend : list(language * string * language_kind * string * string * string);
        backend : list(language * string * language_kind * string * string * string) }.
    
    Definition select_description_per_kind
               (ldl: list(language * string * language_kind * string * string * string)) :=
      mkExportDesc
        (filter (check_kind FrontEnd) ldl)
        (filter (check_kind CoreEnd) ldl)
        (filter (check_kind DistrEnd) ldl)
        (filter (check_kind BackEnd) ldl).

    (* Eval vm_compute in (select_description_per_kind language_descriptions_with_ids). *)

    Definition export_language_descriptions : export_desc :=
      select_description_per_kind language_descriptions_with_ids.

  End Lang.

  Section Query.
    Require Import BasicSystem.

    (** Query languages *)
    Require Import SQLRuntime.
    Require Import OQLRuntime.
    Require Import LambdaNRARuntime.
    (** Rule languages *)
    Require Import CAMPRuleRuntime.
    Require Import TechRuleRuntime.
    Require Import DesignRuleRuntime.
    (** Intermediate languages *)
    Require Import NRARuntime.
    Require Import NRAEnvRuntime.
    Require Import NNRCRuntime.
    Require Import NNRCMRRuntime.
    Require Import CldMRRuntime.
    Require Import DNNRCRuntime.
    Require Import CAMPRuntime.

    Require Import NNRCMRtoDNNRC.
    Require Import TDNNRCInfer.
  
    Definition vdbindings := vdbindings.

    (* Languages *)
    Context {ft:foreign_type}.
    Context {bm:brand_model}.

    Context {fr:foreign_runtime}.
    Context {fredop:foreign_reduce_op}.

    Definition camp_rule := camp_rule.
    Definition tech_rule := tech_rule.
    Definition designer_rule := designer_rule.
    Definition camp := camp.
    Definition oql := oql.
    Definition sql := sql.
    Definition lambda_nra := lambda_nra.
    Definition nra := nra.
    Definition nraenv_core := cnraenv.
    Definition nraenv := nraenv.
    Definition nnrc_core := nnrc_core.
    Definition nnrc := nnrc.
    Definition nnrcmr := nnrcmr.
    Definition cldmr := cld_mrl.
    Definition dnnrc_dataset := dnnrc _ unit dataset.
    Definition dnnrc_typed_dataset {bm:brand_model} := dnnrc _ (type_annotation unit) dataset.
    Definition javascript := string.
    Definition java := string.
    Definition spark_rdd := string.
    Definition spark_dataset := string.
    Definition cloudant := (list (string * string) * (string * list string))%type.

    Inductive query : Set :=
    | Q_camp_rule : camp_rule -> query
    | Q_tech_rule : tech_rule -> query
    | Q_designer_rule : designer_rule -> query
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
    | Q_spark_rdd : spark_rdd -> query
    | Q_spark_dataset : spark_dataset -> query
    | Q_cloudant : cloudant -> query
    | Q_error : string -> query.

    Tactic Notation "query_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "Q_camp_rule"%string
      | Case_aux c "Q_tech_rule"%string
      | Case_aux c "Q_designer_rule"%string
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
      | Case_aux c "Q_spark_rdd"%string
      | Case_aux c "Q_spark_dataset"%string
      | Case_aux c "Q_cloudant"%string
      | Case_aux c "Q_error"%string].

    Definition language_of_query q :=
      match q with
      | Q_camp_rule _ => L_camp_rule
      | Q_tech_rule _ => L_tech_rule
      | Q_designer_rule _ => L_designer_rule
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
      | Q_spark_rdd _ => L_spark_rdd
      | Q_spark_dataset _ => L_spark_dataset
      | Q_cloudant _ => L_cloudant
      | Q_error err =>
        L_error ("No language corresponding to error query '"++err++"'")
      end.

    Definition name_of_query q :=
      name_of_language (language_of_query q).

    (* given a language, returns the type of that language *)
    Definition type_of_language (l:language) : Set :=
      match l with
      | L_camp_rule => camp_rule
      | L_tech_rule => tech_rule
      | L_designer_rule => designer_rule
      | L_camp => camp
      | L_oql => oql
      | L_sql => sql
      | L_lambda_nra => lambda_nra
      | L_nra => nra
      | L_nraenv_core => nraenv_core
      | L_nraenv => nraenv
      | L_nnrc_core => nnrc_core
      | L_nnrc => nnrc
      | L_nnrcmr => nnrcmr
      | L_cldmr => cldmr
      | L_dnnrc_dataset => dnnrc_dataset
      | L_dnnrc_typed_dataset => dnnrc_typed_dataset
      | L_javascript => javascript
      | L_java => java
      | L_spark_rdd => spark_rdd
      | L_spark_dataset => spark_dataset
      | L_cloudant => cloudant
      | L_error _ => string
      end.
  End Query.

End CompLang.

Tactic Notation "language_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "L_camp_rule"%string
  | Case_aux c "L_tech_rule"%string
  | Case_aux c "L_designer_rule"%string
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
  | Case_aux c "L_spark_rdd"%string
  | Case_aux c "L_spark_dataset"%string
  | Case_aux c "L_cloudant"%string
  | Case_aux c "L_error"%string].


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
