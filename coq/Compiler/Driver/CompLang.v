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
    | L_sqlpp : language
    | L_lambda_nra : language
    | L_nra : language
    | L_nraenv_core : language
    | L_nraenv : language
    | L_nnrc_core : language
    | L_nnrc : language
    | L_nnrcmr : language
    | L_cldmr : language
    | L_dnnrc : language
    | L_dnnrc_typed : language
    | L_javascript : language
    | L_java : language
    | L_spark_rdd : language
    | L_spark_df : language
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
      | "sqlpp"%string => L_sqlpp
      | "lambda_nra"%string => L_lambda_nra
      | "nra"%string => L_nra
      | "nraenv_core"%string => L_nraenv_core
      | "nraenv"%string => L_nraenv
      | "nnrc_core"%string => L_nnrc_core
      | "nnrc"%string => L_nnrc
      | "nnrcmr"%string => L_nnrcmr
      | "cldmr"%string => L_cldmr
      | "dnnrc"%string => L_dnnrc
      | "dnnrc_typed"%string => L_dnnrc_typed
      | "js"%string | "rhino"%string | "javascript"%string => L_javascript
      | "java"%string => L_java
      | "spark_rdd"%string => L_spark_rdd
      | "spark_df"%string | "spark_dataset"%string => L_spark_df
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
      | L_sqlpp => "sqlpp"%string
      | L_lambda_nra => "lambda_nra"%string
      | L_nra => "nra"%string
      | L_nraenv_core => "nraenv_core"%string
      | L_nraenv => "nraenv"%string
      | L_nnrc_core => "nnrc_core"%string
      | L_nnrc => "nnrc"%string
      | L_nnrcmr => "nnrcmr"%string
      | L_cldmr => "cldmr"%string
      | L_dnnrc => "dnnrc"%string
      | L_dnnrc_typed => "dnnrc_typed"%string
      | L_javascript => "js"%string
      | L_java => "java"%string
      | L_spark_rdd => "spark_rdd"%string
      | L_spark_df => "spark_df"%string
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
      (L_sql,FrontEnd,"SQL", "Structured Query Language")
        :: (L_sqlpp,FrontEnd,"SQL++","SQL With Semi-Structured Data Extensions")
        :: (L_oql,FrontEnd,"OQL", "Object Query Language")
        :: (L_lambda_nra,FrontEnd,"λNRA", "Lambda Nested Relational Algebra")
        :: (L_tech_rule,FrontEnd,"TechRule", "Technical Rules")
        :: (L_designer_rule,FrontEnd,"DesignRule", "Designer Rules")
        :: (L_camp_rule,FrontEnd,"CAMPRule", "Rules for CAMP")
        :: (L_camp,CoreEnd,"CAMP", "Calculus of Aggregating Matching Patterns")
        :: (L_nra,CoreEnd,"NRA", "Nested Relational Algebra")
        :: (L_nraenv_core,CoreEnd,"cNRAᵉ", "Core Nested Relational Algebra with Environments")
        :: (L_nraenv,CoreEnd,"NRAᵉ", "Nested Relational Algebra with Environments")
        :: (L_nnrc_core,CoreEnd,"cNNRC", "Core Named Nested Relational Calculus")
        :: (L_nnrc,CoreEnd,"NNRC", "Named Nested Relational Calculus")
        :: (L_nnrcmr,DistrEnd,"NNRCMR", "Named Nested Relational Calculus with Map/Reduce")
        :: (L_cldmr,DistrEnd,"CldMR", "Named Nested Relational Calculus with Cloudant Map/Reduce")
        :: (L_dnnrc,DistrEnd,"DNNRC", "Distributed Named Nested Relational Calculus")
        :: (L_dnnrc_typed,DistrEnd,"tDNNRC", "Typed Distributed Named Nested Relational Calculus")
        :: (L_javascript,BackEnd,"JavaScript", "JavaScript")
        :: (L_java,BackEnd,"Java", "Java")
        :: (L_spark_rdd,BackEnd,"SparkRDD", "Spark (RDD API)")
        :: (L_spark_df,BackEnd,"SparkDF", "Spark (Dataframe API)")
        :: (L_cloudant,BackEnd,"Cloudant", "Cloudant Map/Reduce Views")
        :: nil.

    Definition add_id_to_language_description (ld:language * language_kind * string * string) :=
      match ld with
      | (lang,kind,label,desc) =>
        (lang,name_of_language lang,kind,label,desc)
      end.

    Definition language_descriptions_with_ids :=
      map add_id_to_language_description language_descriptions.

    (* Eval vm_compute in languages_descriptions_with_ids. *)

    Definition check_kind (the_kind:language_kind)
               (ld:language * string * language_kind * string * string)
      :=
      match ld with
      | (lang,id,kind,label,desc) =>
        if (language_kind_eq_dec kind the_kind) then true else false
      end.
    
    Record export_desc :=
      mkExportDesc
      { frontend : list(language * string * language_kind * string * string);
        coreend : list(language * string * language_kind * string * string);
        distrend : list(language * string * language_kind * string * string);
        backend : list(language * string * language_kind * string * string) }.
    
    Definition select_description_per_kind
               (ldl: list(language * string * language_kind * string * string)) :=
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
    Require Import SQLPPRuntime.
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
    Require Import tDNNRCRuntime.
    Require Import CAMPRuntime.
    (** Target languages *)
    Require Import JavaScriptRuntime.
    Require Import JavaRuntime.
    Require Import SparkRDDRuntime.
    Require Import SparkDFRuntime.
    Require Import CloudantRuntime.

    Require Import NNRCMRtoDNNRC.
    Require Import DNNRCTypes.
  
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
    Definition sqlpp := sqlpp.
    Definition lambda_nra := lambda_nra.
    Definition nra := nra.
    Definition nraenv_core := nraenv_core.
    Definition nraenv := nraenv.
    Definition nnrc_core := nnrc_core.
    Definition nnrc := nnrc.
    Definition nnrcmr := nnrcmr.
    Definition cldmr := cldmr.
    Definition dnnrc := dnnrc_dataframe.
    Definition dnnrc_typed {bm:brand_model} := dnnrc_dataframe_typed.
    Definition javascript := js.
    Definition java := java.
    Definition spark_rdd := spark_rdd.
    Definition spark_df := spark_df.
    Definition cloudant := cloudant.

    Inductive query : Set :=
    | Q_camp_rule : camp_rule -> query
    | Q_tech_rule : tech_rule -> query
    | Q_designer_rule : designer_rule -> query
    | Q_camp : camp -> query
    | Q_oql : oql -> query
    | Q_sql : sql -> query
    | Q_sqlpp : sqlpp -> query
    | Q_lambda_nra : lambda_nra -> query
    | Q_nra : nra -> query
    | Q_nraenv_core : nraenv_core -> query
    | Q_nraenv : nraenv -> query
    | Q_nnrc_core : nnrc_core -> query
    | Q_nnrc : nnrc -> query
    | Q_nnrcmr : nnrcmr -> query
    | Q_cldmr : cldmr -> query
    | Q_dnnrc : dnnrc -> query
    | Q_dnnrc_typed : dnnrc_typed -> query
    | Q_javascript : javascript -> query
    | Q_java : java -> query
    | Q_spark_rdd : spark_rdd -> query
    | Q_spark_df : spark_df -> query
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
      | Case_aux c "Q_sqlpp"%string
      | Case_aux c "Q_lambda_nra"%string
      | Case_aux c "Q_nra"%string
      | Case_aux c "Q_nraenv_core"%string
      | Case_aux c "Q_nraenv"%string
      | Case_aux c "Q_nnrc_core"%string
      | Case_aux c "Q_nnrc"%string
      | Case_aux c "Q_nnrcmr"%string
      | Case_aux c "Q_cldmr"%string
      | Case_aux c "Q_dnnrc"%string
      | Case_aux c "Q_dnnrc_typed"%string
      | Case_aux c "Q_javascript"%string
      | Case_aux c "Q_java"%string
      | Case_aux c "Q_spark_rdd"%string
      | Case_aux c "Q_spark_df"%string
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
      | Q_sqlpp _ => L_sqlpp
      | Q_lambda_nra _ => L_lambda_nra
      | Q_nra _ => L_nra
      | Q_nraenv_core _ => L_nraenv_core
      | Q_nraenv _ => L_nraenv
      | Q_nnrc_core _ => L_nnrc_core
      | Q_nnrc _ => L_nnrc
      | Q_nnrcmr _ => L_nnrcmr
      | Q_cldmr _ => L_cldmr
      | Q_dnnrc _ => L_dnnrc
      | Q_dnnrc_typed _ => L_dnnrc_typed
      | Q_javascript _ => L_javascript
      | Q_java _ => L_java
      | Q_spark_rdd _ => L_spark_rdd
      | Q_spark_df _ => L_spark_df
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
      | L_sqlpp => sqlpp
      | L_lambda_nra => lambda_nra
      | L_nra => nra
      | L_nraenv_core => nraenv_core
      | L_nraenv => nraenv
      | L_nnrc_core => nnrc_core
      | L_nnrc => nnrc
      | L_nnrcmr => nnrcmr
      | L_cldmr => cldmr
      | L_dnnrc => dnnrc
      | L_dnnrc_typed => dnnrc_typed
      | L_javascript => javascript
      | L_java => java
      | L_spark_rdd => spark_rdd
      | L_spark_df => spark_df
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
  | Case_aux c "L_sqlpp"%string
  | Case_aux c "L_lambda_nra"%string
  | Case_aux c "L_nra"%string
  | Case_aux c "L_nraenv_core"%string
  | Case_aux c "L_nraenv"%string
  | Case_aux c "L_nnrc_core"%string
  | Case_aux c "L_nnrc"%string
  | Case_aux c "L_nnrcmr"%string
  | Case_aux c "L_cldmr"%string
  | Case_aux c "L_dnnrc"%string
  | Case_aux c "L_dnnrc_typed"%string
  | Case_aux c "L_javascript"%string
  | Case_aux c "L_java"%string
  | Case_aux c "L_spark_rdd"%string
  | Case_aux c "L_spark_df"%string
  | Case_aux c "L_cloudant"%string
  | Case_aux c "L_error"%string].


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
