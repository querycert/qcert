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
Require Import Utils.
Require Import List.
Require Import EquivDec.

Require Import CommonSystem.

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
Require Import SparkRDDRuntime.
Require Import SparkDFRuntime.

Require Import NNRCMRtoDNNRC.
Require Import DNNRCTypes.

Section CompLang.
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
    | L_nnrs_core : language
    | L_nnrs : language
    | L_nnrs_imp : language
    | L_imp_qcert : language
    | L_imp_json : language
    | L_nnrcmr : language
    | L_dnnrc : language
    | L_dnnrc_typed : language
    | L_js_ast : language
    | L_javascript : language
    | L_java : language
    | L_spark_rdd : language
    | L_spark_df : language
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

    Definition no_L_error (lang: language) : Prop :=
      match lang with
      | L_error _ => False
      | _ => True
      end.

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
      | "nnrs_core"%string => L_nnrs_core
      | "nnrs"%string => L_nnrs
      | "nnrs_imp"%string => L_nnrs_imp
      | "imp_qcert"%string => L_imp_qcert
      | "imp_json"%string => L_imp_json
      | "nnrcmr"%string => L_nnrcmr
      | "dnnrc"%string => L_dnnrc
      | "dnnrc_typed"%string => L_dnnrc_typed
      | "js_ast"%string => L_js_ast
      | "js"%string | "rhino"%string | "javascript"%string => L_javascript
      | "java"%string => L_java
      | "spark_rdd"%string => L_spark_rdd
      | "spark_df"%string | "spark_dataset"%string => L_spark_df
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
      | L_nnrs_core => "nnrs_core"%string
      | L_nnrs => "nnrs"%string
      | L_nnrs_imp => "nnrs_imp"%string
      | L_imp_qcert => "imp_qcert"%string
      | L_imp_json => "imp_json"%string
      | L_nnrcmr => "nnrcmr"%string
      | L_dnnrc => "dnnrc"%string
      | L_dnnrc_typed => "dnnrc_typed"%string
      | L_js_ast => "js_ast"%string
      | L_javascript => "js"%string
      | L_java => "java"%string
      | L_spark_rdd => "spark_rdd"%string
      | L_spark_df => "spark_df"%string
      | L_error _ => "error"%string
      end.

    Lemma language_of_name_of_language lang :
      no_L_error lang ->
      language_of_name_case_sensitive (name_of_language lang) = lang.
    Proof.
      destruct lang; vm_compute; tauto.
    Qed.

(*    Lemma name_of_language_language_of_name name :
      no_L_error (language_of_name_case_sensitive name) ->
      name_of_language (language_of_name_case_sensitive name) = name.
    Proof.
    Should be true, but the proof by brute force is computationally intensive.
    Qed.
*)

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
        :: (L_lambda_nra,FrontEnd,"λ-NRA", "Lambda Nested Relational Algebra")
        :: (L_tech_rule,FrontEnd,"TechRule", "Technical Rules")
        :: (L_designer_rule,FrontEnd,"DesignerRule", "Designer Rules")
        :: (L_camp_rule,CoreEnd,"CAMPRule", "Rules for CAMP")
        :: (L_camp,CoreEnd,"CAMP", "Calculus of Aggregating Matching Patterns")
        :: (L_nra,CoreEnd,"NRA", "Nested Relational Algebra")
        :: (L_nraenv_core,CoreEnd,"cNRAᵉ", "Core Nested Relational Algebra with Environments")
        :: (L_nraenv,CoreEnd,"NRAᵉ", "Nested Relational Algebra with Environments")
        :: (L_nnrc_core,CoreEnd,"cNNRC", "Core Named Nested Relational Calculus")
        :: (L_nnrc,CoreEnd,"NNRC", "Named Nested Relational Calculus")
        :: (L_nnrs_core,BackEnd,"cNNRS", "Core Named Nested Relational Calculus imperative")
        :: (L_nnrs,CoreEnd,"NNRS", "Named Nested Relational Calculus imperative")
        :: (L_nnrs_imp,BackEnd,"NNRSimp", "Named Nested Relational Calculus imperative")
        :: (L_imp_qcert,BackEnd,"ImpQcert", "Imperative langauge with Q*cert data model")
        :: (L_imp_json,BackEnd,"ImpJson", "Imperative langauge with json data model")
        :: (L_nnrcmr,DistrEnd,"NNRCMR", "Named Nested Relational Calculus with Map/Reduce")
        :: (L_dnnrc,DistrEnd,"DNNRC", "Distributed Named Nested Relational Calculus")
        :: (L_dnnrc_typed,DistrEnd,"tDNNRC", "Typed Distributed Named Nested Relational Calculus")
        :: (L_js_ast,BackEnd,"JsAst", "JavaScript AST")
        :: (L_javascript,BackEnd,"JavaScript", "JavaScript")
        :: (L_java,BackEnd,"Java", "Java")
        :: (L_spark_rdd,BackEnd,"SparkRDD", "Spark (RDDs API)")
        :: (L_spark_df,BackEnd,"SparkDF", "Spark (DataFrames API)")
        :: nil.

    Definition add_id_to_language_description (ld:language * language_kind * string * string) :=
      match ld with
      | (lang,kind,label,desc) =>
        (lang,name_of_language lang,kind,label,desc)
      end.

    Definition language_descriptions_with_ids :=
      map add_id_to_language_description language_descriptions.

    (* Eval vm_compute in languages_descriptions_with_ids. *)

    Lemma languages_descriptions_complete :
      forall lang,
        no_L_error lang ->
        exists kind s1 s2,
          In (lang, kind, s1, s2) language_descriptions.
    Proof.
      destruct lang; vm_compute;
        intros; try solve [do 3 eexists; tauto].
      Unshelve.
      - tauto.
      - tauto.
      - tauto.
    Qed.

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
    Definition nnrs_core := nnrs_core.
    Definition nnrs := nnrs.
    Definition nnrs_imp_expr := nnrs_imp_expr.
    Definition nnrs_imp_stmt := nnrs_imp_stmt.
    Definition nnrs_imp := nnrs_imp.
    Definition imp_qcert_expr := imp_qcert_expr.
    Definition imp_qcert_stmt := imp_qcert_stmt.
    Definition imp_qcert := imp_qcert.
    Definition imp_json_expr := imp_json_expr.
    Definition imp_json_stmt := imp_json_stmt.
    Definition imp_json := imp_json.
    Definition nnrcmr := nnrcmr.
    Definition dnnrc := dnnrc.
    Definition dnnrc_typed {bm:brand_model} := dnnrc_typed.
    Definition js_ast := list funcdecl.
    Definition javascript := javascript.
    Definition java := java.
    Definition spark_rdd := spark_rdd.
    Definition spark_df := spark_df.

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
    | Q_nnrs_core : nnrs_core -> query
    | Q_nnrs : nnrs -> query
    | Q_nnrs_imp : nnrs_imp -> query
    | Q_imp_qcert : imp_qcert -> query
    | Q_imp_json : imp_json -> query
    | Q_nnrcmr : nnrcmr -> query
    | Q_dnnrc : dnnrc -> query
    | Q_dnnrc_typed : dnnrc_typed -> query
    | Q_js_ast : js_ast -> query
    | Q_javascript : javascript -> query
    | Q_java : java -> query
    | Q_spark_rdd : spark_rdd -> query
    | Q_spark_df : spark_df -> query
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
      | Case_aux c "Q_nnrs_core"%string
      | Case_aux c "Q_nnrs"%string
      | Case_aux c "Q_nnrs_imp"%string
      | Case_aux c "Q_imp_qcert"%string
      | Case_aux c "Q_imp_json"%string
      | Case_aux c "Q_nnrcmr"%string
      | Case_aux c "Q_dnnrc"%string
      | Case_aux c "Q_dnnrc_typed"%string
      | Case_aux c "Q_js_ast"%string
      | Case_aux c "Q_javascript"%string
      | Case_aux c "Q_java"%string
      | Case_aux c "Q_spark_rdd"%string
      | Case_aux c "Q_spark_df"%string
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
      | Q_nnrs_core _ => L_nnrs_core
      | Q_nnrs _ => L_nnrs
      | Q_nnrs_imp _ => L_nnrs_imp
      | Q_imp_qcert _ => L_imp_qcert
      | Q_imp_json _ => L_imp_json
      | Q_nnrcmr _ => L_nnrcmr
      | Q_dnnrc _ => L_dnnrc
      | Q_dnnrc_typed _ => L_dnnrc_typed
      | Q_js_ast _ => L_js_ast
      | Q_javascript _ => L_javascript
      | Q_java _ => L_java
      | Q_spark_rdd _ => L_spark_rdd
      | Q_spark_df _ => L_spark_df
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
      | L_nnrs_core => nnrs_core
      | L_nnrs => nnrs
      | L_nnrs_imp => nnrs_imp
      | L_imp_qcert => imp_qcert
      | L_imp_json => imp_json
      | L_nnrcmr => nnrcmr
      | L_dnnrc => dnnrc
      | L_dnnrc_typed => dnnrc_typed
      | L_js_ast => js_ast
      | L_javascript => javascript
      | L_java => java
      | L_spark_rdd => spark_rdd
      | L_spark_df => spark_df
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
  | Case_aux c "L_nnrs_core"%string
  | Case_aux c "L_nnrs"%string
  | Case_aux c "L_nnrs_imp"%string
  | Case_aux c "L_imp_qcert"%string
  | Case_aux c "L_imp_json"%string
  | Case_aux c "L_nnrcmr"%string
  | Case_aux c "L_dnnrc"%string
  | Case_aux c "L_dnnrc_typed"%string
  | Case_aux c "L_js_ast"%string
  | Case_aux c "L_javascript"%string
  | Case_aux c "L_java"%string
  | Case_aux c "L_spark_rdd"%string
  | Case_aux c "L_spark_df"%string
  | Case_aux c "L_error"%string].

