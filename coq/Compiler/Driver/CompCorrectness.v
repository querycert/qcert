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
Require Import List.
Require Import Morphisms.

(* Common libraries *)
Require Import Utils.
Require Import CommonSystem.
Require Import TypingRuntime.

(* Query languages *)
Require Import SQLRuntime.
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
Require Import SparkDFRuntime.

(* Translations *)
Require Import OQLtoNRAEnv.
Require Import SQLtoNRAEnv.
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
Require Import NNRCtoDNNRC.
Require Import NNRCtoNNRCMR.
Require Import NNRStoNNRSimp.
Require Import NNRSimptoImpQcert.
Require Import ImpQcerttoImpJson.
Require Import NNRSimptoJavaScriptAst.
Require Import NNRCtoJava.
Require Import cNNRCtoCAMP.
Require Import cNNRCtoNNRC.
Require Import NNRCMRtoNNRC.
Require Import NNRCMRtoDNNRC.
Require Import DNNRCtotDNNRC.
Require Import tDNNRCtoSparkDF.

(* Optimizers *)
Require Import NRAEnvOptim.
Require Import NNRCOptim.
Require Import NNRSimpOptim.
Require Import NNRCMROptim.
Require Import tDNNRCOptim.
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
Require Import CompDriver.
Require Import CompEval.

Section CompCorrectness.
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
  Context {imp_qcert_logger:optimizer_logger string imp_qcert}.
  Context {imp_json_logger:optimizer_logger string imp_json}.
  Context {dnnrc_logger:optimizer_logger string (DNNRCBase.dnnrc_base fr (type_annotation unit) dataframe)}.
  Context {ftojs:foreign_to_javascript}.
  Context {ftoajs:foreign_to_ajavascript}.
  Context {ftojava:foreign_to_java}.
  Context {ftos:foreign_to_scala}.
  Context {ftospark:foreign_to_spark}.
  Context {ftjson:foreign_to_JSON}.

  (** Note: All stops are assumed correct (i.e., not moving does not change semantics) *)
  (** Note: True/False is indicated for each edge in the compiler pipeline *)
  (** Note: For now optimization is not recorded as correct *)

  Definition driver_correct_javascript (dv: javascript_driver) :=
    match dv with
    | Dv_javascript_stop => True
    end.

  Definition driver_correct_js_ast (dv: js_ast_driver) :=
    match dv with
    | Dv_js_ast_stop => True
    | Dv_js_ast_to_javascript dv => False /\ driver_correct_javascript dv
    end.

  Definition driver_correct_java (dv: java_driver) :=
    match dv with
    | Dv_java_stop => True
    end.

  Definition driver_correct_spark_df (dv: spark_df_driver) :=
    match dv with
    | Dv_spark_df_stop => True
    end.

  Fixpoint driver_correct_dnnrc_typed {ftyping: foreign_typing} (dv: dnnrc_typed_driver) :=
    match dv with
    | Dv_dnnrc_typed_stop => True
    | Dv_dnnrc_typed_optim dv => False /\ driver_correct_dnnrc_typed dv
    | Dv_dnnrc_typed_to_spark_df rt rulename dv => False /\ driver_correct_spark_df dv
    end.

  Definition driver_correct_dnnrc (dv: dnnrc_driver) :=
    match dv with
    | Dv_dnnrc_stop => True
    | Dv_dnnrc_to_dnnrc_typed _ dv => False /\ driver_correct_dnnrc_typed dv
    end.

  Fixpoint driver_correct_imp_json (dv: imp_json_driver) :=
    match dv with
    | Dv_imp_json_stop => True
    | Dv_imp_json_to_js_ast dv => False /\ driver_correct_js_ast dv
    end.

  Fixpoint driver_correct_imp_qcert (dv: imp_qcert_driver) :=
    match dv with
    | Dv_imp_qcert_stop => True
    | Dv_imp_qcert_to_imp_json dv => False /\ driver_correct_imp_json dv
    end.

  Fixpoint driver_correct_nnrs_imp (dv: nnrs_imp_driver) :=
    match dv with
    | Dv_nnrs_imp_stop => True
    | Dv_nnrs_imp_optim _ dv => False /\ driver_correct_nnrs_imp dv
    | Dv_nnrs_imp_to_imp_qcert _ dv => driver_correct_imp_qcert dv
    | Dv_nnrs_imp_to_js_ast _ dv => False /\ driver_correct_js_ast dv
    end.

  Definition driver_correct_nnrs (dv: nnrs_driver) :=
    match dv with
    | Dv_nnrs_stop => True
    | Dv_nnrs_to_nnrs_imp dv => True /\ driver_correct_nnrs_imp dv
    end.

  Definition driver_correct_nnrs_core (dv: nnrs_core_driver) :=
    match dv with
    | Dv_nnrs_core_stop => True
    | Dv_nnrs_core_to_nnrs dv => True /\ driver_correct_nnrs dv
    end.

  Fixpoint driver_correct_camp (dv: camp_driver) :=
    match dv with
    | Dv_camp_stop => True
    | Dv_camp_to_nraenv_core dv => True /\ driver_correct_nraenv_core dv
    | Dv_camp_to_nraenv dv => True /\ driver_correct_nraenv dv
    | Dv_camp_to_nra dv => True /\ driver_correct_nra dv
    end

  with driver_correct_nra (dv: nra_driver)  :=
    match dv with
    | Dv_nra_stop => True
    | Dv_nra_to_nnrc_core dv => True /\ driver_correct_nnrc_core dv
    | Dv_nra_to_nraenv_core dv => True /\ driver_correct_nraenv_core dv
    end

  with driver_correct_nraenv_core (dv: nraenv_core_driver) :=
    match dv with
    | Dv_nraenv_core_stop => True
    | Dv_nraenv_core_to_nraenv dv => True /\ driver_correct_nraenv dv
    | Dv_nraenv_core_to_nnrc_core dv => True /\ driver_correct_nnrc_core dv
    | Dv_nraenv_core_to_nra dv => True /\ driver_correct_nra dv
    end

  with driver_correct_nraenv (dv: nraenv_driver) :=
    match dv with
    | Dv_nraenv_stop => True
    | Dv_nraenv_optim opc dv => False /\ driver_correct_nraenv dv
    | Dv_nraenv_to_nnrc dv => True /\ driver_correct_nnrc dv
    | Dv_nraenv_to_nraenv_core dv => True /\ driver_correct_nraenv_core dv
    end

  with driver_correct_nnrc_core (dv: nnrc_core_driver) :=
    match dv with
    | Dv_nnrc_core_stop => True
    | Dv_nnrc_core_to_nnrs_core inputs dv => True /\ driver_correct_nnrs_core dv
    | Dv_nnrc_core_to_nnrc dv => True /\ driver_correct_nnrc dv
    | Dv_nnrc_core_to_camp avoid dv => False /\ driver_correct_camp dv (** XXX lifting issue XXX *)
    end

  with driver_correct_nnrc (dv: nnrc_driver) :=
    match dv with
    | Dv_nnrc_stop => True
    | Dv_nnrc_optim opc dv => False /\ driver_correct_nnrc dv
    | Dv_nnrc_to_nnrc_core dv => True /\ driver_correct_nnrc_core dv
    | Dv_nnrc_to_nnrs inputs dv => True /\ driver_correct_nnrs dv
    | Dv_nnrc_to_nnrcmr vinit inputs_loc dv => False /\ driver_correct_nnrcmr dv
    | Dv_nnrc_to_dnnrc inputs_loc dv => False /\ driver_correct_dnnrc dv
    | Dv_nnrc_to_java class_name imports dv => False /\ driver_correct_java dv
    end

  with driver_correct_nnrcmr (dv: nnrcmr_driver) :=
    match dv with
    | Dv_nnrcmr_stop => True
    | Dv_nnrcmr_optim dv => False /\ driver_correct_nnrcmr dv
    | Dv_nnrcmr_to_nnrc dv => False /\ driver_correct_nnrc dv
    | Dv_nnrcmr_to_dnnrc dv => False /\ driver_correct_dnnrc dv
    end.

  Definition driver_correct_camp_rule (dv: camp_rule_driver) :=
    match dv with
    | Dv_camp_rule_stop => True
    | Dv_camp_rule_to_camp dv => True /\ driver_correct_camp dv
    end.

  Definition driver_correct_tech_rule (dv: tech_rule_driver) :=
    match dv with
    | Dv_tech_rule_stop => True
    | Dv_tech_rule_to_camp_rule dv => False /\ driver_correct_camp_rule dv
    end.

  Definition driver_correct_designer_rule (dv: designer_rule_driver) :=
    match dv with
    | Dv_designer_rule_stop => True
    | Dv_designer_rule_to_camp_rule dv => False /\ driver_correct_camp_rule dv
    end.

  Definition driver_correct_oql (dv: oql_driver) :=
    match dv with
    | Dv_oql_stop => True
    | Dv_oql_to_nraenv dv => True /\ driver_correct_nraenv dv
    end.

  Definition driver_correct_sql (dv: sql_driver) :=
    match dv with
    | Dv_sql_stop => True
    | Dv_sql_to_nraenv dv => False /\ driver_correct_nraenv dv
    end.

  Definition driver_correct_sqlpp (dv: sqlpp_driver) :=
    match dv with
    | Dv_sqlpp_stop => True
    | Dv_sqlpp_to_nraenv dv => False /\ driver_correct_nraenv dv
    end.

  Definition driver_correct_lambda_nra (dv: lambda_nra_driver) :=
    match dv with
    | Dv_lambda_nra_stop => True
    | Dv_lambda_nra_to_nraenv dv => True /\ driver_correct_nraenv dv
    end.

  Definition driver_correct (dv: driver)  :=
    match dv with
    | Dv_camp_rule dv => driver_correct_camp_rule dv
    | Dv_tech_rule dv => driver_correct_tech_rule dv
    | Dv_designer_rule dv => driver_correct_designer_rule dv
    | Dv_camp dv => driver_correct_camp dv
    | Dv_oql dv => driver_correct_oql dv
    | Dv_sql dv => driver_correct_sql dv
    | Dv_sqlpp dv => driver_correct_sqlpp dv
    | Dv_lambda_nra dv => driver_correct_lambda_nra dv
    | Dv_nra dv => driver_correct_nra dv
    | Dv_nraenv_core dv => driver_correct_nraenv_core dv
    | Dv_nraenv dv => driver_correct_nraenv dv
    | Dv_nnrc_core dv => driver_correct_nnrc_core dv
    | Dv_nnrc dv => driver_correct_nnrc dv
    | Dv_nnrs_core dv => driver_correct_nnrs_core dv
    | Dv_nnrs dv => driver_correct_nnrs dv
    | Dv_nnrs_imp dv => driver_correct_nnrs_imp dv
    | Dv_imp_qcert dv => driver_correct_imp_qcert dv
    | Dv_imp_json dv => driver_correct_imp_json dv
    | Dv_nnrcmr dv => driver_correct_nnrcmr dv
    | Dv_dnnrc dv => driver_correct_dnnrc dv
    | Dv_dnnrc_typed dv => driver_correct_dnnrc_typed dv
    | Dv_js_ast dv => driver_correct_js_ast dv
    | Dv_javascript dv => driver_correct_javascript dv
    | Dv_java dv => driver_correct_java dv
    | Dv_spark_df dv => driver_correct_spark_df dv
    | Dv_error s => True (* XXX ??? XXX *)
    end.

  Section eval_preserved.

    Lemma error_msg_to_false s1 :
      (forall s : string, Q_error s1 :: nil <> Q_error s :: nil) -> False.
    Proof.
      intros.
      specialize (H s1).
      congruence.
    Qed.

    Ltac elim_qerror :=
      match goal with
      | [H:context [forall _ : string, compile _ _ <> (Q_error _ :: nil)] |- _ ] =>
        try (unfold compile in H; simpl in H; simpl;
             assert False by apply (error_msg_to_false _ H); contradiction)
      end.

    Ltac prove_same_outputs :=
      unfold eval_camp_rule, eval_camp,
      eval_nra, eval_nraenv, eval_nraenv_core,
      eval_nnrc, eval_nnrc_core, eval_nnrs, eval_nnrs_imp, eval_imp_qcert, eval_imp_json, eval_nnrcmr,
      eval_dnnrc, eval_dnnrc_typed;
      try match goal with
      | [ |- equal_outputs (lift_output (camp_rule_eval_top ?h ?c (lift_input ?i)))
                           (lift_output (camp_rule_eval_top ?h ?c (lift_input ?i))) ] =>
        destruct  (lift_output (camp_rule_eval_top h c (lift_input i))); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (camp_eval_top ?h ?c (lift_input ?i)))
                           (lift_output (camp_eval_top ?h ?c (lift_input ?i))) ] =>
        destruct  (lift_output (camp_eval_top h c (lift_input i))); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (nraenv_core_eval_top ?h ?c (lift_input ?i)))
                           (lift_output (nraenv_core_eval_top ?h ?c (lift_input ?i))) ] =>
        destruct  (lift_output (nraenv_core_eval_top h c (lift_input i))); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (nraenv_eval_top ?h ?c (lift_input ?i)))
                           (lift_output (nraenv_eval_top ?h ?c (lift_input ?i))) ] =>
        destruct  (lift_output (nraenv_eval_top h c (lift_input i))); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (nra_eval_top ?h ?c (lift_input ?i)))
                           (lift_output (nra_eval_top ?h ?c (lift_input ?i))) ] =>
        destruct  (lift_output (nra_eval_top h c (lift_input i))); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (nnrc_eval_top ?h ?c (lift_input ?i)))
                           (lift_output (nnrc_eval_top ?h ?c (lift_input ?i))) ] =>
        destruct  (lift_output (nnrc_eval_top h c (lift_input i))); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (nnrc_eval_top ?h ?c (unlocalize_constants ?i)))
                           (lift_output (nnrc_eval_top ?h ?c (unlocalize_constants ?i))) ] =>
        destruct  (lift_output (nnrc_eval_top h c (unlocalize_constants i))); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (nnrc_core_eval_top ?h ?c (lift_input ?i)))
                           (lift_output (nnrc_core_eval_top ?h ?c (lift_input ?i))) ] =>
        destruct  (lift_output (nnrc_core_eval_top h c (lift_input i))); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (eval_oql ?h ?c (lift_input ?i)))
                           (lift_output (eval_oql ?h ?c (lift_input ?i))) ] =>
        destruct  (lift_output (eval_oql h c (lift_input i))); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (eval_lambda_nra ?h ?c (lift_input ?i)))
                           (lift_output (eval_lambda_nra ?h ?c (lift_input ?i))) ] =>
        destruct  (lift_output (eval_lambda_nra h c (lift_input i))); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (nnrs_eval_top ?h ?c (lift_input ?i)))
                           (lift_output (nnrs_eval_top ?h ?c (lift_input ?i))) ] =>
        destruct  (lift_output (nnrs_eval_top h c (lift_input i))); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (nnrcmr_eval_top ?h ?init ?c ?i))
                           (lift_output (nnrcmr_eval_top ?h ?init ?c ?i)) ] =>
        destruct  (lift_output (nnrcmr_eval_top h init c i)); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (dnnrc_eval_top ?h ?c ?i))
                           (lift_output (dnnrc_eval_top ?h ?c ?i)) ] =>
        destruct  (lift_output (dnnrc_eval_top h c i)); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (lift_output (dnnrc_typed_eval_top ?h ?c ?i))
                           (lift_output (dnnrc_typed_eval_top ?h ?c ?i)) ] =>
        destruct  (lift_output (dnnrc_typed_eval_top h c i)); simpl; try reflexivity;
        unfold equal_outputs; simpl; match_destr; auto
      | [ |- equal_outputs (Ev_out_unsupported ?s1)
                           (Ev_out_unsupported ?s2) ] =>
        unfold equal_outputs; simpl; auto
      end.

    Context {h:list(string*string)}.

    Definition query_not_error (q:query) :=
      match q with
      | Q_error _ => False
      | _ => True
      end.


    Definition driver_matches_query (dv:driver) (q:query) :=
    match (dv, q) with
    | (Dv_camp_rule _, Q_camp_rule _) => True
    | (Dv_tech_rule _, Q_tech_rule _) => True
    | (Dv_designer_rule _, Q_designer_rule _) => True
    | (Dv_camp _, Q_camp _) => True
    | (Dv_oql _, Q_oql _) => True
    | (Dv_sql _, Q_sql _) => True
    | (Dv_sqlpp _, Q_sqlpp _) => True
    | (Dv_lambda_nra _, Q_lambda_nra _) => True
    | (Dv_nra _, Q_nra _) => True
    | (Dv_nraenv_core _, Q_nraenv_core _) => True
    | (Dv_nraenv _, Q_nraenv _) => True
    | (Dv_nnrc_core _, Q_nnrc_core _) => True
    | (Dv_nnrc _, Q_nnrc _) => True
    | (Dv_nnrs_core _, Q_nnrs_core _) => True
    | (Dv_nnrs _, Q_nnrs _) => True
    | (Dv_nnrs_imp _, Q_nnrs_imp _) => True
    | (Dv_imp_qcert _, Q_imp_qcert _) => True
    | (Dv_imp_json _, Q_imp_json _) => True
    | (Dv_nnrcmr _, Q_nnrcmr _) => True
    | (Dv_dnnrc _, Q_dnnrc _) => True
    | (Dv_dnnrc_typed _, Q_dnnrc_typed _) => True
    | (Dv_js_ast _, Q_js_ast _) => True
    | (Dv_javascript _, Q_javascript _) => True
    | (Dv_java _, Q_java _) => True
    | (Dv_spark_df _, Q_spark_df _) => True
    | (_, _) => False
    end.

    Lemma correct_driver_succeeds_imp_json:
      forall dv, driver_correct (Dv_imp_json dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_imp_json dv) (Q_imp_json q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      unfold compile in H0.
      revert q H0.
      induction dv; simpl in *; intuition; subst; eauto.
    Qed.

    Lemma correct_driver_succeeds_imp_qcert:
      forall dv, driver_correct (Dv_imp_qcert dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_imp_qcert dv) (Q_imp_qcert q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      unfold compile in H0.
      revert q H0.
      induction dv; simpl in *; intuition; subst; eauto.
    Qed.

    Lemma correct_driver_succeeds_nnrs_imp:
      forall dv, driver_correct (Dv_nnrs_imp dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_nnrs_imp dv) (Q_nnrs_imp q))).
    Proof.
      induction dv;
        intros;
        rewrite Forall_forall; intros;
        unfold compile in H0.
      - simpl in H0; destruct H0; try contradiction.
        rewrite <- H0; simpl; trivial.
      - simpl in H0; destruct H0; try contradiction.
        rewrite <- H0; simpl; trivial.
        revert q H0.
        induction dv; simpl in *; intuition; subst; eauto.
      - simpl in H0; destruct H0.
        rewrite <- H0; simpl; trivial.
        destruct H0.
        + rewrite <- H0; simpl; trivial.
        + destruct j; simpl in *; try contradiction.
          destruct j; simpl in *; try contradiction.
          destruct H0; simpl in *; try contradiction.
          rewrite <- H0; simpl; trivial.
      - simpl in H0; destruct H0; try contradiction.
        rewrite <- H0; simpl; trivial.
        revert q H0.
        induction i; simpl in *; intuition; subst; eauto.
    Qed.

    Lemma correct_driver_succeeds_nnrs:
      forall dv, driver_correct (Dv_nnrs dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_nnrs dv) (Q_nnrs q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; simpl in *.
      - contradiction.
      - destruct H as [_ H].
        generalize (correct_driver_succeeds_nnrs_imp n H (nnrs_to_nnrs_imp q)).
        rewrite Forall_forall; eauto.
    Qed.

    Lemma correct_driver_succeeds_nnrs_core:
      forall dv, driver_correct (Dv_nnrs_core dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_nnrs_core dv) (Q_nnrs_core q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; simpl in *; try contradiction.
      destruct n; simpl in *; intuition; subst; simpl; trivial.
      generalize (correct_driver_succeeds_nnrs_imp n H3  (nnrs_to_nnrs_imp (nnrs_core_to_nnrs q))).
        rewrite Forall_forall; eauto.
    Qed.

    Lemma correct_driver_succeeds_cnd:
      (forall dv, driver_correct (Dv_camp dv)
                  -> (forall q, Forall query_not_error
                                       (compile (Dv_camp dv) (Q_camp q))))
      /\ (forall dv, driver_correct (Dv_nra dv)
                     -> (forall q, Forall query_not_error
                                          (compile (Dv_nra dv) (Q_nra q))))
      /\ (forall dv, driver_correct (Dv_nraenv_core dv)
                     -> (forall q, Forall query_not_error
                                          (compile (Dv_nraenv_core dv) (Q_nraenv_core q))))
      /\ (forall dv, driver_correct (Dv_nraenv dv)
                     -> (forall q, Forall query_not_error
                                          (compile (Dv_nraenv dv) (Q_nraenv q))))
      /\ (forall dv, driver_correct (Dv_nnrc_core dv)
                     -> (forall q, Forall query_not_error
                                          (compile (Dv_nnrc_core dv) (Q_nnrc_core q))))
      /\ (forall dv, driver_correct (Dv_nnrc dv)
                     -> (forall q, Forall query_not_error
                                          (compile (Dv_nnrc dv) (Q_nnrc q))))
      /\ (forall dv, driver_correct (Dv_nnrcmr dv)
                     -> (forall q, Forall query_not_error
                                          (compile (Dv_nnrcmr dv) (Q_nnrcmr q)))).
    Proof.
      apply cnd_combined_ind
      ; simpl; try reflexivity; intros
      ; apply Forall_forall; simpl; intros
      ; elim H0; intros; try contradiction
      ; clear H0; try (rewrite <- H1; simpl; trivial).
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (camp_to_nraenv_core q));
        rewrite Forall_forall in H; auto.
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (camp_to_nraenv q));
        rewrite Forall_forall in H; auto.
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (camp_to_nra q));
        rewrite Forall_forall in H; auto.
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (nra_to_nnrc_core q));
        rewrite Forall_forall in H; auto.
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (nra_to_nraenv_core q));
        rewrite Forall_forall in H; auto.
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (nraenv_core_to_nraenv q));
        rewrite Forall_forall in H; auto.
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (nraenv_core_to_nnrc_core q));
        rewrite Forall_forall in H; auto.
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (nraenv_core_to_nra q));
        rewrite Forall_forall in H; auto.
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (nraenv_to_nnrc q));
        rewrite Forall_forall in H; auto.
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (nraenv_to_nraenv_core q));
        rewrite Forall_forall in H; auto.
      - destruct H as [_ H].
        unfold driver_correct_nnrs_core in H.
        destruct H1; intros; subst; simpl; trivial.
        destruct n; simpl in *; intuition; subst; simpl; trivial.
        destruct n; simpl in *; intuition; subst; simpl; trivial.
        generalize (correct_driver_succeeds_nnrs_imp n H3  (nnrs_to_nnrs_imp (nnrc_to_nnrs_top l (proj1_sig q)))).
        rewrite Forall_forall; eauto.
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (nnrc_core_to_nnrc q));
        rewrite Forall_forall in H; auto.
      - elim H1; intros; clear H1 H2; try (rewrite <- H0; simpl; trivial);
        specialize (H H3 (nnrc_to_nnrc_core q));
        rewrite Forall_forall in H; auto.
      - elim H1; intros; try (rewrite <- H0; simpl; trivial).
        destruct n; simpl in *; intuition; subst; simpl; trivial.
       generalize (correct_driver_succeeds_nnrs_imp n H4 (nnrs_to_nnrs_imp (nnrc_to_nnrs l q))).
       rewrite Forall_forall; eauto.
      - elim H; intros; contradiction.
      - elim H; intros; contradiction.
      - elim H; intros; contradiction. (* Failure case for dnnrc to dnnrc_typed -- False on correctness branch *)
    Qed.

    Lemma correct_driver_succeeds_camp_rule:
      forall dv, driver_correct (Dv_camp_rule dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_camp_rule dv) (Q_camp_rule q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; intros; [rewrite <- H1; simpl; trivial| ]; clear H0.
      destruct dv; simpl in H1; [contradiction| ].
      generalize correct_driver_succeeds_cnd; intros.
      elim H0; intros; clear H0 H3.
      simpl in H; elim H; intros.
      specialize (H2 c H3 (camp_rule_to_camp q)).
      rewrite Forall_forall in H2; auto.
    Qed.

    Lemma correct_driver_succeeds_tech_rule:
      forall dv, driver_correct (Dv_tech_rule dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_tech_rule dv) (Q_tech_rule q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; [simpl in *; contradiction| ].
      simpl in H.
      elim H; intros; contradiction.
    Qed.

    Lemma correct_driver_succeeds_designer_rule:
      forall dv, driver_correct (Dv_designer_rule dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_designer_rule dv) (Q_designer_rule q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; [simpl in *; contradiction| ].
      simpl in H.
      elim H; intros; contradiction.
    Qed.

    Lemma correct_driver_succeeds_camp:
      forall dv, driver_correct (Dv_camp dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_camp dv) (Q_camp q))).
    Proof.
      intros.
      generalize correct_driver_succeeds_cnd; intros.
      elim H0; intros; clear H0 H2.
      rewrite Forall_forall; intros.
      specialize (H1 dv H q).
      rewrite Forall_forall in H1; auto.
    Qed.

    Lemma correct_driver_succeeds_nraenv:
      forall dv, driver_correct (Dv_nraenv dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_nraenv dv) (Q_nraenv q))).
    Proof.
      intros.
      generalize correct_driver_succeeds_cnd; intros.
      elim H0; intros; clear H0 H1.
      elim H2; intros; clear H0 H2.
      elim H1; intros; clear H0 H1.
      elim H2; intros; clear H2 H1.
      rewrite Forall_forall; intros.
      specialize (H0 dv H q).
      rewrite Forall_forall in H0; auto.
    Qed.

    Lemma correct_driver_succeeds_nraenv_core:
      forall dv, driver_correct (Dv_nraenv_core dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_nraenv_core dv) (Q_nraenv_core q))).
    Proof.
      intros.
      generalize correct_driver_succeeds_cnd; intros.
      elim H0; intros; clear H0 H1.
      elim H2; intros; clear H0 H2.
      elim H1; intros; clear H1 H2.
      rewrite Forall_forall; intros.
      specialize (H0 dv H q).
      rewrite Forall_forall in H0; auto.
    Qed.

    Lemma correct_driver_succeeds_nnrc_core:
      forall dv, driver_correct (Dv_nnrc_core dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_nnrc_core dv) (Q_nnrc_core q))).
    Proof.
      intros.
      generalize correct_driver_succeeds_cnd; intros.
      elim H0; intros; clear H0 H1.
      elim H2; intros; clear H0 H2.
      elim H1; intros; clear H0 H1.
      elim H2; intros; clear H2 H0.
      elim H1; intros; clear H1 H2.
      rewrite Forall_forall; intros.
      specialize (H0 dv H q).
      rewrite Forall_forall in H0; auto.
    Qed.

    Lemma correct_driver_succeeds_nnrc:
      forall dv, driver_correct (Dv_nnrc dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_nnrc dv) (Q_nnrc q))).
    Proof.
      intros.
      generalize correct_driver_succeeds_cnd; intros.
      elim H0; intros; clear H0 H1.
      elim H2; intros; clear H0 H2.
      elim H1; intros; clear H0 H1.
      elim H2; intros; clear H2 H0.
      elim H1; intros; clear H1 H0.
      elim H2; intros; clear H1 H2.
      rewrite Forall_forall; intros.
      specialize (H0 dv H q).
      rewrite Forall_forall in H0; auto.
    Qed.

    Lemma correct_driver_succeeds_nnrcmr:
      forall dv, driver_correct (Dv_nnrcmr dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_nnrcmr dv) (Q_nnrcmr q))).
    Proof.
      intros.
      generalize correct_driver_succeeds_cnd; intros.
      elim H0; intros; clear H0 H1.
      elim H2; intros; clear H0 H2.
      elim H1; intros; clear H0 H1.
      elim H2; intros; clear H2 H0.
      elim H1; intros; clear H1 H0.
      elim H2; intros; clear H0 H2.
      rewrite Forall_forall; intros.
      specialize (H1 dv H q).
      rewrite Forall_forall in H1; auto.
    Qed.


    Lemma correct_driver_succeeds_nra:
      forall dv, driver_correct (Dv_nra dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_nra dv) (Q_nra q))).
    Proof.
      intros.
      generalize correct_driver_succeeds_cnd; intros.
      elim H0; intros; clear H0 H1.
      elim H2; intros; clear H2 H1.
      rewrite Forall_forall; intros.
      simpl in H1.
      specialize (H0 dv H q).
      rewrite Forall_forall in H0; auto.
    Qed.

    Lemma correct_driver_succeeds_oql:
      forall dv, driver_correct (Dv_oql dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_oql dv) (Q_oql q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; [simpl in *; contradiction| ].
      simpl in H.
      elim H; intros; clear H H1.
      simpl in H0.
      generalize (correct_driver_succeeds_nraenv n); intros. simpl in H.
      specialize (H H2 (oql_to_nraenv q)).
      rewrite Forall_forall in H.
      auto.
    Qed.

    Lemma correct_driver_succeeds_sql:
      forall dv, driver_correct (Dv_sql dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_sql dv) (Q_sql q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; [simpl in *; contradiction| ].
      simpl in H.
      elim H; intros; clear H H1.
      simpl in H0.
      generalize (correct_driver_succeeds_nraenv n); intros. simpl in H.
      specialize (H H2 (sql_to_nraenv q)).
      rewrite Forall_forall in H.
      auto.
    Qed.

    Lemma correct_driver_succeeds_sqlpp:
      forall dv, driver_correct (Dv_sqlpp dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_sqlpp dv) (Q_sqlpp q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; [simpl in *; contradiction| ].
      simpl in H.
      elim H; intros; clear H H1.
      simpl in H0.
      generalize (correct_driver_succeeds_nraenv n); intros. simpl in H.
      specialize (H H2 (sqlpp_to_nraenv q)).
      rewrite Forall_forall in H.
      auto.
    Qed.

    Lemma correct_driver_succeeds_lambda_nra:
      forall dv, driver_correct (Dv_lambda_nra dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_lambda_nra dv) (Q_lambda_nra q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; [simpl in *; contradiction| ].
      simpl in H.
      elim H; intros; clear H H1.
      simpl in H0.
      generalize (correct_driver_succeeds_nraenv n); intros. simpl in H.
      specialize (H H2 (lambda_nra_to_nraenv q)).
      rewrite Forall_forall in H.
      auto.
    Qed.

    Lemma correct_driver_succeeds_javascript:
      forall dv, driver_correct (Dv_javascript dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_javascript dv) (Q_javascript q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; simpl in *; contradiction.
    Qed.

    Lemma correct_driver_succeeds_js_ast:
      forall dv, driver_correct (Dv_js_ast dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_js_ast dv) (Q_js_ast q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; simpl in *; [ contradiction | ].
      destruct H.
      contradiction.
    Qed.

    Lemma correct_driver_succeeds_java:
      forall dv, driver_correct (Dv_java dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_java dv) (Q_java q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; simpl in *; contradiction.
    Qed.

    Lemma correct_driver_succeeds_spark_df:
      forall dv, driver_correct (Dv_spark_df dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_spark_df dv) (Q_spark_df q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; simpl in *; contradiction.
    Qed.

    Lemma correct_driver_succeeds_dnnrc:
      forall dv, driver_correct (Dv_dnnrc dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_dnnrc dv) (Q_dnnrc q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl; trivial| ].
      destruct dv; [simpl in *; contradiction| ].
      simpl in H.
      elim H; intros; contradiction.
    Qed.

    Lemma correct_driver_succeeds_dnnrc_typed:
      forall dv, driver_correct (Dv_dnnrc_typed dv) ->
                 (forall q, Forall query_not_error
                                   (compile (Dv_dnnrc_typed dv) (Q_dnnrc_typed q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      simpl in H.
      simpl in H0.
      destruct dv; simpl in *.
      elim H0; intros.
      rewrite <- H1; simpl; auto.
      contradiction.
      elim H; intros; contradiction.
      elim H; intros; contradiction.
    Qed.

    Theorem compile_with_correct_driver_succeeds (dv:driver) (q:query) :
      driver_correct dv ->
      driver_matches_query dv q ->
      Forall query_not_error (compile dv q).
    Proof.
      intros.
      destruct dv; destruct q; try contradiction; clear H0.
      - apply correct_driver_succeeds_camp_rule; auto.
      - apply correct_driver_succeeds_tech_rule; auto.
      - apply correct_driver_succeeds_designer_rule; auto.
      - apply correct_driver_succeeds_camp; auto.
      - apply correct_driver_succeeds_oql; auto.
      - apply correct_driver_succeeds_sql; auto.
      - apply correct_driver_succeeds_sqlpp; auto.
      - apply correct_driver_succeeds_lambda_nra; auto.
      - apply correct_driver_succeeds_nra; auto.
      - apply correct_driver_succeeds_nraenv_core; auto.
      - apply correct_driver_succeeds_nraenv; auto.
      - apply correct_driver_succeeds_nnrc_core; auto.
      - apply correct_driver_succeeds_nnrc; auto.
      - apply correct_driver_succeeds_nnrs_core; auto.
      - apply correct_driver_succeeds_nnrs; auto.
      - apply correct_driver_succeeds_nnrs_imp; auto.
      - apply correct_driver_succeeds_imp_qcert; auto.
      - apply correct_driver_succeeds_imp_json; auto.
      - apply correct_driver_succeeds_nnrcmr; auto.
      - apply correct_driver_succeeds_dnnrc; auto.
      - apply correct_driver_succeeds_dnnrc_typed; auto.
      - apply correct_driver_succeeds_js_ast; auto.
      - apply correct_driver_succeeds_javascript; auto.
      - apply correct_driver_succeeds_java; auto.
      - apply correct_driver_succeeds_spark_df; auto.
    Qed.

    Definition query_preserves_eval (q1 q2:query) : Prop :=
      forall ev_in, equal_outputs (eval_query h q1 ev_in) (eval_query h q2 ev_in).

    Ltac trivial_same_query :=
      unfold query_preserves_eval; intros; simpl; prove_same_outputs.

    Global Instance query_equiv : Equivalence query_preserves_eval.
    Proof.
      constructor.
      - unfold Reflexive, query_preserves_eval.
        intros.
        unfold equal_outputs.
        match_destr.
        match_destr.
        congruence.
      - unfold Symmetric, query_preserves_eval.
        intros.
        unfold equal_outputs in *.
        specialize (H ev_in).
        destruct (eval_query h x ev_in);
          destruct (eval_query h y ev_in); auto.
        destruct (data_eq_dec d d0).
        rewrite e; match_destr; congruence.
        contradiction.
      - unfold Transitive, query_preserves_eval.
        intros.
        unfold equal_outputs in *.
        specialize (H ev_in);
        specialize (H0 ev_in).
        destruct (eval_query h x ev_in);
          destruct (eval_query h y ev_in);
          destruct (eval_query h z ev_in); auto.
        + contradiction.
        + contradiction.
        + destruct (data_eq_dec d d0).
          rewrite e in *; assumption.
          contradiction.
        + contradiction.
    Qed.

    Lemma query_preserves_eval_trans q1 q2 q3:
      query_preserves_eval q1 q2 -> query_preserves_eval q2 q3 -> query_preserves_eval q1 q3.
    Proof.
      intros H12 H23.
      unfold query_preserves_eval in *.
      intros i.
      specialize (H12 i).
      specialize (H23 i).
      rewrite H12.
      rewrite H23.
      reflexivity.
    Qed.

    Lemma camp_rule_to_camp_preserves_eval (q:camp_rule) :
      query_preserves_eval (Q_camp_rule q) (Q_camp (camp_rule_to_camp q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_camp_rule.
      unfold eval_camp.
      unfold camp_rule_to_camp.
      rewrite camp_rule_to_camp_top_correct.
      trivial_same_query.
    Qed.

    Lemma camp_to_nraenv_core_preserves_eval (q:camp) :
      query_preserves_eval (Q_camp q) (Q_nraenv_core (camp_to_nraenv_core q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_camp.
      unfold eval_nraenv_core.
      unfold camp_to_nraenv_core.
      rewrite camp_to_nraenv_core_top_correct.
      trivial_same_query.
    Qed.

    Lemma camp_to_nraenv_preserves_eval (q:camp) :
      query_preserves_eval (Q_camp q) (Q_nraenv (camp_to_nraenv q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_camp.
      unfold eval_nraenv.
      unfold camp_to_nraenv.
      rewrite camp_to_nraenv_top_correct.
      trivial_same_query.
    Qed.

    Lemma camp_to_nra_preserves_eval (q:camp) :
      query_preserves_eval (Q_camp q) (Q_nra (camp_to_nra q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_camp.
      unfold eval_nra.
      unfold camp_to_nra.
      rewrite camp_to_nra_top_correct.
      trivial_same_query.
    Qed.

    Lemma nra_to_nnrc_core_preserves_eval (q:nra) :
      query_preserves_eval (Q_nra q) (Q_nnrc_core (nra_to_nnrc_core q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nra.
      unfold eval_nnrc_core.
      unfold nra_to_nnrc_core.
      rewrite nra_to_nnrc_core_top_correct.
      trivial_same_query.
    Qed.

    Lemma nra_to_nraenv_core_preserves_eval (q:nra) :
      query_preserves_eval (Q_nra q) (Q_nraenv_core (nra_to_nraenv_core q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nra.
      unfold eval_nraenv_core.
      unfold nra_to_nraenv_core.
      rewrite nra_to_nraenv_core_top_correct.
      trivial_same_query.
    Qed.

    Lemma nraenv_core_to_nraenv_preserves_eval (q:nraenv_core) :
      query_preserves_eval (Q_nraenv_core q) (Q_nraenv (nraenv_core_to_nraenv q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nraenv_core.
      unfold eval_nraenv.
      unfold nraenv_core_to_nraenv.
      rewrite nraenv_core_to_nraenv_top_correct.
      trivial_same_query.
    Qed.

    Lemma nraenv_core_to_nnrc_core_preserves_eval (q:nraenv_core) :
      query_preserves_eval (Q_nraenv_core q) (Q_nnrc_core (nraenv_core_to_nnrc_core q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nraenv_core.
      unfold eval_nnrc_core.
      unfold nraenv_core_to_nnrc_core.
      rewrite nraenv_core_to_nnrc_core_top_correct.
      trivial_same_query.
    Qed.

    Lemma nraenv_core_to_nra_preserves_eval (q:nraenv_core) :
      query_preserves_eval (Q_nraenv_core q) (Q_nra (nraenv_core_to_nra q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nraenv_core.
      unfold eval_nra.
      unfold nraenv_core_to_nra.
      rewrite nraenv_core_to_nra_top_correct.
      trivial_same_query.
    Qed.

    Lemma nraenv_to_nnrc_preserves_eval (q:nraenv) :
      query_preserves_eval (Q_nraenv q) (Q_nnrc (nraenv_to_nnrc q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nraenv.
      unfold eval_nnrc.
      unfold nraenv_to_nnrc.
      rewrite nraenv_to_nnrc_top_correct.
      trivial_same_query.
    Qed.

    Lemma nraenv_to_nraenv_core_preserves_eval (q:nraenv) :
      query_preserves_eval (Q_nraenv q) (Q_nraenv_core (nraenv_to_nraenv_core q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nraenv.
      unfold eval_nraenv_core.
      unfold nraenv_to_nraenv_core.
      rewrite nraenv_to_nraenv_core_top_correct.
      trivial_same_query.
    Qed.

    Lemma nnrc_core_to_nnrc_preserves_eval (q:nnrc_core) :
      query_preserves_eval (Q_nnrc_core q) (Q_nnrc (nnrc_core_to_nnrc q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nnrc_core.
      unfold eval_nnrc.
      unfold nnrc_core_to_nnrc.
      destruct q; simpl.
      rewrite nnrc_core_to_nnrc_top_correct.
      simpl.
      trivial_same_query.
    Qed.

    Lemma nnrc_to_nnrc_core_preserves_eval (q:nnrc) :
      query_preserves_eval (Q_nnrc q) (Q_nnrc_core (nnrc_to_nnrc_core q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nnrc.
      unfold eval_nnrc_core.
      unfold nnrc_to_nnrc_core.
      rewrite nnrc_to_nnrc_core_top_correct.
      trivial_same_query.
    Qed.

    Lemma nnrc_core_to_nnrs_core_preserves_eval inputs (q:nnrc_core) :
      query_preserves_eval (Q_nnrc_core q) (Q_nnrs_core (nnrc_core_to_nnrs_core inputs q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nnrc_core.
      unfold eval_nnrs_core.
      unfold nnrc_core_to_nnrs_core.
      rewrite <- nnrc_core_to_nnrs_core_correct.
      trivial_same_query.
    Qed.

    Lemma nnrc_to_nnrs_preserves_eval inputs (q:nnrc) :
      query_preserves_eval (Q_nnrc q) (Q_nnrs (nnrc_to_nnrs inputs q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nnrc.
      unfold eval_nnrs.
      unfold nnrc_to_nnrs.
      rewrite <- nnrc_to_nnrs_top_correct.
      trivial_same_query.
    Qed.

    Lemma nnrc_to_nnrs_imp_preserves_eval l (q:nnrc) :
      query_preserves_eval
        (Q_nnrc q)
        (Q_nnrs_imp (nnrs_to_nnrs_imp (nnrc_to_nnrs l q))).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nnrc.
      unfold eval_nnrs_imp.
      unfold nnrs_to_nnrs_imp.
      rewrite <- nnrs_to_nnrs_imp_top_correct.
      rewrite <- nnrc_to_nnrs_top_correct.
      reflexivity.
    Qed.

    Lemma nnrc_core_to_nnrs_imp_preserves_eval l (q:nnrc_core) :
      query_preserves_eval (Q_nnrc_core q) (Q_nnrs_imp (nnrs_to_nnrs_imp (nnrc_to_nnrs_top l (proj1_sig q)))).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nnrc_core.
      unfold eval_nnrs_imp.
      unfold nnrs_to_nnrs_imp.
      rewrite <- nnrs_to_nnrs_imp_top_correct.
      rewrite <- nnrc_to_nnrs_top_correct.
      rewrite nnrc_core_to_nnrc_top_correct.
      reflexivity.
    Qed.

    Lemma nnrc_core_to_imp_qcert_preserves_eval l qname (q:nnrc_core) :
      query_preserves_eval (Q_nnrc_core q)
       (Q_imp_qcert (nnrs_imp_to_imp_qcert qname (nnrs_to_nnrs_imp (nnrc_to_nnrs_top l (proj1_sig q))))).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nnrc_core.
      unfold eval_imp_qcert.
      unfold nnrs_to_nnrs_imp.
      unfold nnrs_imp_to_imp_qcert.
      rewrite <- nnrs_imp_to_imp_qcert_top_correct.
      rewrite <- nnrs_to_nnrs_imp_top_correct.
      rewrite <- nnrc_to_nnrs_top_correct.
      rewrite nnrc_core_to_nnrc_top_correct.
      reflexivity.
    Qed.

    Lemma nnrs_to_nnrs_imp_preserves_eval q :
      query_preserves_eval (Q_nnrs q) (Q_nnrs_imp (nnrs_to_nnrs_imp q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nnrs.
      unfold eval_nnrs_imp.
      unfold nnrs_to_nnrs_imp.
      rewrite <- nnrs_to_nnrs_imp_top_correct.
      reflexivity.
    Qed.

    Lemma nnrs_imp_to_imp_qcert_preserves_eval qname q :
      query_preserves_eval (Q_nnrs_imp q) (Q_imp_qcert (nnrs_imp_to_imp_qcert qname q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nnrs_imp.
      unfold eval_imp_qcert.
      unfold nnrs_imp_to_imp_qcert.
      rewrite <- nnrs_imp_to_imp_qcert_top_correct.
      unfold nnrs_imp_eval_top.
      unfold id, olift.
      reflexivity.
    Qed.

    (*
    Lemma nnrc_to_dnnrc_preserves_eval (inputs_loc: vdbindings) (q:nnrc) :
      query_preserves_eval (Q_nnrc q) (Q_dnnrc (nnrc_to_dnnrc inputs_loc q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_nnrc.
      unfold eval_dnnrc.
      unfold nnrc_to_dnnrc.
      rewrite <- nnrc_to_dnnrc_top_correct.
      unfold lift_input.
      trivial_same_query.
      assumption.
      a dmit.
    Qed.
    *)

    Lemma oql_to_nraenv_preserves_eval (q:oql) :
      query_preserves_eval (Q_oql q) (Q_nraenv (oql_to_nraenv q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_oql.
      unfold eval_nraenv.
      unfold oql_to_nraenv.
      rewrite oql_to_nraenv_top_correct.
      trivial_same_query.
    Qed.

    Lemma lambda_nra_to_nraenv_preserves_eval (q:lambda_nra) :
      query_preserves_eval (Q_lambda_nra q) (Q_nraenv (lambda_nra_to_nraenv q)).
    Proof.
      unfold query_preserves_eval; intros.
      simpl.
      unfold eval_lambda_nra.
      unfold eval_nraenv.
      unfold lambda_nra_to_nraenv.
      rewrite lambda_nra_to_nraenv_top_correct.
      trivial_same_query.
    Qed.

    Lemma correct_driver_preserves_eval_imp_json:
      forall dv, driver_correct (Dv_imp_json dv) ->
                 (forall q, Forall (query_preserves_eval (Q_imp_json q))
                                   (compile (Dv_imp_json dv) (Q_imp_json q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      revert q x H0.
      induction dv; simpl in *; intuition; subst; simpl
      ; try solve[trivial_same_query; reflexivity].
    Qed.

    Lemma correct_driver_preserves_eval_imp_qcert:
      forall dv, driver_correct (Dv_imp_qcert dv) ->
                 (forall q, Forall (query_preserves_eval (Q_imp_qcert q))
                                   (compile (Dv_imp_qcert dv) (Q_imp_qcert q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      revert q x H0.
      induction dv; simpl in *; intuition; subst; simpl
      ; try solve[trivial_same_query; reflexivity].
    Qed.

    Lemma correct_driver_preserves_eval_nnrs_imp:
      forall dv, driver_correct (Dv_nnrs_imp dv) ->
                 (forall q, Forall (query_preserves_eval (Q_nnrs_imp q))
                                   (compile (Dv_nnrs_imp dv) (Q_nnrs_imp q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      induction dv.
      + destruct H0; try contradiction.
        rewrite <- H0.
        reflexivity.
      + destruct H; contradiction.
      + destruct H; contradiction.
      + destruct H0; [ rewrite <- H0; reflexivity | ].
        simpl in H0. intuition.
        * rewrite <- H1.
          apply nnrs_imp_to_imp_qcert_preserves_eval.
        * destruct i; simpl in *; try contradiction; intuition.
    Qed.

    Lemma correct_driver_preserves_eval_nnrs:
      forall dv, driver_correct (Dv_nnrs dv) ->
                 (forall q, Forall (query_preserves_eval (Q_nnrs q))
                                   (compile (Dv_nnrs dv) (Q_nnrs q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl| ].
      - trivial_same_query.
        reflexivity.
      - destruct dv; simpl in *; try contradiction.
        apply (query_preserves_eval_trans (Q_nnrs q) (Q_nnrs_imp (nnrs_to_nnrs_imp q))  x).
        * apply nnrs_to_nnrs_imp_preserves_eval.
        * destruct H; clear H.
          specialize (correct_driver_preserves_eval_nnrs_imp n H1 (nnrs_to_nnrs_imp q)).
          rewrite Forall_forall.
          intros Hnnrs_imp.
          specialize (Hnnrs_imp x H0).
          trivial.
    Qed.

    Lemma correct_driver_preserves_eval_cnd:
      (forall dv, driver_correct (Dv_camp dv)
                  -> (forall q, Forall (query_preserves_eval (Q_camp q))
                                       (compile (Dv_camp dv) (Q_camp q))))
      /\ (forall dv, driver_correct (Dv_nra dv)
                     -> (forall q, Forall (query_preserves_eval (Q_nra q))
                                          (compile (Dv_nra dv) (Q_nra q))))
      /\ (forall dv, driver_correct (Dv_nraenv_core dv)
                     -> (forall q, Forall (query_preserves_eval (Q_nraenv_core q))
                                          (compile (Dv_nraenv_core dv) (Q_nraenv_core q))))
      /\ (forall dv, driver_correct (Dv_nraenv dv)
                     -> (forall q, Forall (query_preserves_eval (Q_nraenv q))
                                          (compile (Dv_nraenv dv) (Q_nraenv q))))
      /\ (forall dv, driver_correct (Dv_nnrc_core dv)
                     -> (forall q, Forall (query_preserves_eval (Q_nnrc_core q))
                                          (compile (Dv_nnrc_core dv) (Q_nnrc_core q))))
      /\ (forall dv, driver_correct (Dv_nnrc dv)
                     -> (forall q, Forall (query_preserves_eval (Q_nnrc q))
                                          (compile (Dv_nnrc dv) (Q_nnrc q))))
      /\ (forall dv, driver_correct (Dv_nnrcmr dv)
                     -> (forall q, Forall (query_preserves_eval (Q_nnrcmr q))
                                          (compile (Dv_nnrcmr dv) (Q_nnrcmr q)))).
    Proof.
      apply cnd_combined_ind
      ; simpl; try reflexivity; intros
      ; apply Forall_forall; simpl; intros
      ; elim H0; intros; try contradiction
      ; clear H0; try (rewrite <- H1; simpl; trivial_same_query).
      (* CAMP to cNRAEnv arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (camp_to_nraenv_core q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply camp_to_nraenv_core_preserves_eval.
      (* CAMP to NRAEnv arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (camp_to_nraenv q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply camp_to_nraenv_preserves_eval.
      (* CAMP to NRA arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (camp_to_nra q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply camp_to_nra_preserves_eval.
      (* NRA to cNNRC arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (nra_to_nnrc_core q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply nra_to_nnrc_core_preserves_eval.
      (* NRA to cNRAEnv arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (nra_to_nraenv_core q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply nra_to_nraenv_core_preserves_eval.
      (* cNRAEnv to NRAEnv arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (nraenv_core_to_nraenv q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply nraenv_core_to_nraenv_preserves_eval.
      (* cNRAEnv to cNNRC arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (nraenv_core_to_nnrc_core q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply nraenv_core_to_nnrc_core_preserves_eval.
      (* cNRAEnv to NRA arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (nraenv_core_to_nra q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply nraenv_core_to_nra_preserves_eval.
      (* NRAEnv to NNRC arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (nraenv_to_nnrc q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply nraenv_to_nnrc_preserves_eval.
      (* NRAEnv to NNRC arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (nraenv_to_nraenv_core q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply nraenv_to_nraenv_core_preserves_eval.
      (* cNNRC to NNRSimp arrow *)
      - destruct H as [_ H].
        destruct n; simpl in *; intuition
        ; try contradiction; subst; simpl
        ; try apply nnrc_core_to_nnrs_core_preserves_eval.
        destruct n; simpl in *; intuition; subst.
        apply (query_preserves_eval_trans (Q_nnrc_core q) (Q_nnrs_imp (nnrs_to_nnrs_imp (nnrc_to_nnrs_top l (proj1_sig q)))) x).
        * apply (nnrc_core_to_nnrs_imp_preserves_eval).
        * specialize (correct_driver_preserves_eval_nnrs_imp n H3 (nnrs_to_nnrs_imp (nnrc_to_nnrs_top l (proj1_sig q)))).
          intros Hn.
          rewrite Forall_forall in Hn.
          specialize (Hn x H1).
          trivial.
      (* cNNRC to NNRC arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (nnrc_core_to_nnrc q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply nnrc_core_to_nnrc_preserves_eval.
      (* NNRC to cNNRC arrow *)
      - elim H1; intros; clear H1.
        rewrite <- H0; simpl; trivial_same_query.
        specialize (H H3 (nnrc_to_nnrc_core q)).
        rewrite Forall_forall in H; intros.
        specialize (H x H0). clear H0.
        rewrite <- H.
        clear H2 H.
        apply nnrc_to_nnrc_core_preserves_eval.
      (* NNRC to NNRS arrow *)
      - destruct n; destruct H.
        + simpl in *.
          intuition; subst.
          apply nnrc_to_nnrs_preserves_eval.
        + destruct H1; simpl in *; subst
          ; try apply nnrc_to_nnrs_preserves_eval.
          apply (query_preserves_eval_trans (Q_nnrc q) (Q_nnrs_imp (nnrs_to_nnrs_imp (nnrc_to_nnrs_top l q))) x).
        * apply (nnrc_to_nnrs_imp_preserves_eval).
        * destruct H0.
          specialize (correct_driver_preserves_eval_nnrs_imp n H2 (nnrs_to_nnrs_imp (nnrc_to_nnrs_top l q))).
          intros Hn.
          rewrite Forall_forall in Hn.
          specialize (Hn x H1).
          trivial.

      (* NNRC to DNNRC arrow *)
      - elim H; intros; contradiction. (* Not proved *)
      (* NNRC to js_ast arrow *)
      - elim H; intros; contradiction. (* Not proved *)
      (* NNRC to Java arrow *)
      - elim H; intros; contradiction. (* Not proved *)
    Qed.

    Lemma correct_driver_preserves_eval_camp_rule:
      forall dv, driver_correct (Dv_camp_rule dv) ->
                 (forall q, Forall (query_preserves_eval (Q_camp_rule q))
                                   (compile (Dv_camp_rule dv) (Q_camp_rule q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; intros.
      - rewrite <- H1; simpl; trivial_same_query.
      - clear H0.
        destruct dv; simpl in H1; [contradiction| ].
        generalize correct_driver_preserves_eval_cnd; intros.
        elim H0; intros; clear H0 H3.
        elim H; intros.
        specialize (H2 c H3 (camp_rule_to_camp q)).
        rewrite Forall_forall in H2.
        specialize (H2 x).
        rewrite <- H2.
        apply camp_rule_to_camp_preserves_eval.
        simpl.
        apply H1.
    Qed.

    Lemma correct_driver_preserves_eval_tech_rule:
      forall dv, driver_correct (Dv_tech_rule dv) ->
                 (forall q, Forall (query_preserves_eval (Q_tech_rule q))
                                   (compile (Dv_tech_rule dv) (Q_tech_rule q))).
    Proof.
      intros.
      simpl in H.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; intros.
      - rewrite <- H1; simpl; trivial_same_query.
      - clear H0.
        destruct dv; simpl in H1; [contradiction| ].
        elim H; intros; contradiction.
    Qed.

    Lemma correct_driver_preserves_eval_designer_rule:
      forall dv, driver_correct (Dv_designer_rule dv) ->
                 (forall q, Forall (query_preserves_eval (Q_designer_rule q))
                                   (compile (Dv_designer_rule dv) (Q_designer_rule q))).
    Proof.
      intros.
      simpl in H.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; intros.
      - rewrite <- H1; simpl; trivial_same_query.
      - clear H0.
        destruct dv; simpl in H1; [contradiction| ].
        elim H; intros; contradiction.
    Qed.

    Lemma correct_driver_preserves_eval_camp:
      forall dv, driver_correct (Dv_camp dv) ->
                 (forall q, Forall (query_preserves_eval (Q_camp q))
                                   (compile (Dv_camp dv) (Q_camp q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      generalize correct_driver_preserves_eval_cnd; intros.
      elim H1; intros; clear H1 H3.
      specialize (H2 dv H q).
      rewrite Forall_forall in H2.
      auto.
    Qed.

    Lemma correct_driver_preserves_eval_nra:
      forall dv, driver_correct (Dv_nra dv) ->
                 (forall q, Forall (query_preserves_eval (Q_nra q))
                                   (compile (Dv_nra dv) (Q_nra q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      generalize correct_driver_preserves_eval_cnd; intros.
      elim H1; intros; clear H1 H2.
      elim H3; intros; clear H3 H2.
      specialize (H1 dv H q).
      rewrite Forall_forall in H1.
      auto.
    Qed.

    Lemma correct_driver_preserves_eval_nraenv:
      forall dv, driver_correct (Dv_nraenv dv) ->
                 (forall q, Forall (query_preserves_eval (Q_nraenv q))
                                   (compile (Dv_nraenv dv) (Q_nraenv q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      generalize correct_driver_preserves_eval_cnd; intros.
      elim H1; intros; clear H1 H2.
      elim H3; intros; clear H3 H1.
      elim H2; intros; clear H2 H1.
      elim H3; intros; clear H3 H2.
      specialize (H1 dv H q).
      rewrite Forall_forall in H1.
      auto.
    Qed.

    Lemma correct_driver_preserves_eval_nraenv_core:
      forall dv, driver_correct (Dv_nraenv_core dv) ->
                 (forall q, Forall (query_preserves_eval (Q_nraenv_core q))
                                   (compile (Dv_nraenv_core dv) (Q_nraenv_core q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      generalize correct_driver_preserves_eval_cnd; intros.
      elim H1; intros; clear H1 H2.
      elim H3; intros; clear H3 H1.
      elim H2; intros; clear H2 H3.
      specialize (H1 dv H q).
      rewrite Forall_forall in H1.
      auto.
    Qed.

    Lemma correct_driver_preserves_eval_nnrc:
      forall dv, driver_correct (Dv_nnrc dv) ->
                 (forall q, Forall (query_preserves_eval (Q_nnrc q))
                                   (compile (Dv_nnrc dv) (Q_nnrc q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      generalize correct_driver_preserves_eval_cnd; intros.
      elim H1; intros; clear H1 H2.
      elim H3; intros; clear H3 H1.
      elim H2; intros; clear H2 H1.
      elim H3; intros; clear H3 H1.
      elim H2; intros; clear H2 H1.
      elim H3; intros; clear H2 H3.
      specialize (H1 dv H q).
      rewrite Forall_forall in H1.
      auto.
    Qed.

    Lemma correct_driver_preserves_eval_nnrc_core:
      forall dv, driver_correct (Dv_nnrc_core dv) ->
                 (forall q, Forall (query_preserves_eval (Q_nnrc_core q))
                                   (compile (Dv_nnrc_core dv) (Q_nnrc_core q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      generalize correct_driver_preserves_eval_cnd; intros.
      elim H1; intros; clear H1 H2.
      elim H3; intros; clear H3 H1.
      elim H2; intros; clear H2 H1.
      elim H3; intros; clear H3 H1.
      elim H2; intros; clear H2 H3.
      specialize (H1 dv H q).
      rewrite Forall_forall in H1.
      auto.
    Qed.




    Lemma correct_driver_preserves_eval_nnrs_core:
      forall dv, driver_correct (Dv_nnrs_core dv) ->
                 (forall q, Forall (query_preserves_eval (Q_nnrs_core q))
                                   (compile (Dv_nnrs_core dv) (Q_nnrs_core q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; clear H0; intros; [rewrite <- H0; simpl| ].
      - trivial_same_query.
        reflexivity.
      - destruct dv; simpl in *; try contradiction.
        destruct n; simpl in *; intuition; subst.
        + trivial_same_query; try reflexivity.
        + trivial_same_query; try reflexivity.
        + apply (query_preserves_eval_trans (Q_nnrs_core q) (Q_nnrs_imp (nnrs_to_nnrs_imp (nnrs_core_to_nnrs q))) x).
          * apply nnrs_to_nnrs_imp_preserves_eval.
          * specialize (correct_driver_preserves_eval_nnrs_imp n H3 (nnrs_to_nnrs_imp (nnrs_core_to_nnrs q))).
            intros Hn.
            rewrite Forall_forall in Hn.
            specialize (Hn x H2).
            trivial.
    Qed.

    Lemma correct_driver_preserves_eval_nnrcmr:
      forall dv, driver_correct (Dv_nnrcmr dv) ->
                 (forall q, Forall (query_preserves_eval (Q_nnrcmr q))
                                   (compile (Dv_nnrcmr dv) (Q_nnrcmr q))).
    Proof.
      intros.
      simpl in H.
      rewrite Forall_forall; intros.
      simpl in H0.
      destruct dv; simpl in *.
      - elim H0; intros; clear H0.
        rewrite <- H1; simpl. trivial_same_query.
        contradiction.
      - elim H; intros; contradiction.
      - elim H; intros; contradiction.
      - elim H; intros; contradiction.
    Qed.

    Lemma correct_driver_preserves_eval_dnnrc:
      forall dv, driver_correct (Dv_dnnrc dv) ->
                 (forall q, Forall (query_preserves_eval (Q_dnnrc q))
                                   (compile (Dv_dnnrc dv) (Q_dnnrc q))).
    Proof.
      intros.
      simpl in H.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; intros; clear H0.
      rewrite <- H1; simpl; trivial_same_query.
      destruct dv; simpl in H1; [contradiction| ].
      elim H; intros; contradiction.
    Qed.

    Lemma correct_driver_preserves_eval_dnnrc_typed:
      forall dv, driver_correct (Dv_dnnrc_typed dv) ->
                 (forall q, Forall (query_preserves_eval (Q_dnnrc_typed q))
                                   (compile (Dv_dnnrc_typed dv) (Q_dnnrc_typed q))).
    Proof.
      intros.
      simpl in H.
      rewrite Forall_forall; intros.
      destruct dv; simpl in *.
      - elim H0; intros; clear H0.
        rewrite <- H1; simpl. trivial_same_query.
        contradiction.
      - elim H; intros; contradiction.
      - elim H; intros; contradiction.
    Qed.

    Lemma correct_driver_preserves_eval_oql:
      forall dv, driver_correct (Dv_oql dv) ->
                 (forall q, Forall (query_preserves_eval (Q_oql q))
                                   (compile (Dv_oql dv) (Q_oql q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; intros.
      - rewrite <- H1; simpl; trivial_same_query.
      - clear H0.
        destruct dv; simpl in H1; [contradiction| ].
        generalize correct_driver_preserves_eval_cnd; intros.
        elim H0; intros; clear H0 H2.
        elim H3; intros; clear H0 H3.
        elim H2; intros; clear H0 H2.
        elim H3; intros; clear H2 H3.
        elim H; intros.
        specialize (H0 n H3 (oql_to_nraenv q)).
        rewrite Forall_forall in H0.
        specialize (H0 x).
        rewrite <- H0.
        apply oql_to_nraenv_preserves_eval.
        simpl.
        apply H1.
    Qed.

    Lemma correct_driver_preserves_eval_lambda_nra:
      forall dv, driver_correct (Dv_lambda_nra dv) ->
                 (forall q, Forall (query_preserves_eval (Q_lambda_nra q))
                                   (compile (Dv_lambda_nra dv) (Q_lambda_nra q))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; intros.
      - rewrite <- H1; simpl; trivial_same_query.
      - clear H0.
        destruct dv; simpl in H1; [contradiction| ].
        generalize correct_driver_preserves_eval_cnd; intros.
        elim H0; intros; clear H0 H2.
        elim H3; intros; clear H0 H3.
        elim H2; intros; clear H0 H2.
        elim H3; intros; clear H2 H3.
        elim H; intros.
        specialize (H0 n H3 (lambda_nra_to_nraenv q)).
        rewrite Forall_forall in H0.
        specialize (H0 x).
        rewrite <- H0.
        apply lambda_nra_to_nraenv_preserves_eval.
        simpl.
        apply H1.
    Qed.

    Lemma correct_driver_preserves_eval_sql:
      forall dv, driver_correct (Dv_sql dv) ->
                 (forall q, Forall (query_preserves_eval (Q_sql q))
                                   (compile (Dv_sql dv) (Q_sql q))).
    Proof.
      intros.
      simpl in H.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; intros.
      - rewrite <- H1; simpl; trivial_same_query.
      - clear H0.
        destruct dv; simpl in H1; [contradiction| ].
        elim H; intros; contradiction.
    Qed.

    Lemma correct_driver_preserves_eval_sqlpp:
      forall dv, driver_correct (Dv_sqlpp dv) ->
                 (forall q, Forall (query_preserves_eval (Q_sqlpp q))
                                   (compile (Dv_sqlpp dv) (Q_sqlpp q))).
    Proof.
      intros.
      simpl in H.
      rewrite Forall_forall; intros.
      simpl in H0.
      elim H0; intros.
      - rewrite <- H1; simpl; trivial_same_query.
      - clear H0.
        destruct dv; simpl in H1; [contradiction| ].
        elim H; intros; contradiction.
    Qed.

    Lemma correct_driver_preserves_eval_js_ast:
      forall dv, driver_correct (Dv_js_ast dv) ->
                 (forall q, Forall (query_preserves_eval (Q_js_ast q))
                                   (compile (Dv_js_ast dv) (Q_js_ast q))).
    Proof.
      intros.
      simpl in H.
      rewrite Forall_forall; intros.
      destruct dv; simpl in *.
      elim H0; intros.
      - rewrite <- H1; simpl; trivial_same_query.
      - contradiction.
      - destruct H; contradiction.
    Qed.

    Lemma correct_driver_preserves_eval_javascript:
      forall dv, driver_correct (Dv_javascript dv) ->
                 (forall q, Forall (query_preserves_eval (Q_javascript q))
                                   (compile (Dv_javascript dv) (Q_javascript q))).
    Proof.
      intros.
      simpl in H.
      rewrite Forall_forall; intros.
      destruct dv; simpl in *.
      elim H0; intros.
      - rewrite <- H1; simpl; trivial_same_query.
      - contradiction.
    Qed.

    Lemma correct_driver_preserves_eval_java:
      forall dv, driver_correct (Dv_java dv) ->
                 (forall q, Forall (query_preserves_eval (Q_java q))
                                   (compile (Dv_java dv) (Q_java q))).
    Proof.
      intros.
      simpl in H.
      rewrite Forall_forall; intros.
      destruct dv; simpl in *.
      elim H0; intros.
      - rewrite <- H1; simpl; trivial_same_query.
      - contradiction.
    Qed.

    Lemma correct_driver_preserves_eval_spark_df:
      forall dv, driver_correct (Dv_spark_df dv) ->
                 (forall q, Forall (query_preserves_eval (Q_spark_df q))
                                   (compile (Dv_spark_df dv) (Q_spark_df q))).
    Proof.
      intros.
      simpl in H.
      rewrite Forall_forall; intros.
      destruct dv; simpl in *.
      elim H0; intros.
      - rewrite <- H1; simpl; trivial_same_query.
      - contradiction.
    Qed.

    (** This is an initial version of correctness theorem for the
compiler driver as a whole. *)

(** Assuming the driver [dv] is correct (i.e., only follows
verified compilation paths),
And assuming the driver [dv] matches the input query,
then:
- For every query [q] that matches
the expected input of driver [dv]
- for every produced compilation
steps I.e., [q'] in the list returned by [compile dv q], we have:
- [q'] preserves the evaluation semantics for [q]

I.e., for all input data, evaluation of [q] and [q'] over that
input data returns the same output data. *)

    Theorem compile_with_correct_driver_preserves_eval (dv:driver) (q:query) :
      driver_correct dv ->
      driver_matches_query dv q ->
      Forall (query_preserves_eval q) (compile dv q).
    Proof.
      intros.
      destruct dv; destruct q; try contradiction; clear H0.
      - apply correct_driver_preserves_eval_camp_rule; auto.
      - apply correct_driver_preserves_eval_tech_rule; auto.
      - apply correct_driver_preserves_eval_designer_rule; auto.
      - apply correct_driver_preserves_eval_camp; auto.
      - apply correct_driver_preserves_eval_oql; auto.
      - apply correct_driver_preserves_eval_sql; auto.
      - apply correct_driver_preserves_eval_sqlpp; auto.
      - apply correct_driver_preserves_eval_lambda_nra; auto.
      - apply correct_driver_preserves_eval_nra; auto.
      - apply correct_driver_preserves_eval_nraenv_core; auto.
      - apply correct_driver_preserves_eval_nraenv; auto.
      - apply correct_driver_preserves_eval_nnrc_core; auto.
      - apply correct_driver_preserves_eval_nnrc; auto.
      - apply correct_driver_preserves_eval_nnrs_core; auto.
      - apply correct_driver_preserves_eval_nnrs; auto.
      - apply correct_driver_preserves_eval_nnrs_imp; auto.
      - apply correct_driver_preserves_eval_imp_qcert; auto.
      - apply correct_driver_preserves_eval_imp_json; auto.
      - apply correct_driver_preserves_eval_nnrcmr; auto.
      - apply correct_driver_preserves_eval_dnnrc; auto.
      - apply correct_driver_preserves_eval_dnnrc_typed; auto.
      - apply correct_driver_preserves_eval_js_ast; auto.
      - apply correct_driver_preserves_eval_javascript; auto.
      - apply correct_driver_preserves_eval_java; auto.
      - apply correct_driver_preserves_eval_spark_df; auto.
    Qed.

  End eval_preserved.

  Section Verified.

    Lemma driver_nraenv_to_imp_qcert_verified_correct conf :
      driver_correct (driver_of_path conf (L_nraenv :: L_nnrc :: L_nnrc_core :: L_nnrc :: L_nnrs :: L_nnrs_imp :: L_imp_qcert :: nil)).
    Proof.
      simpl; split; auto.
    Qed.

    Lemma driver_nraenv_to_imp_qcert_verified_matches_query conf q :
      driver_matches_query
        (driver_of_path conf (L_nraenv :: L_nnrc :: L_nnrc_core :: L_nnrc :: L_nnrs :: L_nnrs_imp :: L_imp_qcert :: nil)) 
        (Q_nraenv q).
    Proof.
      unfold driver_of_path.
      simpl.
      unfold driver_matches_query.
      auto.
    Qed.

    Context {h:list(string*string)}.

    Lemma compile_nraenv_to_imp_qcert_verified_correct conf q q' :
      compile_nraenv_to_imp_qcert_verified conf (Q_nraenv q) = q' ->
      exists q'',
        (q' = Q_imp_qcert q'' /\ (@query_preserves_eval h (Q_nraenv q) (Q_imp_qcert q''))).
    Proof.
      elim (compile_nraenv_to_imp_qcert_verified_yields_result conf q); intros.
      unfold compile_nraenv_to_imp_qcert_verified in *.
      generalize (@compile_with_correct_driver_preserves_eval h
                    (driver_of_path conf (L_nraenv :: L_nnrc :: L_nnrc_core :: L_nnrc :: L_nnrs :: L_nnrs_imp :: L_imp_qcert :: nil))
                    (Q_nraenv q)
                    (driver_nraenv_to_imp_qcert_verified_correct conf)
                    (driver_nraenv_to_imp_qcert_verified_matches_query conf q)).
      intro Heval.
      rewrite H in H0.
      rewrite <- H0.
      exists x.
      split.
      - reflexivity.
      - rewrite Forall_forall in Heval.
        apply Heval; clear Heval.
        simpl.
        right; right; right; right; right; right; left; simpl.
        simpl in H.
        auto.
    Qed.

    Lemma stuff d:
      (lift_input (map (fun xy : string * data => (fst xy, Dlocal (snd xy))) d)) = d.
    Proof.
      induction d; simpl; [reflexivity| ].
      destruct a; simpl.
      f_equal.
      assumption.
    Qed.
    
    Lemma nraenv_to_imp_qcert_correct conf (qnra:nraenv) (x:imp_qcert):
      CompDriver.compile_nraenv_to_imp_qcert_verified conf (Q_nraenv qnra) = Q_imp_qcert x ->
      forall d : bindings, nraenv_eval_top h qnra d =
                           imp_qcert_eval_top h d x.
    Proof.
      intros.
      generalize (compile_nraenv_to_imp_qcert_verified_correct conf qnra (Q_imp_qcert x) H); intros; clear H.
      elim H0; clear H0; intros.
      elim H; clear H; intros.
      unfold query_preserves_eval in H0.
      specialize (H0 (map (fun xy => (fst xy, Dlocal (snd xy))) d)).
      unfold equal_outputs in H0.
      simpl in H0.
      inversion H; clear H; subst.
      case_eq (eval_nraenv h qnra (lift_input (map (fun xy : string * data => (fst xy, Dlocal (snd xy))) d))); intros;
        case_eq (eval_imp_qcert h x0 (lift_input (map (fun xy : string * data => (fst xy, Dlocal (snd xy))) d))); intros;
      rewrite H in H0; simpl in H0;
      rewrite H1 in H0; simpl in H0;
        try contradiction;
          rewrite stuff in H; rewrite stuff in H1.
      - unfold eval_nraenv in H; rewrite H.
        unfold eval_imp_qcert in H1; rewrite H1.
        case_eq (data_eq_dec d0 d1); intros.
        subst; auto.
        rewrite H2 in H0; contradiction.
      - unfold eval_nraenv in H; rewrite H.
        unfold eval_imp_qcert in H1; rewrite H1.
        auto.
    Qed.

  End Verified.
End CompCorrectness.
