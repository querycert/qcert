(*
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
Require Import NNRSimptoImpData.
Require Import ImpDatatoImpEJson.
Require Import ImpEJsontoJavaScriptAst.
Require Import JavaScriptAsttoJavaScript.
Require Import NNRCtoDNNRC.
Require Import NNRCtoNNRCMR.
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
Require Import NNRCMROptim.
Require Import tDNNRCOptim.
Require Import NNRSimpOptim.
(* Require Import ImpOptim. *)
Require Import OptimizerLogger.

(* Foreign Datatypes Support *)
Require Import ForeignDataToEJson.
Require Import ForeignToEJsonRuntime.
Require Import ForeignEJsonToWSON.
Require Import ForeignToReduceOps.
Require Import ForeignToSpark.
Require Import ForeignToJava.
Require Import ForeignToJavaScriptAst.
Require Import ForeignToScala.

(** Compiler Driver *)
Require Import CompLang.
Require Import CompEnv.
Require Import CompConfig.
Require Import CompDriver.

Section CompCustom.
  (* Some useful notations *)
  Local Open Scope list_scope.

  (* Context *)
  Context {ft:foreign_type}.
  Context {fruntime:foreign_runtime}.
  Context {foreign_ejson_model:Set}.
  Context {fejson:foreign_ejson foreign_ejson_model}.
  Context {ftowson:foreign_to_wson foreign_ejson_model}.
  Context {foreign_ejson_runtime_op : Set}.
  Context {ftejson:foreign_to_ejson foreign_ejson_model foreign_ejson_runtime_op}.
  Context {frtejson:foreign_to_ejson_runtime}.
  Context {fredop:foreign_reduce_op}.
  Context {ftoredop:foreign_to_reduce_op}.
  Context {bm:brand_model}.
  Context {ftyping: foreign_typing}.
  Context {nraenv_logger:optimizer_logger string nraenv}.
  Context {nnrc_logger:optimizer_logger string nnrc}.
  Context {nnrs_imp_expr_logger:optimizer_logger string nnrs_imp_expr}.
  Context {nnrs_imp_stmt_logger:optimizer_logger string nnrs_imp_stmt}.
  Context {nnrs_imp_logger:optimizer_logger string nnrs_imp}.
  Context {dnnrc_logger:optimizer_logger string (DNNRCBase.dnnrc_base _ (type_annotation unit) dataframe)}.
  Context {ftojava:foreign_to_java}.
  Context {ftos:foreign_to_scala}.
  Context {ftospark:foreign_to_spark}.
  Context {ftjsast:foreign_ejson_to_ajavascript}.

  Section Verified.
    Definition compile_nraenv_to_imp_data_verified (conf:driver_config) (q:query) : query :=
      let dv := driver_of_path
                  conf
                  (L_nraenv::L_nnrc::L_nnrs::L_nnrs_imp::L_imp_data::nil)
      in
      match List.rev (compile dv q) with
      | nil => Q_error "No compilation result!"
      | target :: _ => target
      end.

    Lemma compile_nraenv_to_imp_data_verified_yields_result conf q :
      exists q', compile_nraenv_to_imp_data_verified conf (Q_nraenv q) = Q_imp_data q'.
    Proof.
      unfold compile_nraenv_to_imp_data_verified.
      simpl.
      exists (nnrs_imp_to_imp_data
                (comp_qname_lowercase conf)
                (nnrs_to_nnrs_imp
                   (nnrc_to_nnrs (vars_of_constants_config (comp_constants conf))
                                 (NNRCLet init_venv (NNRCConst (drec nil))
                                          (NNRCLet init_vid (NNRCConst dunit)
                                                   (NRAEnvtoNNRC.nraenv_to_nnrc q init_vid init_venv)))))).
      reflexivity.
    Qed.

    Definition compile_nraenv_to_imp_ejson_verified (conf:driver_config) (q:query) : query :=
      let dv :=
          driver_of_path
            conf
            (L_nraenv::L_nnrc::L_nnrs::L_nnrs_imp::L_imp_data::L_imp_ejson::nil)
      in
      match List.rev (compile dv q) with
      | nil => Q_error "No compilation result!"
      | target :: _ => target
      end.

    Lemma compile_nraenv_to_imp_ejson_verified_yields_result conf q :
      exists q', compile_nraenv_to_imp_ejson_verified conf (Q_nraenv q) = Q_imp_ejson q'.
    Proof.
      unfold compile_nraenv_to_imp_ejson_verified.
      exists (imp_data_to_imp_ejson
                (nnrs_imp_to_imp_data
                   (comp_qname_lowercase conf)
                   (nnrs_to_nnrs_imp
                      (nnrc_to_nnrs
                         (vars_of_constants_config (comp_constants conf))
                         (NNRCLet init_venv (NNRCConst (drec nil))
                                  (NNRCLet init_vid (NNRCConst dunit)
                                           (NRAEnvtoNNRC.nraenv_to_nnrc q init_vid init_venv))))))).
      reflexivity.
    Qed.

  End Verified.

  Section Others.
    Definition compile_nnrc_to_javascript_ast (conf:driver_config) (q:query) : query :=
      let dv := driver_of_path conf (L_nnrc::L_nnrs::L_nnrs_imp::L_imp_data::L_imp_ejson::L_js_ast::nil) in
      match List.rev (compile dv q) with
      | nil => Q_error "No compilation result!"
      | target :: _ => target
      end.

    Definition compile_nnrc_to_java (conf:driver_config) (q:query) : query :=
      let dv := driver_of_path conf (L_nnrc::L_java::nil) in
      match List.rev (compile dv q) with
      | nil => Q_error "No compilation result!"
      | target :: _ => target
      end.

  End Others.

End CompCustom.

