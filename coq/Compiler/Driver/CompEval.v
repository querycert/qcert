(*
 * COPYRight 2015-2017 IBM Corporation
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

Section CompEval.

  Require Import String.

  (* Basic *)
  Require Import BasicSystem.
  Require Import TypingRuntime.

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
  Require Import tDNNRCRuntime.
  Require Import CAMPRuntime.
  (** Target languages *)
  Require Import JavaScriptRuntime.
  Require Import JavaRuntime.
  Require Import SparkRDDRuntime.
  Require Import SparkDFRuntime.
  Require Import CloudantRuntime.

  (* Foreign Support *)
  Require Import ForeignToReduceOps.
  Require Import ForeignToSpark.
  Require Import ForeignCloudant.
  Require Import ForeignToCloudant.
  
  (* Compiler Driver *)
  Require Import CompLang.
  Require Import CompEnv.

  (* Some useful notations *)
  Local Open Scope list_scope.

  (* Context *)
  
  Context {fruntime:foreign_runtime}.   (* Necessary for everything, including data *)
  Context {fredop:foreign_reduce_op}.   (* Necessary for NNRCMR evaluation *)
  Context {fcloudant:foreign_cloudant}. (* Necessary for CldMR evaluation *)
  Context {ft:foreign_type}.            (* Necessary for DNNRC evaluation *)
  Context {bm:brand_model}.             (* Necessary for DNNRC evaluation *)

  Context (h:list(string*string)).

  (* Evaluation functions *)
  Section EvalFunctions.

    (* Language: camp_rule *)
    Definition eval_camp_rule (q:camp_rule) (cenv: bindings) : option data :=
      CAMPRule.camp_rule_eval_top h q cenv.
    Definition eval_camp_rule_debug (debug:bool) (q:camp_rule) (cenv: bindings) : string :=
      CAMPRule.camp_rule_eval_top_debug h debug q cenv.

    (* Language: camp *)
    Definition eval_camp (q:camp) (cenv: bindings) : option data :=
      CAMP.camp_eval_top h q cenv.
    Definition eval_camp_debug (debug:bool) (q:camp) (cenv: bindings) : string :=
      CAMP.camp_eval_top_debug h debug q cenv.

    (* Language: oql *)
    Definition eval_oql (q:oql) (cenv: bindings) : option data :=
      OQL.oql_eval_top h q cenv.

    (* Language: lambda_nra *)
    Definition eval_lambda_nra (q:lambda_nra) (cenv: bindings) : option data :=
      LambdaNRA.lambda_nra_eval_top h q cenv.

    (* Language: nra *)
    Definition eval_nra (q:nra) (cenv: bindings) : option data :=
      NRA.nra_eval_top h q cenv.

    (* Language: nraenv_core *)
    Definition eval_nraenv_core (q:nraenv_core) (cenv: bindings) : option data :=
      cNRAEnv.nraenv_core_eval_top h q cenv.

    (* Language: nraenv *)
    Definition eval_nraenv (q:nraenv) (cenv: bindings) : option data :=
      NRAEnv.nraenv_eval_top h q cenv.

    (* Language: nnrc_core *)
    Definition eval_nnrc_core (q:nnrc_core) (cenv: bindings) : option data :=
      cNNRC.nnrc_core_eval_top h q cenv.

    (* Language: nnrc *)
    Definition eval_nnrc (q:nnrc) (cenv: bindings) : option data :=
      NNRC.nnrc_eval_top h q cenv.

    (* Language: nnrcmr *)
    Definition eval_nnrcmr (q:nnrcmr) (dcenv: dbindings) : option data :=
      NNRCMR.nnrcmr_eval_top h init_vinit q dcenv.

    (* Language: cldmr *)
    Definition eval_cldmr (q:cldmr) (cenv: bindings) : option data :=
      CldMR.cldmr_eval_top h init_vinit q cenv.

    (* Language: dnnrc *)
    Definition eval_dnnrc (q:dnnrc) (cenv: dbindings) : option data :=
      DNNRC.dnnrc_dataframe_eval_top h q cenv.

    (* Language: dnnrc_typed *)
    Definition eval_dnnrc_typed (q:dnnrc_typed) (cenv: dbindings) : option data :=
      tDNNRC.dnnrc_dataframe_typed_eval_top h q cenv.

  End EvalFunctions.

  Section EvalDriver.
    Definition eval_input : Set := dbindings.

    Definition lift_input (ev_in:eval_input) : bindings :=
      unlocalize_constants ev_in.

    Inductive eval_output : Set :=
    | Ev_out_unsupported : string -> eval_output
    | Ev_out_failed : eval_output
    | Ev_out_returned : data -> eval_output
    | Ev_out_returned_debug : string -> eval_output
    .

    Definition lift_output (result:option data) :=
      match result with
      | None => Ev_out_failed
      | Some d => Ev_out_returned d
      end.

    Definition eval_query (q:query) (ev_in:eval_input) : eval_output :=
      match q with
      | Q_camp_rule q => lift_output (eval_camp_rule q (lift_input ev_in))
      | Q_tech_rule _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_designer_rule _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_camp q => lift_output (eval_camp q (lift_input ev_in))
      | Q_oql q => lift_output (eval_oql q (lift_input ev_in))
      | Q_sql _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_sqlpp q => Ev_out_unsupported "SQL++ eval not yet implemented"
      | Q_lambda_nra q => lift_output (eval_lambda_nra q (lift_input ev_in))
      | Q_nra q => lift_output (eval_nra q (lift_input ev_in))
      | Q_nraenv_core q => lift_output (eval_nraenv_core q (lift_input ev_in))
      | Q_nraenv q => lift_output (eval_nraenv q (lift_input ev_in))
      | Q_nnrc_core q => lift_output (eval_nnrc_core q (lift_input ev_in))
      | Q_nnrc q => lift_output (eval_nnrc q (lift_input ev_in))
      | Q_nnrcmr q => lift_output (eval_nnrcmr q ev_in) (* XXX Does not localize, keeps distributed information XXX *)
      | Q_cldmr q => lift_output (eval_cldmr q (lift_input ev_in))
      | Q_dnnrc q => lift_output (eval_dnnrc q ev_in) (* XXX Does not localize, keeps distributed information XXX *)
      | Q_dnnrc_typed q => lift_output (eval_dnnrc_typed q ev_in) (* XXX Does not localize, keeps distributed information XXX *)
      | Q_javascript _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_java _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_spark_rdd _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_spark_df _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_cloudant _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_error err => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      end.

    Definition eval_query_debug (q:query) (ev_in:eval_input) : eval_output :=
      match q with
      | Q_camp_rule q => Ev_out_returned_debug (eval_camp_rule_debug true q (lift_input ev_in))
      | Q_tech_rule _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_designer_rule _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_camp q => Ev_out_returned_debug (eval_camp_debug true q (lift_input ev_in))
      | Q_oql _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_sql _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_sqlpp _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_lambda_nra _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_nra _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_nraenv_core _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_nraenv _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_nnrc_core _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_nnrc _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_nnrcmr _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_cldmr _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_dnnrc _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_dnnrc_typed _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_javascript _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_java _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_spark_rdd _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_spark_df _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_cloudant _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_error err => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      end.

    Definition equal_outputs o1 o2 :=
      match (o1,o2) with
      | (Ev_out_unsupported _, Ev_out_unsupported _) => True
      | (Ev_out_failed,Ev_out_failed) => True
      | (Ev_out_returned d1, Ev_out_returned d2) => if data_eq_dec d1 d2 then True else False
      | (Ev_out_returned_debug _, Ev_out_returned_debug _) => True
      | (_,_) => False
      end.

  End EvalDriver.

  (* Evaluation functions: variant with a single world collection as input *)
  (* Note: those simply build a single WORLD constant environment by calling mkWorld *)
  (* XXX probably should be made obsolete with the eval driver, but
       used in ocaml and queryTests XXX *)
  Section EvalWorld.
    Definition eval_camp_rule_world (r:camp_rule) (world:list data) : option data :=
      eval_camp_rule r (mkWorld world).
    Definition eval_camp_rule_world_debug (debug:bool) (r:camp_rule) (world:list data) : string :=
      eval_camp_rule_debug debug r (mkWorld world).
    
    Definition eval_camp_world (q:camp) (world:list data) : option data :=
      eval_camp q (mkWorld world).
    Definition eval_camp_world_debug (debug:bool) (q:camp) (world:list data) : string :=
      eval_camp_debug debug q (mkWorld world).
    
    Definition eval_oql_world (q:oql) (world:list data) : option data :=
      eval_oql q (mkWorld world).
    
    Definition eval_lambda_nra_world (q:lambda_nra) (world:list data) : option data :=
      eval_lambda_nra q (mkWorld world).
    
    Definition eval_nra_world (q:nra) (world:list data) : option data :=
      eval_nra q (mkWorld world).
    
    Definition eval_nraenv_core_world (q:nraenv_core) (world:list data) : option data :=
      eval_nraenv_core q (mkWorld world).
    
    Definition eval_nraenv_world (q:nraenv) (world:list data) : option data :=
      eval_nraenv q (mkWorld world).
    
    Definition eval_nnrc_core_world (q:nnrc_core) (world:list data) : option data :=
      eval_nnrc_core q (mkWorld world).
    
    Definition eval_nnrc_world (q:nnrc) (world:list data) : option data :=
      eval_nnrc q (mkWorld world).
    
    Definition eval_nnrcmr_world (q:nnrcmr) (world:list data) : option data :=
      eval_nnrcmr q (mkDistWorld world). (* XXX Creates a distributed WORLD collection XXX *)
    
    Definition eval_cldmr_world (q:cldmr) (world:list data) : option data :=
      eval_cldmr q (mkWorld world).
    
    Definition eval_dnnrc_world (q:dnnrc) (world:list data) : option data :=
      eval_dnnrc q (mkDistWorld world).
    
    Definition eval_dnnrc_typed_world (q:dnnrc) (world:list data) : option data :=
      eval_dnnrc q (mkDistWorld world).
    
  End EvalWorld.

End CompEval.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
