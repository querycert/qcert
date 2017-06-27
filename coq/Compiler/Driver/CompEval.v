(*
 * COPYRight 2015-2016 IBM Corporation
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
  Require Import CldMRRuntime. (* XXX contains cld_load_init_env! XXX *)
  Require Import DNNRCRuntime.
  Require Import tDNNRCRuntime.
  Require Import CAMPRuntime.
  (** Target languages *)
  Require Import JavaScriptRuntime.
  Require Import JavaRuntime.
  Require Import SparkRDDRuntime.
  Require Import SparkDFRuntime.
  Require Import CloudantRuntime.

  (* Translations *)
  Require Import SQLtoNRAEnv.       (* Used for SQL evaluation *)
  Require Import LambdaNRAtoNRAEnv. (* Used for lambda_nra evaluation *)
  Require Import NNRCtoNNRCMR.      (* XXX contains load_init_env! XXX *)

  (* Foreign Support *)
  Require Import ForeignToReduceOps.
  Require Import ForeignToSpark.
  Require Import ForeignCloudant ForeignToCloudant.
  
  (* Compiler Driver *)
  Require Import CompLang CompEnv.

  (* Data *)
  Require Import RData.
  
  (* Some useful notations *)
  Local Open Scope list_scope.

  (* Context *)
  
  Context {fruntime:foreign_runtime}.   (* Necessary for everything, including data *)
  Context {fredop:foreign_reduce_op}.   (* Necessary for NNRCMR evaluation *)
  Context {fcloudant:foreign_cloudant}. (* Necessary for CldMR evaluation *)
  Context {ft:foreign_type}.            (* Necessary for DNNRC evaluation *)
  Context {bm:brand_model}.             (* Necessary for DNNRC evaluation *)

  Context {h:list(string*string)}.

  (* Evaluation functions *)
  Section EvalFunctions.

    (* Note: this is top-level so cenv is always first 'normalized' by calling rec_sort *)
    
    (* Language: camp_rule *)
    (* Note: eval for camp_rule relies on translation to camp *)
    Definition eval_camp_rule (q:camp_rule) (cenv: bindings) : option data :=
      camp_rule_eval_top h q cenv.

    Definition eval_camp_rule_debug (debug:bool) (q:camp_rule) (cenv: bindings) : string :=
      camp_rule_eval_top_debug h debug q cenv.

    (* Language: camp *)
    Definition eval_camp (q:camp) (cenv: bindings) : option data :=
      camp_eval_top h q cenv.

    Definition eval_camp_debug (debug:bool) (q:camp) (cenv: bindings) : string :=
      camp_eval_top_debug h debug q cenv.

    (* Language: oql *)
    Definition eval_oql (q:oql) (cenv: bindings) : option data
      := oql_eval_top h q cenv.

    (* Language: sql *)
    (* Note: eval for sql relies on translation to nraenv_core *)
    Definition eval_sql (q:sql) (cenv: bindings) : option data
      := nraenv_eval_top h (sql_to_nraenv_top q) cenv.
    (* Language: lambda_nra *)
    Definition eval_lambda_nra (q:lambda_nra) (cenv: bindings) : option data
      := lambda_nra_eval_top h q cenv.

    (* Language: nra *)
    Definition eval_nra (q:nra) (cenv: bindings) : option data
      := nra_eval_top h q cenv.
      (* XXX Passing just cenv as ID value is more natural, but not
             consistent with nraenv_core to nra translation which encodes
             ID and ENV in a records using the nra_context_data macro XXX *)

    (* Language: nraenv_core *)
    Definition eval_nraenv_core (q:nraenv_core) (cenv: bindings) : option data
      := nraenv_core_eval_top h q cenv.

    (* Language: nraenv *)
    Definition eval_nraenv (q:nraenv) (cenv: bindings) : option data
      := nraenv_eval_top h q cenv.

    (* Language: nnrc_core *)
    Definition eval_nnrc_core (q:nnrc_core) (cenv: bindings) : option data
      := nnrc_core_eval_top h q cenv.

    (* Language: nnrc *)
    Definition eval_nnrc (q:nnrc) (cenv: bindings) : option data
      := nnrc_eval_top h q cenv.

    (* Language: nnrcmr *)
    Definition eval_nnrcmr (q:nnrcmr) (cenv: bindings) : option data
      := let cenv := rec_sort cenv in
         (* Note: localize_bindings turns all variables distributed! *)
         let loc_cenv := mkDistLocs cenv in
         match load_init_env init_vinit loc_cenv cenv with
         | Some mr_env => nnrcmr_eval h mr_env q
         | None => None
         end.

    (* Language: cldmr *)
    Definition eval_cldmr (q:cldmr) (cenv: bindings) : option data
      := cldmr_eval_top h init_vinit q cenv.

    (* Language: dnnrc *)
    (* WARNING: This doesn't work if using the Dataset part of the language *)

    Definition eval_dnnrc
               (q:dnnrc) (cenv: bindings) : option data :=
      let cenv := rec_sort cenv in
      let loc_cenv := mkDistLocs (rec_sort cenv) in
      match mkDistConstants loc_cenv cenv with
      | Some cenv => lift localize_data (@dnnrc_eval _ _ _ h cenv SparkIRPlug nil q)
      | None => None
      end.

    (* Language: dnnrc_typed *)

    Definition eval_dnnrc_typed
               (q:dnnrc_typed) (cenv: bindings) : option data :=
      let cenv := rec_sort cenv in
      let loc_cenv := mkDistLocs (rec_sort cenv) in
      match mkDistConstants loc_cenv cenv with
      | Some cenv => lift localize_data (@dnnrc_eval _ _ _ h cenv SparkIRPlug nil q)
      | None => None
      end.

  End EvalFunctions.

  Section EvalDriver.
    Definition eval_input : Set := list (string*ddata).

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
      let cenv := lift_input ev_in in
      match q with
      | Q_camp_rule q => lift_output (eval_camp_rule q cenv)
      | Q_tech_rule _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_designer_rule _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_camp q => lift_output (eval_camp q cenv)
      | Q_oql q => lift_output (eval_oql q cenv)
      | Q_sql q => lift_output (eval_sql q cenv)
      | Q_lambda_nra q => lift_output (eval_lambda_nra q cenv)
      | Q_nra q => lift_output (eval_nra q cenv)
      | Q_nraenv_core q => lift_output (eval_nraenv_core q cenv)
      | Q_nraenv q => lift_output (eval_nraenv q cenv)
      | Q_nnrc_core q => lift_output (eval_nnrc_core q cenv)
      | Q_nnrc q => lift_output (eval_nnrc q cenv)
      | Q_nnrcmr q => lift_output (eval_nnrcmr q cenv)
      | Q_cldmr q => lift_output (eval_cldmr q cenv)
      | Q_dnnrc q => lift_output (eval_dnnrc q cenv)
      | Q_dnnrc_typed q => lift_output (eval_dnnrc_typed q cenv)
      | Q_javascript _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_java _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_spark_rdd _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_spark_df _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_cloudant _ => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      | Q_error err => Ev_out_unsupported ("No evaluation support for "++(name_of_language (language_of_query q)))
      end.

    Definition eval_query_debug (q:query) (ev_in:eval_input) : eval_output :=
      let cenv := lift_input ev_in in
      match q with
      | Q_camp_rule q => Ev_out_returned_debug (eval_camp_rule_debug true q cenv)
      | Q_tech_rule _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_designer_rule _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_camp q => Ev_out_returned_debug (eval_camp_debug true q cenv)
      | Q_oql _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
      | Q_sql _ => Ev_out_unsupported ("No debug evaluation support for "++(name_of_language (language_of_query q)))
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
    
    Definition eval_sql_world (q:sql) (world:list data) : option data :=
      eval_sql q (mkWorld world).
    
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
      eval_nnrcmr q (mkWorld world).
    
    Definition eval_cldmr_world (q:cldmr) (world:list data) : option data :=
      eval_cldmr q (mkWorld world).
    
    Definition eval_dnnrc_world (q:dnnrc) (world:list data) : option data :=
      eval_dnnrc q (mkWorld world).
    
    Definition eval_dnnrc_typed_world (q:dnnrc) (world:list data) : option data :=
      eval_dnnrc q (mkWorld world).
    
  End EvalWorld.

End CompEval.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
