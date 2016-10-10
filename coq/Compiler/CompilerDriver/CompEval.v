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

Section CompEval.

  Require Import String.

  (* Basic *)
  Require Import BasicSystem.
  Require Import TypingRuntime.

  (* ASTs *)
  Require Import ODMGRuntime.
  Require Import LambdaAlg.
  Require Import CAMPRuntime.
  Require Import NRARuntime.
  Require Import NRAEnvRuntime.
  Require Import NNRCRuntime.
  Require Import NNRCMRRuntime.
  Require Import CloudantMR. (* XXX contains cld_load_init_env! XXX *)
  Require Import DNNRC Dataset.

  (* Translations *)
  Require Import LambdaAlgtoNRAEnv. (* Used for lambda_nra evaluation *)
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
    
    (* Language: rule *)
    (* Note: eval for rule relies on translation to camp *)
    Definition eval_rule (q:rule) (cenv: list (string*data)) : option data :=
      match interp h (rec_sort cenv) (rule_to_pattern q) nil dunit with
      | Success l => Some (dcoll (l::nil))
      | RecoverableError => Some (dcoll nil)
      | TerminalError => None
      end.

    Definition eval_rule_debug (debug:bool) (q:rule) (cenv: list (string*data)) : string
      := let pp := rule_to_pattern q in
         print_presult_debug pp
                             (interp_debug h
                                           (rec_sort cenv)
                                           debug nil pp nil dunit).

    (* Language: camp *)
    Definition eval_camp (q:camp) (cenv: list (string*data)) : option data
      := match interp h (rec_sort cenv) q nil dunit with
         | Success l => Some (dcoll (l::nil))
         | RecoverableError => Some (dcoll nil)
         | TerminalError => None
         end.

    Definition eval_camp_debug (debug:bool) (q:camp) (cenv: list (string*data)) : string
      := print_presult_debug q
                             (interp_debug h
                                           (rec_sort cenv)
                                           debug nil q nil dunit).

    (* Language: oql *)
    Definition eval_oql (q:oql) (cenv: list (string*data)) : option data
      := oql_interp h (rec_sort cenv) q nil.

    (* Language: lambda_nra *)
    (* Note: eval for lambda_nra relies on translation to nraenv *)
    Definition eval_lambda_nra (q:lambda_nra) (cenv: list (string*data)) : option data
      := fun_of_algenv h (rec_sort cenv) (algenv_of_lalg q) (drec nil) dunit.

    (* Language: nra *)
    Definition eval_nra (q:nra) (cenv: list (string*data)) : option data
      := fun_of_alg h q (drec (rec_sort cenv)).
      (* XXX Passing just cenv as ID value is more natural, but not
             consistent with nraenv to nra translation which encodes
             ID and ENV in a records using the pat_context_data macro XXX *)

    (* Language: nraenv *)
    Definition eval_nraenv (q:nraenv) (cenv: list (string*data)) : option data
      := fun_of_algenv h (rec_sort cenv) q (drec nil) dunit.

    (* Language: nnrc *)
    (* Note: eval_nnrc assumes constant environment has been prefixed with 'CONST$' *)
    Definition eval_nnrc (q:nnrc) (cenv: list (string*data)) : option data
      := nrc_eval h (mkConstants (rec_sort cenv)) q.

    (* Language: nnrcmr *)
    (* Note: eval_nnrcmr assumes constant environment has been prefixed with 'CONST$' *)
    Definition eval_nnrcmr (q:nnrcmr) (cenv: list (string*data)) : option data
      := let cenv := mkConstants (rec_sort cenv) in
         (* Note: localize_bindings turns all variables distributed! *)
         let loc_cenv := mkDistLocs cenv in
         match load_init_env init_vinit loc_cenv cenv with
         | Some mr_env => nrcmr_eval h mr_env q
         | None => None
         end.

    (* Language: cldmr *)
    (* Note: eval_cldmr assumes constant environment has been prefixed with 'CONST$' *)
    Definition eval_cldmr (q:cldmr) (cenv: list (string*data)) : option data
      := let cenv := mkConstants (rec_sort cenv) in
         match cld_load_init_env init_vinit cenv with
         | Some cenv => cld_mrl_eval h cenv q
         | None => None
         end.

    (* Language: dnnrc_dataset *)
    (* WARNING: This doesn't work if using the Dataset part of the langauge *)

    Definition eval_dnnrc_dataset
               (q:dnnrc_dataset) (cenv: list (string*data)) : option data :=
      let cenv := mkConstants (rec_sort cenv) in
      let loc_cenv := mkDistLocs (rec_sort cenv) in
      match mkDistConstants loc_cenv cenv with
      | Some cenv => lift localize_data (@dnrc_eval _ _ _ h SparkIRPlug cenv q)
      | None => None
      end.

    (* Evaluation functions: variant with a single world collection as input *)
    (* Note: those simply build a single WORLD constant environment by calling mkWorld *)
    (* XXX probably should be made obsolete with the eval driver, but
           used in ocaml and queryTests XXX *)
    Section EvalWorld.
      Definition eval_rule_world (r:rule) (world:list data) : option data :=
        eval_rule r (mkWorld world).
      Definition eval_rule_world_debug (debug:bool) (r:rule) (world:list data) : string :=
        eval_rule_debug debug r (mkWorld world).

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

      Definition eval_nraenv_world (q:nraenv) (world:list data) : option data :=
        eval_nraenv q (mkWorld world).

      Definition eval_nnrc_world (q:nnrc) (world:list data) : option data :=
        eval_nnrc q (mkWorld world).

      Definition eval_nnrcmr_world (q:nnrcmr) (world:list data) : option data :=
        eval_nnrcmr q (mkWorld world).

      Definition eval_cldmr_world (q:cldmr) (world:list data) : option data :=
        eval_cldmr q (mkWorld world).

      Definition eval_dnnrc_dataset_world (q:dnnrc_dataset) (world:list data) : option data :=
        eval_dnnrc_dataset q (mkWorld world).

    End EvalWorld.
    
  End EvalFunctions.

  Section EvalQuery.
    Inductive eval_input : Set :=
    | Ev_in_world : list data -> eval_input
    | Ev_in_constant_env : list (string*data) -> eval_input
    .

    Definition lift_input (ev_in:eval_input) : list (string*data) :=
      match ev_in with
      | Ev_in_world world => mkWorld world
      | Ev_in_constant_env cenv => cenv
      end.
    
    Inductive eval_output : Set :=
    | Ev_out_unsupported : eval_output
    | Ev_out_failed : eval_output
    | Ev_out_returned : data -> eval_output
    .

    Definition lift_output (result:option data) :=
      match result with
      | None => Ev_out_failed
      | Some d => Ev_out_returned d
      end.
    
    Definition eval_query (q:query) (ev_in:eval_input) : eval_output :=
      let cenv := lift_input ev_in in
      match q with
      | Q_rule q => lift_output (eval_rule q cenv)
      | Q_camp q => lift_output (eval_camp q cenv)
      | Q_oql q => lift_output (eval_oql q cenv)
      | Q_lambda_nra q => lift_output (eval_lambda_nra q cenv)
      | Q_nra q => lift_output (eval_nra q cenv)
      | Q_nraenv q => lift_output (eval_nraenv q cenv)
      | Q_nnrc q => lift_output (eval_nnrc q cenv)
      | Q_nnrcmr q => lift_output (eval_nnrcmr q cenv)
      | Q_cldmr q => lift_output (eval_cldmr q cenv)
      | Q_dnnrc_dataset _ => Ev_out_unsupported
      | Q_dnnrc_typed_dataset _ => Ev_out_unsupported
      | Q_javascript _ => Ev_out_unsupported
      | Q_java _ => Ev_out_unsupported
      | Q_spark _ => Ev_out_unsupported
      | Q_spark2 _ => Ev_out_unsupported
      | Q_cloudant _ => Ev_out_unsupported
      | Q_error err => Ev_out_unsupported
      end.
  End EvalQuery.

End CompEval.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
