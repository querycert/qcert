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

Require Import CompilerRuntime.
Module QEval(runtime:CompilerRuntime).

  Require Import String List String EquivDec.
  
  Require Import BasicSystem.
  Require Import CompLang CompEval.

  Section QE.
  Context {h:list(string*string)}.

  (* Inputs to eval *)
  Definition constant_env : Set := list (string*data).
  Definition world_env : Set := list data.

  (* Eval for arbitrary (local) constant environments *)
  Definition eval_rule : rule -> constant_env -> option data := @eval_rule _ h.
  Definition eval_rule_debug : bool -> rule -> constant_env -> string := @eval_rule_debug _ h.
  
  Definition eval_camp : camp -> constant_env -> option data := @eval_camp _ h.
  Definition eval_camp_debug : bool -> camp -> constant_env -> string := @eval_camp_debug _ h.

  Definition eval_oql : oql -> constant_env -> option data := @eval_oql _ h.
  Definition eval_lambda_nra : lambda_nra -> constant_env -> option data := @eval_lambda_nra _ h.

  Definition eval_nra : nra -> constant_env -> option data := @eval_nra _ h.
  Definition eval_nraenv : nraenv -> constant_env -> option data := @eval_nraenv _ h.

  Definition eval_nnrc : nnrc -> constant_env -> option data := @eval_nnrc _ h.

  Definition eval_nnrcmr : nnrcmr -> constant_env -> option data := @eval_nnrcmr _ _ h.
  Definition eval_cldmr : cldmr -> constant_env -> option data := @eval_cldmr _ _ h.
  Definition eval_dnnrc_dataset {bm:brand_model} : dnnrc_dataset -> constant_env -> option data := @eval_dnnrc_dataset _ _ bm h.

  (* Eval for single 'world' collection *)
  Definition eval_rule_world : rule -> world_env -> option data := @eval_rule_world _ h.
  Definition eval_rule_world_debug : bool -> rule -> world_env -> string := @eval_rule_world_debug _ h.
  
  Definition eval_camp_world : camp -> world_env -> option data := @eval_camp_world _ h.
  Definition eval_camp_world_debug : bool -> camp -> world_env -> string := @eval_camp_world_debug _ h.

  Definition eval_oql_world : oql -> world_env -> option data := @eval_oql_world _ h.
  Definition eval_lambda_nra_world : lambda_nra -> world_env -> option data := @eval_lambda_nra_world _ h.

  Definition eval_nra_world : nra -> world_env -> option data := @eval_nra_world _ h.
  Definition eval_nraenv_world : nraenv -> world_env -> option data := @eval_nraenv_world _ h.

  Definition eval_nnrc_world : nnrc -> world_env -> option data := @eval_nnrc_world _ h.

  Definition eval_nnrcmr_world : nnrcmr -> world_env -> option data := @eval_nnrcmr_world _ _ h.
  Definition eval_cldmr_world : cldmr -> world_env -> option data := @eval_cldmr_world _ _ h.
  Definition eval_dnnrc_dataset_world {bm:brand_model} : dnnrc_dataset -> world_env -> option data := @eval_dnnrc_dataset_world _ _ bm h.

  (* Eval driver *)

  Definition eval_input : Set := eval_input.
  Definition eval_output : Set := eval_output.

  Definition eval_query {bm:brand_model} : query -> eval_input -> eval_output := @eval_query _ _ _ _ bm h.

  End QE.

End QEval.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
