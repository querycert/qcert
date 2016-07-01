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
Module OQLTop(runtime:CompilerRuntime).

  Require Import String List String EquivDec.
  
  Require Import BasicSystem.
  Require Import OQL OQLtoNRAEnv.

  Require Import CompUtil CompFront CompCore CompBack.

  Module CF := CompFront runtime.
  Module CC := CompCore runtime.
  Module CB := CompBack runtime.

  (***************
   * NRA Section *
   ***************)

  Require Import NRAEnvRuntime.

  Local Open Scope algenv_scope.
  
  (* Compiler from OQL to NRA+Env *)
  
  Definition tcompile_oql_to_algenv_typed_opt (e:oql_expr) : algenv :=
    (* Produces the initial plan *)
    let op_init := CF.translate_oql_to_algenv e in
    (* Optimization pass over the initial plan *)
    let op_optim := CC.toptimize_algenv_typed_opt op_init
    in op_optim.


  (****************
   * NNRC Section *
   ****************)

  Require Import NNRCRuntime.

  (* Compiler from OQL to NNRC *)
  
  Definition tcompile_oql_to_nnrc_typed_opt (e:oql_expr) : nrc :=
    (* Produces the initial plan *)
    let op_init := CF.translate_oql_to_algenv e in
    (* Compile/Optimize to NNRC *)
    let e_rew := CC.tcompile_nraenv_to_nnrc_typed_opt op_init in
    e_rew.

  (* Typed compilation from rules to Javascript *)

  Require Import NNRCtoJavascript.
  
  Definition tcompile_oql_to_js_code_gen (e:oql_expr) : string :=
    let nnrc := tcompile_oql_to_nnrc_typed_opt e in
    CB.nrc_to_js_code_gen nnrc.


  (******************
   * NNRCMR Section *
   ******************)

  Require Import NNRCMRRuntime.

  (* Typed compilation from OQL to NNRC + Map Reduce *)

  (* - For now the assumption is that all free vars in the original nrc
       expression are collections and will be distributed.
     - The free variables are obtained after nrc rewrites
     - one has to be careful to pass those free variables to the mr-optimizer *)
  
  Definition tcompile_oql_to_nnrcmr_chain (e:oql_expr) : list (var * dlocalization) * nrcmr :=
    (* Produces the initial plan *)
    let op_init := CF.translate_oql_to_algenv e in
    (* Compile/Optimize to NNRCMR *)
    CC.tcompile_nraenv_to_nnrcmr_chain_typed_opt op_init.

  (*****************
   * CldMR Section *
   *****************)

  (* Typed compilation from OQL to Cloudant Map Reduce *)

  Require Import CloudantMR.

  Definition tcompile_oql_to_cldmr_chain (h:list (string*string)) (e:oql_expr) : cld_mrl :=
    (* Produces the initial plan *)
    let op_init := CF.translate_oql_to_algenv e in
    (* Compile/Optimize to NNRCMR *)
    let (env_vars, e_nrcmr) := CC.tcompile_nraenv_to_nnrcmr_chain_typed_opt op_init in
    (* Generate for Cloudant *)
    let e_cld_mr := CB.nrcmr_to_cldmr_chain_with_prepare h env_vars e_nrcmr in
    e_cld_mr.

  (* Typed compilation from OQL to Cloudant *NEW* *)

  Definition tcompile_oql_to_cloudant_code_gen (h:list (string*string)) (e:oql_expr) (rulename:string) : (list (string*string) * (string * list string)) :=
    (* Produces the initial plan *)
    let op_init := CF.translate_oql_to_algenv e in
    (* Compile/Optimize to NNRCMR *)
    let (env_vars, e_nrcmr) := CC.tcompile_nraenv_to_nnrcmr_chain_typed_opt op_init in
    (* Generate for Cloudant *)
    CB.nrcmr_to_cloudant_code_gen_with_prepare h env_vars e_nrcmr rulename.

End OQLTop.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
