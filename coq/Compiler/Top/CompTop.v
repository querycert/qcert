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
Module CompTop(runtime:CompilerRuntime).

  Require Import String List String EquivDec.
  
  Require Import BasicSystem.
  Require Import ForeignToJavascript.
  Require Import Pattern Rule.

  Require Import CompUtil CompFront CompBack.
  Module CF := CompFront runtime.
  Module CB := CompBack runtime.
  
  (***************
   * NRA Section *
   ***************)

  Require Import NRAEnvRuntime.

  Local Open Scope algenv_scope.

  Hint Constructors data_normalized.
  Definition optimizer : Type := algenv -> algenv.
  (* Algebraic optimizers *)

  Require Import ROptimEnvFunc.

  Definition optimizer_no_optim : optimizer := (fun op:algenv => op).
  Definition optimizer_untyped_opt : optimizer := ROptimEnvFunc.optim.

  (* Compiler from CAMP to NRA+Env *)
  
  Definition compile_pat_to_algenv (optim:optimizer) (p:pat) : algenv :=
    (* Produces the initial plan *)
    let op_init := CF.translate_pat_to_algenv p in
    (* Optimization pass over the initial plan *)
    let op_optim := optim op_init
    in op_optim.

  Definition compile_pat_to_algenv_no_optim := compile_pat_to_algenv optimizer_no_optim.
  Definition compile_pat_to_algenv_untyped_opt := compile_pat_to_algenv optimizer_untyped_opt.
  
  (* Compiler from Rules to NRA+Env *)
  
  Definition compile_rule_to_algenv (optim:optimizer) (r:rule) : algenv :=
    (* Produces the initial plan *)
    let op_init := CF.translate_rule_to_algenv r in
    (* Optimization pass over the initial plan *)
    let op_optim := optim op_init
    in op_optim.

  Definition compile_rule_to_algenv_no_optim := compile_rule_to_algenv optimizer_no_optim.
  Definition compile_rule_to_algenv_untyped_opt := compile_rule_to_algenv optimizer_untyped_opt.
  

  (********************
   * Calculus Section *
   ********************)

  Require Import NNRCRuntime NNRCMRRuntime.
  Require Import NRAEnvtoNNRC NRewFunc.
  Require Import NNRCtoNNRCMR NRewMR.

  (* Calculus rewriter *)

  Definition rewriter : Type := nrc -> nrc.

  Definition rewriter_no_rew : rewriter := (fun e:nrc => e).

  Definition rewriter_simpl_rew : rewriter := head_rew.

  (* Compiler from CAMP to NNRC *)
  
  Definition compile_pat_to_nnrc (optim:optimizer) (rew:rewriter) (p:pat) : nrc :=
    let op_optim := compile_pat_to_algenv optim p in
    let e_init := algenv_to_nnrc op_optim init_vid init_venv in
    let e_rew := rew e_init in
    e_rew.

  Definition compile_pat_to_nnrc_untyped_opt :=
    compile_pat_to_nnrc optimizer_untyped_opt rewriter_simpl_rew.

  (* Compiler from CAMP to NNRC *)
  
  Definition compile_rule_to_nnrc (optim:optimizer) (rew:rewriter) (r:rule) : nrc :=
    let op_optim := compile_rule_to_algenv optim r in
    let e_init := algenv_to_nnrc op_optim init_vid init_venv in
    let e_rew := rew e_init in
    e_rew.

  Definition compile_rule_to_nnrc_untyped_opt :=
    compile_rule_to_nnrc optimizer_untyped_opt rewriter_simpl_rew.

  (* Compiler from CAMP to JavaScript *)

  Require Import NNRCtoJavascript CloudantMRtoJavascript.
  Local Open Scope string_scope.

  
  (*****************
   * Typed Section *
   *****************)
  
  (* Typed Compiler from Rules to NRA+Env *)

  Require Import BasicTypes CAMPTypes NRAEnvTypes.
  Require Import TPatterntoNRAEnv.

  Definition tcompile_rule_to_algenv_none (r:rule) : algenv :=
    compile_rule_to_algenv optimizer_no_optim r.

  Require Import NNRCTypes.
  Require Import TNRAEnvtoNNRC.
  Require Import TOptimEnvFunc.
  
  Definition toptimizer_typed_opt : optimizer := TOptimEnvFunc.toptim.

  Definition tcompile_rule_to_algenv_topt (r:rule) : algenv :=
    compile_rule_to_algenv toptim r.

  (* Typed compilation from rules to NNRC *)

  (* Note: only the algebra rewrites leverage types, the NNRC rewrites
  (at this point) are operating on the untyped form *)
  
  Definition tcompile_rule_to_nnrc (optim:optimizer) (rew:rewriter) (r:rule) : nrc :=
    let op_optim := compile_rule_to_algenv optim r in
    let e_init := algenv_to_nnrc op_optim init_vid init_venv in
    let e_rew := rew e_init in
    e_rew.

  Definition tcompile_rule_to_nnrc_none (r:rule) : nrc :=
    tcompile_rule_to_nnrc optimizer_no_optim rewriter_no_rew r.

  Require Import TRewFunc.
  
  Definition tcompile_rule_to_nnrc_topt (r:rule) : nrc :=
    tcompile_rule_to_nnrc toptim trew r.

  (* Typed compilation from rules to DNNRC *)

  (* Note: only the algebra rewrites leverage types, the DNNRC rewrites
  (at this point) are operating on the untyped form *)

  Require Import DData NNRC DNNRC NNRCtoDNNRC.

  Definition tcompile_rule_to_dnrc (optim:optimizer) (rew:rewriter) (r:rule) : dnrc _ bool algenv :=
    let op_optim := compile_rule_to_algenv optim r in
    let e_init := algenv_to_nnrc op_optim init_vid init_venv in
    let e_rew := rew e_init in
    let de_init := @nrc_to_dnrc_algenv _ bool true mkDistLoc e_rew in
    de_init.

  Definition tcompile_rule_to_dnrc_none (r:rule) : dnrc _ bool algenv :=
    tcompile_rule_to_dnrc optimizer_no_optim rewriter_no_rew r.

  Definition tcompile_rule_to_dnrc_topt (r:rule) : dnrc _ bool algenv :=
    tcompile_rule_to_dnrc toptim trew r.

  (* Typed compilation from rules to NNRC + Map Reduce *)

  (* - For now the assumption is that all free vars in the original nrc
       expression are collections and will be distributed.
     - The free variables are obtained after nrc rewrites
     - one has to be careful to pass those free variables to the mr-optimizer *)
  
  Definition tcompile_rule_to_nnrcmr_chain_no_optim (r:rule) : list (var * dlocalization) * nrcmr :=
    let e_nrc := tcompile_rule_to_nnrc_topt r in
    let e_nrc_no_id := nrc_subst e_nrc init_vid (NRCConst dunit) in
    let e_rew := trew e_nrc_no_id in
    let e_rew_free_vars := nrc_free_vars e_rew in
    let env_variables :=
        ((init_vid, Vlocal)
           ::(init_vinit, Vlocal)
           ::(localize_names e_rew_free_vars))
    in
    let e_mr :=
        nnrc_to_nnrcmr_chain e_rew
                             init_vinit
                             env_variables
    in
    (env_variables, e_mr).

  Definition tcompile_rule_to_nnrcmr_chain (r:rule) : list (var * dlocalization) * nrcmr :=
    let (env_vars, e_mr) := tcompile_rule_to_nnrcmr_chain_no_optim r in
    let e_mr_optim := mr_optimize e_mr in
    (env_vars, e_mr_optim).


  (* Typed compilation from rules to NNRC + Map Reduce *)

  Require Import CloudantMR NNRCMRtoCloudant ForeignToCloudant.

  Definition tcompile_rule_to_cldmr_chain (h:list (string*string)) (r:rule) : cld_mrl :=
    let '(env_vars, e_mr) := tcompile_rule_to_nnrcmr_chain r in
    CB.nrcmr_to_cldmr_chain_with_prepare h env_vars e_mr.

  (* Typed compilation from rules to Javascript *)

  Definition tcompile_rule_to_js_caco (r:rule) : string :=
    let nnrc := tcompile_rule_to_nnrc_topt r in
    nrcToJSTop nnrc.

  (* Typed compilation from rules to Cloudant *NEW* *)

  Definition tcompile_rule_to_cloudant_caco (h:list (string*string)) (r:rule) (rulename:string) : (list (string*string) * (string * list string)) :=
    let mrl := tcompile_rule_to_cldmr_chain h r in
    mapReducePairstoCloudant h mrl rulename.

  (* To Spark *)

  Require Import NNRCMRtoSpark ForeignToSpark.

  (* Hard-coding the WORLD variable for now. Generalizing will require
     more work on the Spark code-generation side. *)
  
  Definition mrchain_to_spark_data_from_file_caco rulename (env_vars:list (var * dlocalization)) mrchain :=
    CB.mrchain_to_spark_code_gen_with_prepare rulename env_vars mrchain.

End CompTop.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
