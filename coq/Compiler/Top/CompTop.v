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

  Require Import CompUtil.
  Require Import CompDriver.

  Module CD := CompDriver runtime.

  Require Import NRAEnvRuntime.

  Local Open Scope algenv_scope.

  Hint Constructors data_normalized.
  
  Require PatterntoNRAEnv.
  Definition compile_pat_to_algenv (q:CD.camp) : CD.nraenv :=
    CD.nraenv_optim (CD.camp_to_nraenv q).

  (* Compiler from Rules to NRA+Env *)

  Require RuletoNRAEnv.
  Definition compile_rule_to_algenv (q:CD.rule) : CD.nraenv :=
    CD.nraenv_optim (CD.rule_to_nraenv q).


  (********************
   * Calculus Section *
   ********************)

  Require Import NNRCRuntime NNRCMRRuntime.
  Require Import NRAEnvtoNNRC NRewFunc.
  Require Import NNRCtoNNRCMR NRewMR.

  (* Compiler from CAMP to JavaScript *)

  Require Import NNRCtoJavascript CloudantMRtoJavascript.
  Local Open Scope string_scope.

  
  (*****************
   * Typed Section *
   *****************)
  
  (* Typed Compiler from Rules to NRA+Env *)

  Require Import BasicTypes CAMPTypes NRAEnvTypes.
  Require Import TPatterntoNRAEnv.

  Require Import NNRCTypes.
  Require Import TNRAEnvtoNNRC.
  Require Import TOptimEnvFunc.
  
  Definition tcompile_rule_to_algenv_topt (q:CD.rule) : CD.nraenv :=
    CD.rule_to_nraenv q.

  (* Typed compilation from rules to NNRC *)

  (* Note: only the algebra rewrites leverage types, the NNRC rewrites
  (at this point) are operating on the untyped form *)
  
  Require Import TRewFunc.
  
  Definition tcompile_rule_to_nnrc_topt (q:CD.rule) : CD.nnrc :=
    CD.nnrc_optim (CD.nraenv_to_nnrc (CD.rule_to_nraenv q)).

  (* Typed compilation from rules to DNNRC *)

  (* Note: only the algebra rewrites leverage types, the DNNRC rewrites
  (at this point) are operating on the untyped form *)

  Require Import DData NNRC DNNRC NNRCtoDNNRC.

  Definition tcompile_rule_to_dnrc_topt (q:CD.rule) : CD.dnnrc_dataset :=
    CD.nnrc_to_dnnrc_dataset (CD.nnrc_optim (CD.nraenv_to_nnrc (CD.rule_to_nraenv q))).

  (* Typed compilation from rules to NNRC + Map Reduce *)

  (* - For now the assumption is that all free vars in the original nrc
       expression are collections and will be distributed.
     - The free variables are obtained after nrc rewrites
     - one has to be careful to pass those free variables to the mr-optimizer *)
  
  Definition tcompile_rule_to_nnrcmr_chain_no_optim (q:CD.rule) : list (var * dlocalization) * CD.nnrcmr :=
    let e_nrc := tcompile_rule_to_nnrc_topt q in
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

  Definition tcompile_rule_to_nnrcmr_chain (q:CD.rule) : list (var * dlocalization) * CD.nnrcmr :=
    let (env_vars, e_mr) := tcompile_rule_to_nnrcmr_chain_no_optim q in
    let e_mr_optim := CD.nnrcmr_optim e_mr in
    (env_vars, e_mr_optim).


  (* Typed compilation from rules to NNRC + Map Reduce *)

  Require Import CloudantMR NNRCMRtoCloudant ForeignToCloudant.

  Definition tcompile_rule_to_cldmr_chain (h:list (string*string)) (q:CD.rule) : CD.cldmr :=
    let '(env_vars, e_mr) := tcompile_rule_to_nnrcmr_chain q in
    CD.nnrcmr_to_cldmr h e_mr.

  (* Typed compilation from rules to Javascript *)

  Definition tcompile_rule_to_js_caco (q:CD.rule) : string :=
    let nnrc := tcompile_rule_to_nnrc_topt q in
    nrcToJSTop nnrc.

End CompTop.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
