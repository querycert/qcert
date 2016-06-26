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
Module CompFront(runtime:CompilerRuntime).

  Require Import String List String EquivDec.
  
  Require Import BasicRuntime.

  Require Import CompUtil.

  (* Translations from front-end languages to NRAEnv *)
  
  (****************
   * Rule Section *
   ****************)

  Require Import NRAEnvRuntime.
  Require Import Pattern Rule.

  Require Import PatterntoNRAEnv RuletoNRAEnv.

  Local Open Scope algenv_scope.

  (* Translation from Rule to CAMP *)
  
  Definition translate_rule_to_pat (r:rule) : pat :=
    (* Produces the initial camp *)
    rule_to_pattern r.

  (* Translation from CAMP to NRA+Env *)
  
  (* Java equivalent: CampToNra.convert *)
  Definition translate_pat_to_algenv (p:pat) : algenv :=
    (* Produces the initial plan *)
    ANAppEnv (algenv_of_pat p) (ANConst (drec nil)).

  (* Translation from Rules to NRA+Env *)
  
  Definition translate_rule_to_algenv (r:rule) : algenv :=
    (* Produces the initial plan *)
    ANAppEnv (algenv_of_rule r) (ANConst (drec nil)).


  (***************
   * OQL Section *
   ***************)

  Require Import OQL.
  Require Import OQLtoNRAEnv.

  Definition translate_oql_to_algenv (e:oql_expr) : algenv :=
    (* Produces the initial plan *)
    ANApp (algenv_of_oql e) (ANConst (drec nil)).


End CompFront.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
