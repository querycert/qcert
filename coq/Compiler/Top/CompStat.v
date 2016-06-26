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

Require Import List String ZArith.
Require Import Utils BasicRuntime.

Require Import NRARuntime.
Require Import NRAEnvRuntime.
Require Import NNRCRuntime.
Require Import CAMPRuntime.
Require Import ODMGRuntime.

Require Import CompilerRuntime.
Module CompStat(runtime:CompilerRuntime).

  Require Import PatterntoNRAEnv NRAtoNNRC.

    Definition stat_rule_source (r:rule) : Z :=
    (Z_of_nat (pat_size (rule_to_pattern r))).
  
    Definition stat_pattern_source (p:pat) : Z :=
    (Z_of_nat (pat_size p)).
  
    Definition stat_oql_source (e:oql_expr) : Z :=
      (Z_of_nat (oql_size e)).
  
  (* Naive *)

  Definition stat_algenv_no_optim (op:algenv) : Z * Z :=
    let algenv := op in
    (Z_of_nat (algenv_size algenv), Z_of_nat (algenv_depth algenv)).
  
  Definition stat_alg_no_optim (op:algenv) : Z * Z :=
    let alg := alg_of_algenv op in
    (Z_of_nat (alg_size alg), Z_of_nat (alg_depth alg)).
  
  Definition stat_nrc_no_optim (op:algenv) : Z :=
    let alg := alg_of_algenv op in
    Z_of_nat (nrc_size (nra_to_nnrc alg "id"%string)).

  (* Compiler *)

  Require Import CompCore.

  Module CC := CompCore runtime.

  Definition tstat_algenv_typed_opt (op:algenv) : Z * Z :=
    let algenv := CC.toptimize_algenv_typed_opt op in
    (Z_of_nat (algenv_size algenv), Z_of_nat (algenv_depth algenv)).

  Definition tstat_alg_typed_opt (op:algenv) : Z * Z :=
    let alg := alg_of_algenv (CC.toptimize_algenv_typed_opt op) in
    (Z_of_nat (alg_size alg), Z_of_nat (alg_depth alg)).

  Definition tstat_nrc_typed_opt (op:algenv) : Z :=
    Z_of_nat (nrc_size (CC.tcompile_nraenv_to_nnrc_typed_opt op)).

  Local Open Scope string_scope.

  Definition full_stats (sname:string) (ssize:Z) (op:algenv) : data :=
    let (st_algenv_no1, st_algenv_no2) := (stat_algenv_no_optim op) in 
    let (st_alg_no1, st_alg_no2) := (stat_alg_no_optim op) in 
    let (tst_algenv_no1, tst_algenv_no2) := (tstat_algenv_typed_opt op) in 
    let (tst_alg_no1, tst_alg_no2) := (tstat_alg_typed_opt op) in 
    drec (("Source", dstring sname)
            :: ("Source Size", dnat ssize)
            :: ("No Optim Size", drec (("NRAEnv", dnat st_algenv_no1)
                                         :: ("NRAEnv Depth", dnat st_algenv_no2)
                                         :: ("NRA",dnat st_alg_no1)
                                         :: ("NRA Depth", dnat st_alg_no2)
                                         :: ("NNRC",dnat (stat_nrc_no_optim op))
                                         :: nil))
            :: ("[TYPED] Optimized Size", drec (("NRAEnv", dnat tst_algenv_no1)
                                         :: ("NRAEnv Depth", dnat tst_algenv_no2)
                                         :: ("NRA",dnat tst_alg_no1)
                                         :: ("NRA Depth", dnat tst_alg_no2)
                                         :: ("NNRC",dnat (tstat_nrc_typed_opt op))
                                         :: nil))
            :: nil).


  (* Top level *)
  
  Require Import CompFront.
  Require Import NNRCtoJavascript.

  Module CF := CompFront runtime.
  
  Definition json_stats_oql (sname:string) (oql:oql_expr) : string :=
    let ssize := stat_oql_source oql in
    let op := CF.translate_oql_to_algenv oql in
    let stat := full_stats sname ssize op in
    dataToJS quotel_double stat.

  Definition json_stats_rule (sname:string) (r:rule) : string :=
    let ssize := stat_rule_source r in
    let op := CF.translate_rule_to_algenv r in
    let stat := full_stats sname ssize op in
    dataToJS quotel_double stat.

  Definition json_stats_pattern (sname:string) (p:pat) : string :=
    let ssize := stat_pattern_source p in
    let op := CF.translate_pat_to_algenv p in
    let stat := full_stats sname ssize op in
    dataToJS quotel_double stat.

End CompStat.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
