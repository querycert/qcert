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

  Require Import PatterntoNRAEnv NRAtoNNRC NRAEnvtoNNRC.
  Require Import CompCore.
  Require Import TRewFunc.

  Module CC := CompCore runtime.

  Local Open Scope string_scope.

  Definition stat_rule_source (r:rule) : data :=
    dnat (Z_of_nat (pat_size (rule_to_pattern r))).

  Definition stat_pattern_source (p:pat) : data :=
    dnat (Z_of_nat (pat_size p)).

  Definition stat_oql_source (e:oql_expr) : data :=
    dnat (Z_of_nat (oql_size e)).

  Definition stat_algenv (op:algenv) : data :=
    let size := algenv_size op in
    let depth := algenv_depth op in
    drec
      (("size", dnat (Z_of_nat size))
         :: ("depth", dnat (Z_of_nat depth))
         :: nil).

  Definition stat_alg (op:alg) : data :=
    let size := alg_size op in
    let depth := alg_depth op in
    drec
      (("size", dnat (Z_of_nat size))
         :: ("depth", dnat (Z_of_nat depth))
         :: nil).

  Definition stat_nrc (e: nrc) : data :=
    let e_opt := trew e in
    drec
      (("size", dnat (Z_of_nat (nrc_size e)))
         :: ("size optim", dnat (Z_of_nat (nrc_size e_opt)))
         :: nil).

  Definition nra_optim (op: alg) : alg :=
    let algenv_opt := (CC.toptimize_algenv_typed_opt (algenv_of_alg op)) in
    if is_nra_fun algenv_opt then
      deenv_alg algenv_opt
    else
      alg_of_algenv algenv_opt.

  Definition full_stats (sname:string) (ssize:data) (nraenv_no_op:algenv) : data :=
    let vid := "vid" in
    let venv := "venv" in
    let nra_of_nraenv_no_op := alg_of_algenv nraenv_no_op in
    let nra_op_of_nraenv_no_op := nra_optim nra_of_nraenv_no_op in
    let nraenv_op := CC.toptimize_algenv_typed_opt nraenv_no_op in
    let nra_of_nraenv_op := alg_of_algenv nraenv_op in
    let nra_op_of_nraenv_op := nra_optim nra_of_nraenv_op in
    drec (("Source", dstring sname)
            :: ("Source Size", ssize)
            :: ("NRAEnv", stat_algenv nraenv_no_op)
            :: ("NRAEnv -> NNRC", stat_nrc (algenv_to_nnrc nraenv_no_op vid venv))
            :: ("NRAEnv -> NRA", stat_alg nra_of_nraenv_no_op)
            :: ("NRAEnv -> NRA -> NNRC", stat_nrc (nra_to_nnrc nra_of_nraenv_no_op vid))
            :: ("NRAEnv -> NRA optim", stat_alg nra_op_of_nraenv_no_op)
            :: ("NRAEnv -> NRA optim -> NNRC", stat_nrc (nra_to_nnrc nra_op_of_nraenv_no_op vid))
            :: ("NRAEnv -> NRAEnv optim", stat_algenv nraenv_op)
            :: ("NRAEnv -> NRAEnv optim -> NNRC", stat_nrc (algenv_to_nnrc nraenv_op vid venv))
            :: ("NRAEnv -> NRAEnv optim -> NRA", stat_alg nra_of_nraenv_op)
            :: ("NRAEnv -> NRAEnv optim -> NRA -> NNRC", stat_nrc (nra_to_nnrc nra_of_nraenv_op vid))
            :: ("NRAEnv -> NRAEnv optim -> NRA optim", stat_alg nra_op_of_nraenv_op)
            :: ("NRAEnv -> NRAEnv optim -> NRA optim -> NNRC", stat_nrc (nra_to_nnrc nra_op_of_nraenv_op vid))
            :: ("compiler", stat_nrc (CC.tcompile_nraenv_to_nnrc_typed_opt nraenv_no_op))
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
