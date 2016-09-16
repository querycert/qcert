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

  Require Import RuletoNRA PatterntoNRA PatterntoNRAEnv NRAtoNNRC NRAEnvtoNNRC.
  Require Import CompCore.
  Require Import TRewFunc.
  Require Import CompUtil.
  Require Import NNRCtoJavascript.

  Module CC := CompCore runtime.

  Require Import PatterntoNRAEnv RuletoNRAEnv OQLtoNRAEnv.
 
  Local Open Scope string_scope.

  (* Compilation functions *)

  Definition oql_to_nraenv (oql:oql_expr) : algenv := OQLtoNRAEnv.translate_oql_to_algenv oql.

  Definition rule_to_nraenv (r:rule) : algenv := RuletoNRAEnv.translate_rule_to_algenv r.

  Definition rule_to_nra (r:rule) : alg := alg_of_rule r.

  Definition pat_to_nraenv (p:pat) : algenv := PatterntoNRAEnv.translate_pat_to_algenv p.

  Definition pat_to_nra (p:pat) : alg := alg_of_pat p.

  Definition nraenv_optim (op: algenv) : algenv := TOptimEnvFunc.toptim_nraenv op.

  Definition nraenv_compiler (op: algenv) : nrc := CC.tcompile_nraenv_to_nnrc_typed_opt op.

  Definition nraenv_to_nnrc (op: algenv) : nrc := algenv_to_nnrc op init_vid init_venv.

  Definition nraenv_to_nra (op: algenv) : alg := alg_of_algenv op.

  Definition nra_to_nraenv (op: alg) : algenv := algenv_of_alg op.

  Definition nra_optim (op: alg) : alg :=
    let algenv_opt := (TOptimEnvFunc.toptim_nraenv (algenv_of_alg op)) in
    if is_nra_fun algenv_opt then
      deenv_alg algenv_opt
    else
      alg_of_algenv algenv_opt.

  Definition nra_to_nnrc (op: alg) : nrc := nra_to_nnrc op init_vid.

  Definition nnrc_optim (e: nrc) : nrc := trew e.

  (* Stats computation functions *)

  Definition stat_nnrc (e: nrc) : data :=
    drec
      (("nnrc_size", dnat (Z_of_nat (nrc_size e)))
         :: ("nnrc_optim_size", dnat (Z_of_nat (nrc_size (nnrc_optim e))))
         :: nil).

  Definition stat_body_nra (op:alg) : data :=
    drec
      (("nra_size", dnat (Z_of_nat (alg_size op)))
         :: ("nra_depth", dnat (Z_of_nat (alg_depth op)))
         :: ("nra_to_nnrc", stat_nnrc (nra_to_nnrc op))
         :: nil).

  Definition stat_nra (op:alg) : data :=
    drec
      (("nra_no_optim", stat_body_nra op)
         :: ("nra_optim", stat_body_nra (nra_optim op))
         :: nil).

  Definition stat_body_nraenv (op:algenv) : data :=
    drec
      (("nraenv_size", dnat (Z_of_nat (algenv_size op)))
         :: ("nraenv_depth", dnat (Z_of_nat (algenv_depth op)))
         :: ("nraenv_to_nnrc", stat_nnrc (nraenv_to_nnrc op))
         :: ("nraenv_to_nra", stat_nra (nraenv_to_nra op))
         :: nil).

  Definition stat_nraenv (op:algenv) : data :=
    drec
      (("nraenv_no_optim", stat_body_nraenv op)
         :: ("nraenv_optim", stat_body_nraenv (nraenv_optim op))
         :: ("nraenv_compiler", stat_nnrc (nraenv_compiler op))
         :: nil).

  Definition stat_pat (p:pat) : data :=
    drec
      (("pat_size", dnat (Z_of_nat (pat_size p)))
         :: ("pat_to_nraenv", stat_nraenv (pat_to_nraenv p))
         :: ("pat_to_nra", stat_nra (pat_to_nra p))
         :: nil).

  Definition stat_rule (r:rule) : data :=
    drec
      (("rule_size", dnat (Z_of_nat (pat_size (rule_to_pattern r))))
         :: ("rule_to_nraenv", stat_nraenv (rule_to_nraenv r))
         :: ("rule_to_nra", stat_nra (rule_to_nra r))
         :: nil).

  Definition stat_oql (e:oql_expr) : data :=
    drec
      (("oql_size", dnat (Z_of_nat (oql_size e)))
         :: ("oql_to_nraenv", stat_nraenv (oql_to_nraenv e))
         :: nil).


  (* Top level *)

  Definition json_stats_oql (sname:string) (oql:oql_expr) : string :=
    let stat :=
        drec
          (("oql_name", dstring sname)
             :: ("oql_stat", stat_oql oql)
             :: nil)
    in
    dataToJS quotel_double stat.

  Definition json_stats_rule (sname:string) (r:rule) : string :=
    let stat :=
        drec
          (("rule_name", dstring sname)
             :: ("rule_stat", stat_rule r)
             :: nil)
    in
    dataToJS quotel_double stat.

  Definition json_stats_pattern (sname:string) (p:pat) : string :=
    let stat :=
        drec
          (("pat_name", dstring sname)
             :: ("pat_stat", stat_pat p)
             :: nil)
    in
    dataToJS quotel_double stat.


End CompStat.

(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
