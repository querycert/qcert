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

  Require Import NNRCtoJavascript.

  Require Import CompEnv.
  Require CompDriver.

  Module CD := CompDriver.CompDriver runtime.

  Local Open Scope string_scope.

  (* Stats computation functions *)

  Definition stat_nnrc (e: CD.nnrc) : data :=
    drec
      (("nnrc_size", dnat (Z_of_nat (nrc_size e)))
         :: ("nnrc_optim_size", dnat (Z_of_nat (nrc_size (CD.nnrc_optim e))))
         :: nil).

  Definition stat_body_nra (op:CD.nra) : data :=
    drec
      (("nra_size", dnat (Z_of_nat (alg_size op)))
         :: ("nra_depth", dnat (Z_of_nat (alg_depth op)))
         :: ("nra_to_nnrc", stat_nnrc (CD.nra_to_nnrc op))
         :: nil).

  Definition stat_nra (op:CD.nra) : data :=
    drec
      (("nra_no_optim", stat_body_nra op)
         :: ("nra_optim", stat_body_nra (CD.nra_optim op))
         :: nil).

  Definition stat_body_nraenv (op:CD.nraenv) : data :=
    drec
      (("nraenv_size", dnat (Z_of_nat (algenv_size op)))
         :: ("nraenv_depth", dnat (Z_of_nat (algenv_depth op)))
         :: ("nraenv_to_nnrc", stat_nnrc (CD.nraenv_to_nnrc op))
         :: ("nraenv_to_nra", stat_nra (CD.nraenv_to_nra op))
         :: nil).

  Definition stat_nraenv (op:CD.nraenv) : data :=
    drec
      (("nraenv_no_optim", stat_body_nraenv op)
         :: ("nraenv_optim", stat_body_nraenv (CD.nraenv_optim op))
         :: ("nraenv_compiler", stat_nnrc (CD.nraenv_optim_to_nnrc op))
         :: nil).

  Definition stat_pat (p:CD.camp) : data :=
    drec
      (("pat_size", dnat (Z_of_nat (pat_size p)))
         :: ("pat_to_nraenv", stat_nraenv (CD.camp_to_nraenv p))
         :: ("pat_to_nra", stat_nra (CD.camp_to_nra p))
         :: nil).

  Definition stat_rule (r:CD.rule) : data :=
    drec
      (("rule_size", dnat (Z_of_nat (pat_size (CD.rule_to_camp r))))
         :: ("rule_to_nraenv", stat_nraenv (CD.rule_to_nraenv r))
         :: ("rule_to_nra", stat_nra (CD.rule_to_nra r))
         :: nil).

  Definition stat_oql (e:CD.oql) : data :=
    drec
      (("oql_size", dnat (Z_of_nat (oql_size e)))
         :: ("oql_to_nraenv", stat_nraenv (CD.oql_to_nraenv e))
         :: nil).


  (* Top level *)

  Definition json_stats_oql (sname:string) (oql:CD.oql) : string :=
    let stat :=
        drec
          (("oql_name", dstring sname)
             :: ("oql_stat", stat_oql oql)
             :: nil)
    in
    dataToJS quotel_double stat.

  Definition json_stats_rule (sname:string) (r:CD.rule) : string :=
    let stat :=
        drec
          (("rule_name", dstring sname)
             :: ("rule_stat", stat_rule r)
             :: nil)
    in
    dataToJS quotel_double stat.

  Definition json_stats_pattern (sname:string) (p:CD.camp) : string :=
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
