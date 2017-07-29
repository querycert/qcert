(*
 * Copyright 2015-2017 IBM Corporation.  Portions Copyright 2017 Joshua Auerbach.
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

Section SQLPPtoNRAEnv.
  Require Import String.
  Require Import ZArith.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import BasicSystem.
  Require Import RDataSort. (* For SortCriterias *)
  Require Import SQLPP.
  Require Import NRAEnvRuntime.

  Context {fruntime:foreign_runtime}.

  Definition sqlpp_to_nraenv_top (q:sqlpp) : nraenv
    := NRAEnvConst dunit.    (* Temporary placeholder *)

End SQLPPtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
