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


Require Import String.
Require Import NRARuntime.
Require Import NRAEnvRuntime.
Require Import NNRCRuntime.
Require Import NNRCMRRuntime.
Require Import CloudantMR.
Require Import DNNRC Dataset.
Require Import CAMPRuntime.
Require Import ODMGRuntime.

Require Import CompilerRuntime.
Module QStat(runtime:CompilerRuntime).

  Require Import BasicSystem.
  Require Import TypingRuntime.
  Require Import CompLang CompStat.

  Section QS.
    Context {bm:brand_model}.
    Context {ftyping: foreign_typing}.

  (* Stat: Top level *)

  Definition json_stat_of_query : query -> string := json_stat_of_query.
  Definition json_stat_tree_of_query : string -> query -> string := json_stat_tree_of_query.

  End QS.
End QStat.


(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
