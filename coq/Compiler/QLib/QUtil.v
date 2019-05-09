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

Require Import CommonRuntime.
Require Import CompilerRuntime.
Require Import NNRCMRRuntime.
Require Import tDNNRCRuntime.
Require Import ImpRuntime.
Require Import CompEnv.
Require Import Version.

Module QUtil(runtime:CompilerRuntime).

  (* mr_reduce_empty isn't a field of mr so it needs to be exposed *)
  Definition mr_reduce_empty := mr_reduce_empty.

  (* Access to type annotations *)
  Definition type_annotation {br:brand_relation} (A:Set): Set
    := tDNNRC.type_annotation A.

  Definition ta_base {br:brand_relation} (A:Set) (ta:type_annotation A)
    := tDNNRC.ta_base ta.
  Definition ta_inferred {br:brand_relation} (A:Set) (ta:type_annotation A)
    := tDNNRC.ta_inferred ta .
  Definition ta_required {br:brand_relation} (A:Set) (ta:type_annotation A)
    := tDNNRC.ta_required ta.

  (* Processing for input or output of queries *)
  Definition validate_lifted_success := validate_lifted_success.
  Definition validate_data := validate_data.

  Definition mkDistWorld env := mkDistWorld env.

  Definition qcert_version := qcert_version.

  Section results.
    Definition qerror {fdata:foreign_data} : Set := QResult.qerror.
    Definition qresult {fdata:foreign_data} (A:Set) : Set := QResult.qresult A.

    Definition qsuccess {fdata:foreign_data} (A:Set) : A -> qresult A := QResult.qsuccess.
    Definition qfailure {fdata:foreign_data} (A:Set) : qerror -> qresult A := QResult.qfailure.
  End results.

  Definition string_of_json_runtime_op := ImpJson.string_of_json_runtime_op.

End QUtil.

