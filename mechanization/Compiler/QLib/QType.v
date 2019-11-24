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
Require Import Types.
Require RType.
Require String.
Require Import TypingRuntime.
Require Import DatatoJSON.
Require DatatoSparkDF.
Require Data.
Require TUtil.
Require Schema.

Module QType(runtime:CompilerRuntime).

  Definition empty_brand_model (x:unit) := TBrandModel.empty_brand_model.

  Definition record_kind : Set
    := RType.record_kind.

  Definition open_kind : record_kind
    := RType.Open.

  Definition closed_kind : record_kind
    := RType.Closed.

  Definition qtype_struct {m:brand_relation} : Set
    := RType.rtype₀.
  Definition qtype {m:brand_relation} : Set
    := RType.rtype.
  Definition t {m:brand_relation} : Set
    := qtype.

  Definition sorted_pf_type {m:brand_relation} srl
      := SortingAdd.is_list_sorted Bindings.ODT_lt_dec (@Assoc.domain String.string qtype srl) = true.

  Definition bottom {m:brand_relation} : qtype
    := RType.Bottom.  
  Definition top {m:brand_relation} : qtype
    := RType.Top.
  Definition unit {m:brand_relation} : qtype
    := RType.Unit.
  Definition nat {m:brand_relation} : qtype
    := RType.Nat.
  Definition bool {m:brand_relation} : qtype
    := RType.Bool.
  Definition string {m:brand_relation} : qtype
    := RType.String.
  Definition bag {m:brand_relation} : qtype -> qtype
    := RType.Coll.
  Definition record {m:brand_relation} : record_kind -> forall (r:list (String.string*qtype)), sorted_pf_type r -> qtype
    := RType.Rec.
  Definition either {m:brand_relation} : qtype -> qtype -> qtype
    := RType.Either.
  Definition arrow {m:brand_relation} : qtype -> qtype -> qtype
    := RType.Arrow.
  Definition brand {m:brand_relation} : list String.string -> qtype
    := RType.Brand.

  (* Additional support for json to rtype conversion *)
  
  Definition json_to_rtype {m:brand_relation} := json_to_rtype.  

  Definition json_to_rtype_with_fail {m:brand_relation} := json_to_rtype_with_fail.

  (* Additional support for distributed types *)
  
  Definition qcert_dtype {m:brand_relation} : Set
    := DType.drtype.
  Definition dt {m:brand_relation} : Set
    := qcert_dtype.

  Definition json_to_drtype {m:brand_relation} : JSON.json -> qcert_dtype := json_to_drtype.

  Definition json_to_vrtype_with_fail {m:brand_relation} : JSON.json -> option (String.string * qtype) := json_to_vrtype_with_fail.

  Definition tlocal {m:brand_relation}  : qtype -> qcert_dtype := DType.Tlocal.
  Definition tdistr {m:brand_relation}  : qtype -> qcert_dtype := DType.Tdistr.

  (* JSON -> sdata string *)

  Definition qtype_uncoll (m:brand_model) : qtype -> option qtype
    := @TUtil.tuncoll _ m.
  
  Definition data_to_sjson (m:brand_model) : data -> qtype -> option String.string
    := @DatatoSparkDF.data_to_sjson _ _ m.

  (* Additional support for brand models extraction -- will have to be tested/consolidated *)

  Definition brand_relation : Set := brand_relation.
  Definition make_brand_relation := Schema.mk_brand_relation.
  Definition brand_model : Set := brand_model.
  Definition make_brand_model := Schema.make_brand_model_from_decls_fails.
  Definition typing_runtime : Set := typing_runtime.

End QType.

