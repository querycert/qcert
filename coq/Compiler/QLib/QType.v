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

Require Import CompilerRuntime Types.

Module QType(runtime:CompilerRuntime).
  Require RType String.

  Definition empty_brand_model (x:unit) := TBrandModel.empty_brand_model.

  Definition record_kind : Set
    := RType.record_kind.

  Definition open_kind : record_kind
    := RType.Open.

  Definition closed_kind : record_kind
    := RType.Closed.

  Definition camp_type {m:brand_relation} : Set
    := RType.rtype.
  Definition t {m:brand_relation} : Set
    := camp_type.

  Definition sorted_pf_type {m:brand_relation} srl
      := RSort.is_list_sorted RBindings.ODT_lt_dec (@RAssoc.domain String.string camp_type srl) = true.

  Definition bottom {m:brand_relation} : camp_type
    := RType.Bottom.  
  Definition top {m:brand_relation} : camp_type
    := RType.Top.
  Definition unit {m:brand_relation} : camp_type
    := RType.Unit.
  Definition nat {m:brand_relation} : camp_type
    := RType.Nat.
  Definition bool {m:brand_relation} : camp_type
    := RType.Bool.
  Definition string {m:brand_relation} : camp_type
    := RType.String.
  Definition bag {m:brand_relation} : camp_type -> camp_type
    := RType.Coll.
  Definition record {m:brand_relation} : record_kind -> forall (r:list (String.string*camp_type)), sorted_pf_type r -> camp_type
    := RType.Rec.
  Definition either {m:brand_relation} : camp_type -> camp_type -> camp_type
    := RType.Either.
  Definition arrow {m:brand_relation} : camp_type -> camp_type -> camp_type
    := RType.Arrow.
  Definition brand {m:brand_relation} : list String.string -> camp_type
    := RType.Brand.

  (* Additional support for brand models extraction -- will have to be tested/consolidated *)
  Require Import TypingRuntime.

  Definition brand_model : Set := brand_model.
  Definition make_brand_model := make_brand_model_fails.
  Definition typing_runtime : Set := typing_runtime.

  (* Additional support for json to rtype conversion *)
  Require Import JSONtoData.
  
  Definition json_to_rtype {m:brand_relation} := json_to_rtype.  

  Definition json_to_rtype_with_fail {m:brand_relation} := json_to_rtype_with_fail.

  (* JSON -> sdata string *)
  Require SparkData.
  Require RData.
  Require TOpsInfer.

  Definition camp_type_uncoll (m:brand_model) : camp_type -> option camp_type
    := @TOpsInfer.tuncoll _ m.
  
  Definition data_to_sjson (m:brand_model) : data -> camp_type -> option String.string
    := @SparkData.data_to_sjson _ _ _ m.

End QType.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
