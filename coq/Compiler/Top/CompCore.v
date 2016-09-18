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
Module CompCore(runtime:CompilerRuntime).

  Require Import BasicRuntime NNRCMRRuntime.
  Require Import TDNRCInfer.
  
  (* HACK: mr_reduce_empty isn't a field of mr so it needs to be exposed *)
  Definition mr_reduce_empty := mr_reduce_empty.

  (* Access to type annotations *)
  Definition type_annotation {br:brand_relation} (A:Set): Set
    := TDNRCInfer.type_annotation A.

  Definition ta_base {br:brand_relation} (A:Set) (ta:type_annotation A)
    := TDNRCInfer.ta_base ta.
  Definition ta_inferred {br:brand_relation} (A:Set) (ta:type_annotation A)
    := TDNRCInfer.ta_inferred ta .
  Definition ta_required {br:brand_relation} (A:Set) (ta:type_annotation A)
    := TDNRCInfer.ta_required ta.
  
End CompCore.

(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
