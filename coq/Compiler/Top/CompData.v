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
Module CompData(runtime:CompilerRuntime).

  Require String RData JSON.
  Require NNRCtoJavascript.
  
  Definition data : Set 
    := RData.data.
  Definition t : Set 
    := data.
  
  Definition dunit : data 
    := RData.dunit.
  Definition dnat z : data 
    := RData.dnat z.
  Definition dbool b : data 
    := RData.dbool b.
  Definition dstring s : data 
    := RData.dstring s.
  Definition dcoll dl : data 
    := RData.dcoll dl.
  Definition drec dl : data 
    := RData.drec dl.
  Definition dleft : data -> data 
    := RData.dleft.
  Definition dright : data -> data 
    := RData.dright.
  Definition dbrand b : data -> data 
    := RData.dbrand b.
  (* foreign data is supported via the model *)
  
  (** JSON -> data conversion (META variant) *)
  Definition json_to_data br : data -> data 
    := JSON.json_to_data br.
  (** JSON -> data conversion (Enhanced variant) *)
  Definition json_enhanced_to_data br : data -> data 
    := JSON.json_enhanced_to_data br.
  (** data -> JSON *string* conversion *)
  Definition dataToJS s : data -> String.string 
    := NNRCtoJavascript.dataToJS s.
End CompData.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
