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
Require String.
Require RData.
Require JSON.
Require JSONtoData.
Require NNRCtoJavaScript.

Module QData(runtime:CompilerRuntime).
  
  Definition json : Set 
    := JSON.json.
  Definition qdata : Set 
    := RData.data.
  Definition t : Set 
    := qdata.
  
  Definition jnil : json
    := JSON.jnil.
  Definition jnumber z : json 
    := JSON.jnumber z.
  Definition jbool b : json 
    := JSON.jbool b.
  Definition jstring s : json
    := JSON.jstring s.
  Definition jarray jl : json
    := JSON.jarray jl.
  Definition jobject jl : json
    := JSON.jobject jl.

  Definition dunit : qdata 
    := RData.dunit.
  Definition dnat z : qdata 
    := RData.dnat z.
  Definition dbool b : qdata 
    := RData.dbool b.
  Definition dstring s : qdata 
    := RData.dstring s.
  Definition dcoll dl : qdata 
    := RData.dcoll dl.
  Definition drec dl : qdata 
    := RData.drec dl.
  Definition dleft : qdata -> qdata 
    := RData.dleft.
  Definition dright : qdata -> qdata 
    := RData.dright.
  Definition dbrand b : qdata -> qdata 
    := RData.dbrand b.
  (* foreign data is supported via the model *)
  
  (** JSON -> data conversion (META variant) *)
  Definition json_to_qdata br : JSON.json -> qdata 
    := JSONtoData.json_to_data br.
  (** JSON -> data conversion (Enhanced variant) *)
  Definition json_enhanced_to_qdata br : JSON.json -> qdata 
    := JSONtoData.json_enhanced_to_data br.
  (** data -> JSON *string* conversion *)
  Definition qdataToJS s : qdata -> String.string 
    := NNRCtoJavaScript.dataToJS s.

  Definition jsonToJS s : JSON.json -> String.string 
    := NNRCtoJavaScript.jsonToJS s.

  Section dist.
    Import DData.
    Definition qddata : Set := DData.ddata.
    Definition dlocal : qdata -> qddata := DData.Dlocal.
    Definition ddistr (x:qdata) : option qddata :=
      match x with
      | RData.dcoll c => Some (DData.Ddistr c)
      | _ => None
      end.
  End dist.
End QData.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
