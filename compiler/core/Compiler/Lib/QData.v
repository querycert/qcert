(*
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
Require Data.
Require JSON.
Require DataToEJson.
Require EJsonToJSON.
Require Import String.

Module QData(runtime:CompilerRuntime).
  
  Definition json : Set 
    := JSON.json.
  Definition qdata : Set 
    := Data.data.
  Definition t : Set 
    := qdata.
  
  Definition jnull : json
    := JSON.jnull.
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
    := Data.dunit.
  Definition dnat z : qdata 
    := Data.dnat z.
  Definition dfloat n : qdata 
    := Data.dfloat n.
  Definition dbool b : qdata 
    := Data.dbool b.
  Definition dstring s : qdata 
    := Data.dstring s.
  Definition dcoll dl : qdata 
    := Data.dcoll dl.
  Definition drec dl : qdata 
    := Data.drec dl.
  Definition dleft : qdata -> qdata 
    := Data.dleft.
  Definition dright : qdata -> qdata 
    := Data.dright.
  Definition dbrand b : qdata -> qdata 
    := Data.dbrand b.
  (* foreign data is supported via the model *)
  
  (** JSON -> data conversion *)
  (* Note: make sure to normalize input data *)

  Definition json_to_qdata br (j:JSON.json) : qdata
    := DataNorm.normalize_data br (DataToEJson.ejson_to_data (EJsonToJSON.json_to_ejson j)).

  (** data -> JSON *string* conversion *)
  Definition qdataStringify s : qdata -> String.string
    := (fun d => JSON.jsonStringify s (EJsonToJSON.ejson_to_json (DataToEJson.data_to_ejson d))).

  Definition jsonStringify s : JSON.json -> String.string 
    := JSON.jsonStringify s.

  Definition data_to_string : qdata -> String.string
    := qdataStringify EmitUtil.quotel_double.
  
  Definition ejson_to_string : EJson.ejson -> String.string
    := (fun j => EJson.ejsonStringify EmitUtil.quotel_double j).
  Definition cejson_to_string : EJson.cejson -> String.string
    := (fun j => EJson.cejsonStringify EmitUtil.quotel_double j).

  Definition json_to_string : JSON.json -> String.string
    := jsonStringify EmitUtil.quotel_double.

  Section dist.
    Import DData.
    Definition qddata : Set := DData.ddata.
    Definition dlocal : qdata -> qddata := DData.Dlocal.
    Definition ddistr (x:qdata) : option qddata :=
      match x with
      | Data.dcoll c => Some (DData.Ddistr c)
      | _ => None
      end.
  End dist.
End QData.

