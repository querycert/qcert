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

Require Import List String.

Require Import Utils ForeignRuntime.
Require Import RUtilOps.

Local Open Scope string_scope.

Section ForeigntoJava.

  (* data of this type is a java expression that constructs a json element *)
         
    Inductive java_json : Set
      := mk_java_json : string -> java_json.

    Definition from_java_json (obj:java_json)
      := match obj with
         | mk_java_json s => s
         end.

    Definition java_json_NULL : java_json
       := mk_java_json "JsonNull.INSTANCE".
 
     Definition mk_java_json_primitive (obj:string) : java_json
       := mk_java_json ("new JsonPrimitive(" ++ obj ++ ")").
     
     Definition mk_java_json_nat n : java_json
       := mk_java_json_primitive (Z_to_string10 n).
     
     Definition mk_java_json_bool (b:bool) : java_json
       := mk_java_json_primitive 
            (if b then "true" else "false").
     
     Definition mk_java_json_string quotel (s:string)
       := mk_java_json_primitive
            (bracketString quotel s quotel).    

      Class foreign_to_java {fruntime:foreign_runtime}: Type
      := mk_foreign_to_java {
             foreign_to_java_data
               (quotel:string) (fd:foreign_data_type) : java_json
             ; foreign_to_java_unary_op
             (indent:nat) (eol:string)
             (quotel:string) (fu:foreign_unary_op_type)
             (d:java_json) : java_json
         ; foreign_to_java_binary_op
             (indent:nat) (eol:string)
             (quotel:string) (fb:foreign_binary_op_type)
             (d1 d2:java_json) : java_json
           }.
      
End ForeigntoJava.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)