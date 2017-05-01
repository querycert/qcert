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

Local Open Scope string_scope.

Section ForeigntoJavaScript.

Class foreign_to_javascript {fruntime:foreign_runtime}: Type
  := mk_foreign_to_javascript {
         foreign_to_javascript_data
           (quotel:string) (fd:foreign_data_type) : string
         ; foreign_to_javascript_unary_op
             (indent:nat) (eol:string)
             (quotel:string) (fu:foreign_unary_op_type)
             (d:string) : string
         ; foreign_to_javascript_binary_op
             (indent:nat) (eol:string)
             (quotel:string) (fb:foreign_binary_op_type)
             (d1 d2:string) : string
       }.
  
  Section toJavascript.
    Require Import RData.
    Require Import JSON.
    Context {fdata:foreign_data}.
    Fixpoint data_enhanced_to_js (quotel:string) (d:data) : json :=
      match d with
      | dunit => jnil
      | dnat n => jnumber n
      | dbool b => jbool b
      | dstring s => jstring s
      | dcoll c => jarray (map (data_enhanced_to_js quotel) c)
      | drec r => jobject (map (fun x => (fst x, (data_enhanced_to_js quotel) (snd x))) r)
      | dleft d' => jobject (("left"%string, data_enhanced_to_js quotel d')::nil)
      | dright d' => jobject (("right"%string, data_enhanced_to_js quotel d')::nil)
      | dbrand b (drec r) => jobject (("$class "%string, jarray (map jstring b))::(map (fun x => (fst x, data_enhanced_to_js quotel (snd x))) r))
      | dbrand b d' => jobject (("$class"%string, jarray (map jstring b))::("$data"%string, (data_enhanced_to_js quotel d'))::nil)
      | dforeign fd => jforeign fd
      end.

    Fixpoint data_to_js (quotel:string) (d:data) : json :=
      match d with
      | dunit => jnil
      | dnat n => jnumber n
      | dbool b => jbool b
      | dstring s => jstring s
      | dcoll c => jarray (map (data_to_js quotel) c)
      | drec r => jobject (map (fun x => (fst x, (data_to_js quotel) (snd x))) r)
      | dleft d' => jobject (("left"%string, data_to_js quotel d')::nil)
      | dright d' => jobject (("right"%string, data_to_js quotel d')::nil)
      | dbrand b d' => jobject (("type"%string, jarray (map jstring b))::("data"%string, (data_to_js quotel d'))::nil)
      | dforeign fd => jforeign fd
      end.

  End toJavascript.

End ForeigntoJavaScript.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
