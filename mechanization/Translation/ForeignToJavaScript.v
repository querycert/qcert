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

Require Import List.
Require Import String.
Require Import Utils.
Require Import ForeignRuntime.

Local Open Scope string_scope.

Section ForeigntoJavaScript.

Class foreign_to_javascript {fruntime:foreign_runtime}: Type
  := mk_foreign_to_javascript {
         foreign_to_javascript_unary_op
           (indent:nat) (eol:string)
           (quotel:string) (fu:foreign_unary_op_type)
           (d:string) : string
         ; foreign_to_javascript_binary_op
             (indent:nat) (eol:string)
             (quotel:string) (fb:foreign_binary_op_type)
             (d1 d2:string) : string
       }.
End ForeigntoJavaScript.

