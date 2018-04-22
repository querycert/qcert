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

Require Import List.
Require Import String.
Require Import Utils.
Require Import ForeignRuntime.
Require Import JavaScriptAstRuntime.

Local Open Scope string_scope.

Section ForeigntoJavaScriptAst.

Class foreign_to_ajavascript {fruntime:foreign_runtime}: Type
  := mk_foreign_to_ajavascript {
         foreign_to_ajavascript_unary_op
           (fu:foreign_unary_op_type)
           (e:expr) : expr
         ; foreign_to_ajavascript_binary_op
             (fb:foreign_binary_op_type)
             (e1 e2:expr) : expr
       }.
End ForeigntoJavaScriptAst.

