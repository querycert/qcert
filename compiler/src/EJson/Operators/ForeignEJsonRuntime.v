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

Require Import EquivDec.
Require Import List.
Require Import Utils.
Require Import EJsonRuntime.

Section ForeignEJsonRuntime.
  Class foreign_ejson_runtime {fejson:foreign_ejson}
  : Type
    := mk_foreign_ejson_runtime {
           foreign_ejson_runtime_type : Set
           ; foreign_ejson_runtime_dec :> EqDec foreign_ejson_runtime_type eq
           ; foreign_ejson_runtime_tostring :> ToString foreign_ejson_runtime_type
           ; foreign_ejson_runtime_interp 
               (f:foreign_ejson_runtime_type)
               (dl:list ejson) : option ejson                                 
         }.

End ForeignEJsonRuntime.
