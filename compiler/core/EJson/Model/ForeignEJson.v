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
Require Import CoqLibAdd.
Require Import JSON.

Section ForeignEJson.
  
  Class foreign_ejson (foreign_ejson_model : Set) : Type
    := mk_foreign_ejson {
           foreign_ejson_dec :> EqDec foreign_ejson_model eq
           ; foreign_ejson_normalized (a : foreign_ejson_model) : Prop
           ; foreign_ejson_normalize (a : foreign_ejson_model) : foreign_ejson_model
           ; foreign_ejson_normalize_normalizes (a : foreign_ejson_model) : foreign_ejson_normalized (foreign_ejson_normalize a)
           ; foreign_ejson_normalize_idempotent (a : foreign_ejson_model) : foreign_ejson_normalized a -> foreign_ejson_normalize a = a
           ; foreign_ejson_tostring :> ToString foreign_ejson_model
      }.

End ForeignEJson.
