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

Require Import EquivDec.
Require Import CoqLibAdd.

Section ForeignData.
  
  Class foreign_data : Type
    := mk_foreign_data {
           foreign_data_type : Set
(* TODO: #35 is needed before we can generalize this
  ; foreign_data_equiv (a b : foreign_data_type) : Prop
  ; foreign_data_equiv_equiv :> Equivalence foreign_data_equiv
 *) 
           ; foreign_data_dec :> EqDec foreign_data_type eq
           ; foreign_data_normalized (a : foreign_data_type) : Prop
           ; foreign_data_normalize (a : foreign_data_type) : foreign_data_type
           ; foreign_data_normalize_normalizes (a : foreign_data_type) : foreign_data_normalized (foreign_data_normalize a)
           ; foreign_data_normalize_idempotent (a : foreign_data_type) : foreign_data_normalized a -> foreign_data_normalize a = a
           ; foreign_data_tostring :> ToString foreign_data_type
      }.

End ForeignData.

