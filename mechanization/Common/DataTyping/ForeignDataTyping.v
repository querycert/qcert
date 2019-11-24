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

Require Import Utils.
Require Import ForeignData.
Require Import CommonData.
Require Import Types.

Section ForeignDataTyping.
  
  Class foreign_data_typing
        {fdata:foreign_data}
        {ftype:foreign_type} 
    : Type
    := mk_foreign_data_typing {
           foreign_data_typing_has_type
             (d:foreign_data_type)
             (τ:foreign_type_type) : Prop
           ; foreign_data_typing_normalized 
               {d:foreign_data_type}
               {τ:foreign_type_type} :
               foreign_data_typing_has_type d τ ->
               foreign_data_normalized d
           ; foreign_data_typing_subtype
               {d:foreign_data_type}
               {τ₁ τ₂:foreign_type_type} :
               foreign_data_typing_has_type d τ₁ ->
               τ₁ ≤ τ₂ ->
               foreign_data_typing_has_type d τ₂
           ; foreign_data_typing_meet 
               {d:foreign_data_type}
               {τ₁ τ₂:foreign_type_type} :
               foreign_data_typing_has_type d τ₁ ->
               foreign_data_typing_has_type d τ₂ ->
               foreign_data_typing_has_type d (τ₁ ⊓ τ₂)
           ; foreign_data_typing_infer (d:foreign_data_type)
             : option foreign_type_type
           ; foreign_data_typing_infer_normalized {d} :
               foreign_data_normalized d ->
               {τ | foreign_data_typing_infer d = Some τ}
           ; foreign_data_typing_infer_correct {d τ} :
               foreign_data_typing_infer d = Some τ ->
               foreign_data_typing_has_type d τ
           ; foreign_data_typing_infer_least {d τ₁ τ₂} : 
               foreign_data_typing_infer d = Some τ₁ ->
               foreign_data_typing_has_type d τ₂ ->
               τ₁ ≤ τ₂
         }.

  Theorem foreign_data_typing_infer_complete
        {fdata:foreign_data}
        {ftype:foreign_type}
        {ftyping:foreign_data_typing}
          {d τ} :
      foreign_data_typing_has_type d τ -> {τ' | foreign_data_typing_infer d = Some τ'}.
  Proof.
    intros.
    apply foreign_data_typing_infer_normalized.
    apply foreign_data_typing_normalized in H.
    trivial.
  Qed.

End ForeignDataTyping.

