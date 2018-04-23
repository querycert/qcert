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
Require Import CommonData.
Require Import ForeignData.
Require Import ForeignOperators.
Require Import Types.
Require Import ForeignDataTyping.
Require Import TData.

Section ForeignOperatorsTyping.

  Class foreign_unary_op_typing
        {fdata:foreign_data}
        {fuop:foreign_unary_op}
        {ftype:foreign_type}
        {fdtyping:foreign_data_typing}
        {model:brand_model}
    : Type
    := mk_foreign_unary_op_typing {
           foreign_unary_op_typing_has_type
             (fu:foreign_unary_op_type) 
             (τin τout : rtype) : Prop
           ; foreign_unary_op_typing_sound
               {fu:foreign_unary_op_type}
               {τin τout : rtype}
               (optyp:foreign_unary_op_typing_has_type fu τin τout)
               {din:data}
               (dtin:din ▹ τin) :
               (exists dout,
                   foreign_unary_op_interp brand_relation_brands fu din
                   = Some dout
                   /\ dout ▹ τout)
           ; foreign_unary_op_typing_infer (fu:foreign_unary_op_type)
             : rtype -> option rtype
           ; foreign_unary_op_typing_infer_correct
               {fu:foreign_unary_op_type}
               {τ₁ τout} :
               foreign_unary_op_typing_infer fu τ₁ = Some τout ->
               foreign_unary_op_typing_has_type fu τ₁ τout
           ; foreign_unary_op_typing_infer_least
               {fu:foreign_unary_op_type}
               {τ₁ τout₁ τout₂} : 
               foreign_unary_op_typing_infer fu τ₁ = Some τout₁ ->
               foreign_unary_op_typing_has_type fu τ₁ τout₂ ->
               τout₁ ≤ τout₂
           ; foreign_unary_op_typing_infer_complete
               {fu:foreign_unary_op_type}
               {τ₁ τout} : 
               foreign_unary_op_typing_infer fu τ₁ = None ->
               ~ foreign_unary_op_typing_has_type fu τ₁ τout
           (* returns an optional tuple containing:
       1) the inferred type of the binary operation
       2) the required type of the first argument (will be a non-proper supertype of τ₁)
            *)
           ; foreign_unary_op_typing_infer_sub (fu:foreign_unary_op_type)
             : rtype -> option (rtype*rtype)
         }.

    Class foreign_binary_op_typing
        {fdata:foreign_data}
        {fbop:foreign_binary_op}
        {ftype:foreign_type}
        {fdtyping:foreign_data_typing}
        {model:brand_model}
    : Type
    := mk_foreign_binary_op_typing {
           foreign_binary_op_typing_has_type
             (fb:foreign_binary_op_type) 
             (τin₁ τin₂ τout : rtype) : Prop
           ; foreign_binary_op_typing_sound
               {fb:foreign_binary_op_type}
               {τin₁ τin₂ τout : rtype}
               (optyp:foreign_binary_op_typing_has_type fb τin₁ τin₂ τout)
               {din₁ din₂:data}
               (dtin:din₁ ▹ τin₁)
               (dtin:din₂ ▹ τin₂) :
               (exists dout,
                   foreign_binary_op_interp brand_relation_brands fb din₁ din₂
                   = Some dout
                   /\ dout ▹ τout)
           ; foreign_binary_op_typing_infer (fb:foreign_binary_op_type)
             : rtype -> rtype -> option rtype
           ; foreign_binary_op_typing_infer_correct
               {fb:foreign_binary_op_type}
               {τ₁ τ₂ τout} :
               foreign_binary_op_typing_infer fb τ₁ τ₂ = Some τout ->
               foreign_binary_op_typing_has_type fb τ₁ τ₂ τout
           ; foreign_binary_op_typing_infer_least
               {fb:foreign_binary_op_type}
               {τ₁ τ₂ τout₁ τout₂} : 
               foreign_binary_op_typing_infer fb τ₁ τ₂ = Some τout₁ ->
               foreign_binary_op_typing_has_type fb τ₁ τ₂ τout₂ ->
               τout₁ ≤ τout₂
           ; foreign_binary_op_typing_infer_complete
               {fb:foreign_binary_op_type}
               {τ₁ τ₂ τout} : 
               foreign_binary_op_typing_infer fb τ₁ τ₂ = None ->
               ~ foreign_binary_op_typing_has_type fb τ₁ τ₂ τout
           (* returns an optional tuple containing:
       1) the inferred type of the binary operation
       2) the required type of the first argument (will be a non-proper supertype of τ₁)
       3)  the required type of the second argument (will be a non-proper supertype of τ₂) 
            *)
           ; foreign_binary_op_typing_infer_sub (fb:foreign_binary_op_type)
             : rtype -> rtype -> option (rtype*rtype*rtype)

         }.
  
End ForeignOperatorsTyping.

