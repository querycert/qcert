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
Require Import String.
Require Import Utils.
Require Import BrandRelation.
Require Import ForeignData.
Require Import Data.
Require Import DataNorm.

Section ForeignOperators.
  Class foreign_operators {fdata:foreign_data}
  : Type
    := mk_foreign_operators {
           (* Unary operators *)
           foreign_operators_unary : Set
           ; foreign_operators_unary_dec :> EqDec foreign_operators_unary eq
           ; foreign_operators_unary_tostring :> ToString foreign_operators_unary
           ; foreign_operators_unary_interp
               (br:brand_relation_t)
               (op:foreign_operators_unary)
               (d:data) : option data
           ; foreign_operators_unary_normalized
               (br:brand_relation_t)
               (op:foreign_operators_unary) (d o:data) :
               foreign_operators_unary_interp br op d = Some o ->
               data_normalized br d ->
               data_normalized br o
           ; foreign_operators_unary_data_tostring : data -> string
           ; foreign_operators_unary_data_totext : data -> string

           (* Binary operators *)
           ; foreign_operators_binary : Set
           ; foreign_operators_binary_dec :> EqDec foreign_operators_binary eq
           ; foreign_operators_binary_tostring :> ToString foreign_operators_binary
           ; foreign_operators_binary_interp
               (br:brand_relation_t)
               (op:foreign_operators_binary)
               (d1 d2:data) : option data
           ; foreign_operators_binary_normalized
               (br:brand_relation_t)
               (op:foreign_operators_binary) (d1 d2 o:data) :
               foreign_operators_binary_interp br op d1 d2 = Some o ->
               data_normalized br d1 ->
               data_normalized br d2 ->
               data_normalized br o
         }.

End ForeignOperators.
