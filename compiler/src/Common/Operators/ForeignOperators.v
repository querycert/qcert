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
  Class foreign_unary_op {fdata:foreign_data}
  : Type
    := mk_foreign_unary_op {
           foreign_unary_op_type : Set
           ; foreign_unary_op_dec :> EqDec foreign_unary_op_type eq
           ; foreign_unary_op_tostring :> ToString foreign_unary_op_type
           ; foreign_unary_op_interp
               (br:brand_relation_t)
               (op:foreign_unary_op_type)
               (d:data) : option data
           ; foreign_unary_op_normalized
               (br:brand_relation_t)
               (op:foreign_unary_op_type) (d o:data) :
               foreign_unary_op_interp br op d = Some o ->
               data_normalized br d ->
               data_normalized br o
           ; foreign_unary_op_data_tostring : data -> string
           ; foreign_unary_op_data_totext : data -> string
         }.

  Class foreign_binary_op {fdata:foreign_data}
    : Type
    := mk_foreign_binary_op {
           foreign_binary_op_type : Set
           ; foreign_binary_op_dec :> EqDec foreign_binary_op_type eq
           ; foreign_binary_op_tostring :> ToString foreign_binary_op_type
           ; foreign_binary_op_interp
               (br:brand_relation_t)
               (op:foreign_binary_op_type)
               (d1 d2:data) : option data
           ; foreign_binary_op_normalized
               (br:brand_relation_t)
               (op:foreign_binary_op_type) (d1 d2 o:data) :
               foreign_binary_op_interp br op d1 d2 = Some o ->
               data_normalized br d1 ->
               data_normalized br d2 ->
               data_normalized br o
         }.

End ForeignOperators.
