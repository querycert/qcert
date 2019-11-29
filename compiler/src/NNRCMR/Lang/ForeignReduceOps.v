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
Require Import List.
Require Import Utils.
Require Import CommonRuntime.

Section ForeignReduceOps.
  Class foreign_reduce_op {fdata:foreign_data}
  : Type
    := mk_foreign_reduce_op {
           foreign_reduce_op_type : Set
           ; foreign_reduce_op_dec :> EqDec foreign_reduce_op_type eq
           ; foreign_reduce_op_tostring :> ToString foreign_reduce_op_type
           ; foreign_reduce_op_interp 
               (br:brand_relation_t)
               (op:foreign_reduce_op_type)
               (dl:list data) : option data                                 
           ; foreign_reduce_op_normalized
               (br:brand_relation_t)
               (op:foreign_reduce_op_type) (dl:list data) (o:data) :
               foreign_reduce_op_interp br op dl = Some o ->
               Forall (data_normalized br) dl ->
               data_normalized br o
         }.

End ForeignReduceOps.

