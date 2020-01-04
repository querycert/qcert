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
Require Import DataRuntime.
Require Import EJsonRuntime.
Require Import ForeignDataToEJson.
Require Import DataToEJson.

Section ForeignToEJsonRuntime.
  Class foreign_to_ejson_runtime
        {fruntime:foreign_runtime}
        {fejson:foreign_ejson}
        {fetojson:foreign_to_ejson}
        {fejsonops:foreign_ejson_runtime}
      : Type
      := mk_foreign_to_ejson_runtime {
             foreign_to_ejson_runtime_of_unary_op
               (uop:foreign_operators_unary) : foreign_ejson_runtime_op
             ; foreign_to_ejson_runtime_of_unary_op_correct
                 (uop:foreign_operators_unary)
                 (br:brand_relation_t)
                 (d:data) :
                 lift data_to_ejson (foreign_operators_unary_interp br uop d) =
                 foreign_ejson_runtime_op_interp (foreign_to_ejson_runtime_of_unary_op uop)
                                                 (data_to_ejson d::nil)
             ; foreign_to_ejson_runtime_of_binary_op
               (bop:foreign_operators_binary) : foreign_ejson_runtime_op
             ; foreign_to_ejson_runtime_of_binary_op_correct
                 (bop:foreign_operators_binary)
                 (br:brand_relation_t)
                 (d1 d2:data) :
                 lift data_to_ejson (foreign_operators_binary_interp br bop d1 d2) =
                 foreign_ejson_runtime_op_interp (foreign_to_ejson_runtime_of_binary_op bop)
                                                 (data_to_ejson d1::data_to_ejson d2::nil)
         }.

End ForeignToEJsonRuntime.

