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

Require Import List.
Require Import String.
Require Import Utils.
Require Import ForeignRuntime.
Require Import NNRCMRRuntime.

Local Open Scope string_scope.

Section ForeigntoSpark.

  Class foreign_to_spark
        {fruntime:foreign_runtime}
        {fredop:foreign_reduce_op} : Type
  := mk_foreign_to_spark {
         foreign_to_spark_reduce_op
           (rop:foreign_reduce_op_type)
           (scala_endl quotel:string) : string
         ; foreign_to_spark_prepare_nnrcmr :
             nnrcmr -> nnrcmr
       }.

End ForeigntoSpark.

