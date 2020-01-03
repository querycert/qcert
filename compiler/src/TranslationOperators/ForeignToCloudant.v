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
Require Import CldMR.
Require Import ForeignCloudant.

Local Open Scope string_scope.

Section ForeigntoCloudant.

  Class foreign_to_cloudant
        {fruntime:foreign_runtime}
        {fredop:foreign_reduce_op} : Type
  := mk_foreign_to_cloudant {
         foreign_to_cloudant_reduce_op
           (rop:foreign_reduce_op_type)
         : cld_reduce_op
         ; foreign_to_cloudant_prepare_nnrcmr :
             nnrcmr -> nnrcmr
         ; foreign_to_cloudant_nnrcmr_prepared :
             nnrcmr -> Prop
         ; foreign_to_cloudant_prepare_nnrcmr_prepares (src:nnrcmr) :
             foreign_to_cloudant_nnrcmr_prepared
               (foreign_to_cloudant_prepare_nnrcmr src)
       }.

End ForeigntoCloudant.

