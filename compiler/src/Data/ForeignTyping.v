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

Require Export Types.
Require Export ForeignRuntime.
Require Export ForeignDataTyping.
Require Export ForeignOperatorsTyping.

Class foreign_typing
      {fruntime:foreign_runtime}
      {ftype:foreign_type}
      {model:brand_model}
  : Type
  := mk_foreign_typing {
          foreign_typing_data :> foreign_data_typing
         ; foreign_typing_unary_op :> foreign_unary_op_typing
         ; foreign_typing_binary_op :> foreign_binary_op_typing
       }.

