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

Require Export ForeignData.
Require Export ForeignDataToJSON.
Require Export ForeignOperators.

Class foreign_runtime : Type
  := mk_foreign_runtime {
         foreign_runtime_data :> foreign_data
         ; foreign_runtime_unary_op :> foreign_unary_op
         ; foreign_runtime_binary_op :> foreign_binary_op
         ; foreign_runtime_tojson :> foreign_to_JSON
       }.

