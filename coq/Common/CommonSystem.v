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

Require Export CommonRuntime.
Require Export CommonTypes.

Class basic_model : Type
  := mk_basic_model {
         basic_model_runtime :> foreign_runtime
         ; basic_model_foreign_type :> foreign_type
         ; basic_model_brand_model :> brand_model
         ; basic_model_foreign_typing :> foreign_typing
       }.

