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

open Util
open ConfigUtil
open DataUtil
open Compiler.EnhancedCompiler

(* Data utils for the Camp evaluator and compiler *)

val make_brand_relation : (string * string) list -> (char list * char list) list
  
val rtype_content_to_rtype : (string * string) list -> rtype_content -> RType.camp_type
  
val model_content_to_model : (string * string) list -> model_content -> RType.brand_model option

