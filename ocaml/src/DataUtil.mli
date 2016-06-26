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
open Compiler.EnhancedCompiler

(* Data utils for the Camp evaluator and compiler *)

type io_hierarchy = Data.data
type io_hierarchy_list = (string * string) list
type io_input = Data.data list
type io_output = Data.data list

type io_data = Data.data option

val get_hierarchy : io_data -> io_hierarchy
val get_hierarchy_cloudant : io_data -> io_hierarchy
val build_hierarchy : io_hierarchy -> io_hierarchy_list
val get_input : ConfigUtil.eval_config -> io_data -> io_input
val get_output : io_data -> io_output

