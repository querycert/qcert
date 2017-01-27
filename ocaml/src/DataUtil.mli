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
open Compiler.EnhancedCompiler

type serialization_format =
  | META
  | ENHANCED

(* Data utils for the Camp evaluator and compiler *)

(* Extract JSON components *)

type io_json = QData.json

type io_input = QData.json
type io_output = QData.json
type io_schema = QData.json
type io_hierarchy = QData.json
type io_model = QData.json
type io_globals = QData.json

type rtype_content = QData.json
type vrtype_content = QData.json

type content_input = (char list * QData.data) list
type content_output = QData.data list

type content_hierarchy = (char list * char list) list
type content_brandTypes = (string * string) list
type content_typeDefs = (string * rtype_content) list
type content_globals = (string * vrtype_content) list
type content_schema = content_hierarchy * content_brandTypes * content_typeDefs * content_globals

val get_io_components : io_json option -> io_input * io_output * io_schema

val build_input : serialization_format -> io_json option -> content_input
val build_output : io_json option -> content_output
val build_schema : io_json option -> content_schema

val display_sdata : string option -> string -> string list -> string -> unit
