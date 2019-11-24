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
open QcertCompiler.EnhancedCompiler

type serialization_format =
  | META
  | ENHANCED

(* Data utils for the Camp evaluator and compiler *)

(* Extract JSON components *)

type io_json = QData.json

type io_input = QData.json
type io_output = QData.json
type io_schema = QData.json

type io_inheritance = QData.json
type io_brandTypes = QData.json
type io_typeDefs = QData.json
type io_globals = QData.json

type rtype_content = QData.json
type vrtype_content = QData.json

type content_input = (char list * QData.qdata) list
type content_output = QData.qdata

type content_inheritance = (char list * char list) list
type full_content_inheritance = (content_inheritance * io_inheritance)
type content_brandTypes = (string * string) list
type content_typeDefs = (string * rtype_content) list
type content_globals = (string * vrtype_content) list
type content_schema = full_content_inheritance * io_brandTypes option * io_typeDefs option * io_globals option

(* Optimization support *)
type optim_phase =
    { mutable optim_phase_name : string;
      mutable optim_phase_iter : int;
      mutable optim_phase_optims : string list; }
type optim_language =
    { mutable optim_language_name : string;
      mutable optim_phases : optim_phase list; }

val get_io_components : io_json option -> io_input option * io_output option * io_schema option

val build_input : serialization_format -> content_inheritance -> io_input -> content_input
val build_output : content_inheritance -> io_output -> content_output
val build_schema : io_schema -> content_schema
val build_brandTypes : io_brandTypes -> content_brandTypes
val build_typeDefs : io_typeDefs -> content_typeDefs
val build_globals : io_globals -> content_globals

val build_optim_config : QData.json -> QDriver.optim_config
