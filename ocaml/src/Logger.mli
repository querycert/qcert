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

(* This module contains the implementation for the optimization logger *)

open Util

val log_startPass : string -> 'a -> logger_token_type
val log_step : logger_token_type -> string -> 'a -> 'a -> logger_token_type
val log_endPass : logger_token_type -> 'a -> logger_token_type

val set_trace : unit -> unit
val unset_trace : unit -> unit

