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

open ConfigUtil
open ParseUtil
open Compiler.EnhancedCompiler

exception OQL_eval of string
      
(* Frontend Eval *)

val eval_rule : (string * string) list -> Data.data list -> string -> Data.data list option * string
val eval_oql : (string * string) list -> Data.data list -> string -> Data.data option * string

(* Core Eval *)

val eval_nraenv : lang_config -> (string * string) list -> Data.data list -> Asts.nraenv -> Data.data option

