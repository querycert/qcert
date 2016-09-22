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

open Compiler.EnhancedCompiler

val set_source : QcertConfig.global_config -> string -> unit
val set_target : QcertConfig.global_config -> string -> unit
val set_exact_path : QcertConfig.global_config -> unit -> unit
val add_path : QcertConfig.global_config -> string -> unit
val set_dir : QcertConfig.global_config -> string -> unit
val set_dir_target : QcertConfig.global_config -> string -> unit
val set_io : QcertConfig.global_config -> string -> unit
val set_emit_all : QcertConfig.global_config -> unit -> unit
val set_emit_sexp : QcertConfig.global_config -> unit -> unit
val set_emit_sexp_all : QcertConfig.global_config -> unit -> unit
val set_java_imports : QcertConfig.global_config -> string -> unit
val add_input_file : QcertConfig.global_config -> string -> unit
val set_mr_vinit : QcertConfig.global_config -> string -> unit
val add_vdirst : QcertConfig.global_config -> string -> unit
val add_vlocal : QcertConfig.global_config -> string -> unit
