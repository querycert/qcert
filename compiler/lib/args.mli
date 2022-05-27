(*
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

open EnhancedCompiler.EnhancedCompiler

val set_qname : Config.global_config -> string -> unit
val set_class_name : Config.global_config -> string -> unit
val set_source : Config.global_config -> string -> unit
val set_target : Config.global_config -> string -> unit
val set_exact_path : Config.global_config -> unit -> unit
val add_path : Config.global_config -> string -> unit
val set_dir : Config.global_config -> string -> unit
val set_dir_target : Config.global_config -> string -> unit
val set_schema_content : Config.global_config -> string -> unit
val set_input_content : Config.global_config -> string -> unit
val set_output_content : Config.global_config -> string -> unit
val set_schema_file : Config.global_config -> string -> unit
val set_input_file : Config.global_config -> string -> unit
val set_output_file : Config.global_config -> string -> unit
val set_io_file : Config.global_config -> string -> unit
val set_emit_all : Config.global_config -> unit -> unit
val set_emit_sexp : Config.global_config -> unit -> unit
val set_emit_sexp_all : Config.global_config -> unit -> unit
val set_eval : Config.global_config -> unit -> unit
val set_eval_all : Config.global_config -> unit -> unit
val set_eval_debug : Config.global_config -> unit -> unit
val set_eval_validate : Config.global_config -> unit -> unit
val set_quiet : Config.global_config -> unit -> unit
val set_source_sexp : Config.global_config -> unit -> unit
val set_java_imports : Config.global_config -> string -> unit
val set_vinit : Config.global_config -> string -> unit
val set_stat : Config.global_config -> unit -> unit
val set_stat_all : Config.global_config -> unit -> unit
val set_stat_tree : Config.global_config -> unit -> unit

val set_optim_config_file : Config.global_config -> string -> unit
val set_emit_optim_config : Config.global_config -> unit -> unit
val set_optims : Config.global_config -> QDriver.optim_config -> unit

val set_prefix : Config.global_config -> string -> unit

