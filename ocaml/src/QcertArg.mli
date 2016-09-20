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

type qcert_config = {
    mutable qconf_source : CompDriver.language option;
    mutable qconf_target : CompDriver.language option;
    mutable qconf_path : CompDriver.language list;
    mutable qconf_dir : string option;
    mutable qconf_io : string option;
    mutable qconf_schema : TypeUtil.schema;
    qconf_cld_conf : CloudantUtil.cld_config;
    mutable qconf_emit_all : bool;
    qconf_pretty_config : PrettyIL.pretty_config;
    mutable qconf_java_imports : string;
    mutable qconf_input_files : string list;
    mutable qconf_mr_vinit : string;
    mutable qconf_vdbindings : CompDriver.vdbindings;
  }

val default_qconf : unit -> qcert_config

val driver_conf_of_qcert_conf : qcert_config -> string -> CompDriver.driver_config

val language_of_name : string -> CompDriver.language
val name_of_language : CompDriver.language -> string

val set_source : qcert_config -> string -> unit
val set_target : qcert_config -> string -> unit
val add_path : qcert_config -> string -> unit
val set_dir : qcert_config -> string -> unit
val set_io : qcert_config -> string -> unit
val set_emit_all : qcert_config -> unit -> unit
val set_java_imports : qcert_config -> string -> unit
val add_input_file : qcert_config -> string -> unit
val set_mr_vinit : qcert_config -> string -> unit
val add_vdirst : qcert_config -> string -> unit
val add_vlocal : qcert_config -> string -> unit
