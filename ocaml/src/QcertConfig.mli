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

type global_config = {
    mutable gconf_source : CompDriver.language;
    mutable gconf_target : CompDriver.language;
    mutable gconf_path : CompDriver.language list; (* the first element of the path must be source and the last target *)
    mutable gconf_exact_path : bool;
    mutable gconf_dir : string option;
    mutable gconf_dir_target : string option;
    mutable gconf_io : string option;
    mutable gconf_schema : TypeUtil.schema;
    gconf_cld_conf : CloudantUtil.cld_config;
    mutable gconf_emit_all : bool;
    gconf_pretty_config : PrettyIL.pretty_config;
    mutable gconf_emit_sexp : bool;
    mutable gconf_emit_sexp_all : bool;
    mutable gconf_source_sexp : bool;
    mutable gconf_java_imports : string;
    mutable gconf_mr_vinit : string;
    mutable gconf_vdbindings : CompDriver.vdbindings;
  }

val complet_configuration : global_config -> global_config

val driver_conf_of_global_conf : global_config -> string -> string -> CompDriver.driver_config
