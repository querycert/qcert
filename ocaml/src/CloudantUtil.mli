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

(* Some Cloudant Utils *)

open Compiler.EnhancedCompiler

(* Cloudant format *)

type cldkind =
  | Curl
  | Design

type cld_config

val default_cld_config : unit -> cld_config

val get_cld : cld_config -> cldkind
val set_curl : cld_config -> unit -> unit

val get_prefix : cld_config -> string
val set_prefix : cld_config -> string -> unit

(* Javascript harness (for inlining in Cloudant) *)

val get_harness : cld_config -> string
val set_harness : cld_config -> string -> unit

(* Cloudant stuff *)

val idioticize : string -> string -> string

val cloudant_compile_from_nra : cldkind -> string -> string -> Compiler.algenv -> Data.data -> string
val cloudant_compile_from_nnrcmr : cldkind -> string -> string -> (Compiler.var * Compiler.localization) list * Compiler.nrcmr -> Data.data -> string

val cloudant_compile_no_harness_from_nra : string -> Compiler.algenv -> string
val cloudant_compile_no_harness_from_nnrcmr : string -> (Compiler.var * Compiler.localization) list * Compiler.nrcmr -> string

val cloudant_translate_no_harness : (Compiler.var * Compiler.localization) list * Compiler.nrcmr -> Compiler.cld_mrl

val cloudant_code_gen_no_harness : string -> Compiler.cld_mrl -> string

