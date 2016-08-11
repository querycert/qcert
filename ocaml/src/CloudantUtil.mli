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

type cld_config

val default_cld_config : unit -> cld_config

val get_prefix : cld_config -> string
val set_prefix : cld_config -> string -> unit

(* Javascript harness (for inlining in Cloudant) *)

val get_harness : cld_config -> string
val set_harness : cld_config -> string -> unit

(* Cloudant stuff *)

val idioticize : string -> string -> string

val cloudant_compile_from_nra : string -> string -> Asts.nraenv -> Data.json -> string
val cloudant_compile_from_nnrcmr : string -> string -> Asts.nnrcmr -> Data.json -> string

val cloudant_compile_no_harness_from_nra : string -> Asts.nraenv -> string
val cloudant_compile_no_harness_from_nnrcmr : string -> Asts.nnrcmr -> string

val cloudant_translate_no_harness : Asts.nnrcmr -> Asts.cldmr
val cloudant_code_gen_no_harness : string -> Asts.cldmr -> string

