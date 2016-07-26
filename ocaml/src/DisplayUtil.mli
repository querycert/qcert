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

open Asts
open Compiler.EnhancedCompiler
open Util
open ConfigUtil
open PrettyIL

(* Display ILs *)

val display_to_string : pretty_config -> (RType.brand_model * RType.camp_type) option -> algenv -> (string * string * string * string * string * string)

val display_algenv_top : comp_config -> (RType.brand_model * RType.camp_type) option -> (string * algenv) -> unit

(* SExp ILs *)
    
val sexp_string_to_nra : string -> algenv
val nra_to_sexp_string : algenv -> string

val sexp_string_to_nrc : string -> nrc
val nrc_to_sexp_string : nrc -> string

val sexp_string_to_nrcmr : string -> nrcmr
val nrcmr_to_sexp_string : nrcmr -> string

val sexp_string_to_cldmr : string -> cldmr
val cldmr_to_sexp_string : cldmr -> string

val sexp_algenv_top : comp_config -> (string * algenv) -> unit

(* Data Display *)

val display_sdata : data_config -> string -> string list -> unit

