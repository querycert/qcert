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

(* Util *)

val get_display_fname : comp_config -> string -> string

(* Display ILs *)

val display_to_string : pretty_config -> (RType.brand_model * RType.camp_type) option -> nraenv -> (string * string * string * string * string * string)
val display_nraenv_top : PrettyIL.charkind -> int -> (RType.brand_model * RType.camp_type) option -> string option -> string -> nraenv -> unit

(* SExp ILs *)
    
val sexp_string_to_camp : string -> camp
val camp_to_sexp_string : camp -> string

val sexp_string_to_nraenv : string -> nraenv
val nraenv_to_sexp_string : nraenv -> string

val sexp_string_to_nnrc : string -> nnrc
val nnrc_to_sexp_string : nnrc -> string

val sexp_string_to_nnrcmr : string -> nnrcmr
val nnrcmr_to_sexp_string : nnrcmr -> string

val sexp_string_to_cldmr : string -> cldmr
val cldmr_to_sexp_string : cldmr -> string

val sexp_nraenv_top : string -> nraenv -> unit

(* Data Display *)

val display_sdata : data_config -> string -> string list -> unit

