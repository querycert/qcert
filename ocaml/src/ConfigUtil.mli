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

open DataUtil
open Compiler.EnhancedCompiler

(* Configuration utils for the Camp evaluator and compiler *)

type source_lang =
  | RULE
  | OQL

type target_lang =
  | ORIG
  | NRAEnv
  | NNRC
  | DNNRC
  | NNRCMR
  | CLDMR
  | Java
  | JS
  | Spark
  | Spark2
  | Cloudant

type lang_config

val default_eval_lang_config : unit -> lang_config
val default_comp_lang_config : unit -> lang_config

val get_source_lang : lang_config -> source_lang
val get_target_lang : lang_config -> target_lang

val change_source : lang_config -> string -> unit
val change_target : lang_config -> string -> unit

val get_cld_config : lang_config -> CloudantUtil.cld_config

(* Target language *)

val suffix_nra : unit -> string
val suffix_nrasexp : unit -> string
val suffix_nrc : unit -> string
val suffix_nrcsexp : unit -> string
val suffix_dnrc : unit -> string
val suffix_dnrcsexp : unit -> string
val suffix_nrcmr : unit -> string
val suffix_nrcmr_sparksexp : unit -> string
val suffix_nrcmr_spark : unit -> string
val suffix_nrcmr_spark2sexp : unit -> string
val suffix_nrcmr_spark2 : unit -> string
val suffix_nrcmr_cldmr : unit -> string
val suffix_nrcmr_cldmrsexp : unit -> string
val suffix_stats : unit -> string
val suffix_target : lang_config -> string

val suffix_sdata : unit -> string
    
(* Evaluator Section *)
  
type eval_config

val default_eval_config : unit -> eval_config

val set_eval_io : eval_config -> Data.json -> unit
val set_input : eval_config -> string -> unit
val set_format : eval_config -> string -> unit

val get_format : eval_config -> serialization_format
val get_eval_only : eval_config -> bool ref
val get_debug : eval_config -> bool ref
val get_eval_io : eval_config -> Data.json option
val get_eval_inputs : eval_config -> string list
val get_eval_lang_config : eval_config -> lang_config

(* Data Section *)
  
type data_config

val default_data_config : unit -> data_config

val set_json : data_config -> Data.json -> unit
val set_data_format : data_config -> string -> unit
val set_data_schema : data_config -> Data.json -> unit
val set_data_dir : data_config -> string -> unit

val get_data_format : data_config -> serialization_format
val get_data_schema : data_config -> Data.json option
val get_data_dir : data_config -> string option

(* Compiler Section *)
  
type comp_config

val default_comp_config : unit -> comp_config

val set_comp_io : comp_config -> Data.json -> unit
val set_comp_input : comp_config -> string -> unit
val set_dir : comp_config -> string -> unit
val set_display_dir : comp_config -> string -> unit
val set_stats : comp_config -> unit -> unit
val set_display : comp_config -> unit -> unit
val set_display_sexp : comp_config -> unit -> unit
val set_test_sexp : comp_config -> unit -> unit

val get_comp_io : comp_config -> Data.json option
val get_dir : comp_config -> string option
val get_display_dir : comp_config -> string option
val get_target_display : comp_config -> bool ref
val get_target_display_sexp : comp_config -> bool ref
val get_test_sexp : comp_config -> bool ref
val get_target_stats : comp_config -> bool ref
val get_comp_inputs : comp_config -> string list
val get_comp_lang_config : comp_config -> lang_config
val get_pretty_config : comp_config -> PrettyIL.pretty_config

(* Backend Section *)

val set_java_imports : comp_config -> string -> unit
val get_java_imports : comp_config -> string


