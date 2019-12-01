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

open QcertExtracted
open QcertCompiler.EnhancedCompiler

(* Configuration utils for the Camp evaluator and compiler *)

type lang_config

val default_eval_lang_config : unit -> lang_config
val default_comp_lang_config : unit -> lang_config

val get_source_lang : lang_config -> string option
val get_source_lang_caco : lang_config -> string
val get_source_lang_caev : lang_config -> string
val get_target_lang : lang_config -> string option
val get_target_lang_caco : lang_config -> string
val get_target_lang_caev : lang_config -> string
val get_path : lang_config -> string list

val change_source : lang_config -> string -> unit
val change_target : lang_config -> string -> unit
val add_path : lang_config -> string -> unit
val set_path : lang_config -> string list -> unit

(* Target language *)

val suffix_sql : unit -> string
val suffix_sqlpp : unit -> string
val suffix_lambda_nrasexp : unit -> string
val suffix_nra : unit -> string
val suffix_nraenv : unit -> string
val suffix_nrasexp : unit -> string
val suffix_nnrc_core : unit -> string
val suffix_nnrc : unit -> string
val suffix_nnrcsexp : unit -> string
val suffix_dnnrc : unit -> string
val suffix_dnnrcsexp : unit -> string
val suffix_nnrcmr : unit -> string
val suffix_nnrcmr_spark_dfsexp : unit -> string
val suffix_nnrcmr_spark_df : unit -> string
val suffix_stats : unit -> string

val suffix_of_language : QLang.language -> string
(* val suffix_target : lang_config -> string *)

val suffix_sdata : unit -> string

(* Evaluator Section *)

type eval_config

val default_eval_config : unit -> eval_config

val set_eval_io : eval_config -> QData.json -> unit
val set_eval_schema : eval_config -> string -> unit
val set_input : eval_config -> string -> unit

val get_eval_only : eval_config -> bool ref
val get_debug : eval_config -> bool ref
val get_eval_io : eval_config -> QData.json option
val get_eval_schema : eval_config -> string option
val get_eval_inputs : eval_config -> string list
val get_eval_lang_config : eval_config -> lang_config

(* Data Section *)

type data_config

val default_data_config : unit -> data_config

val set_json : data_config -> QData.json -> unit
val set_data_schema : data_config -> QData.json -> unit
val set_data_dir : data_config -> string -> unit

val get_data_schema : data_config -> QData.json option
val get_data_dir : data_config -> string option

(* Compiler Section *)

type comp_config

val default_comp_config : unit -> comp_config

val set_comp_io : comp_config -> string -> unit
val set_comp_input : comp_config -> string -> unit
val set_dir : comp_config -> string -> unit
val set_display_dir : comp_config -> string -> unit
val set_stats : comp_config -> unit -> unit
val set_display : comp_config -> unit -> unit
val set_display_sexp : comp_config -> unit -> unit
val set_test_sexp : comp_config -> unit -> unit

val get_comp_io : comp_config -> string option
val get_dir : comp_config -> string option
val get_display_dir : comp_config -> string option
val get_target_display : comp_config -> bool ref
val get_target_display_sexp : comp_config -> bool ref
val get_test_sexp : comp_config -> bool ref
val get_target_stats : comp_config -> bool ref
val get_comp_inputs : comp_config -> string list
val get_comp_lang_config : comp_config -> lang_config
val get_pretty_config : comp_config -> PrettyCommon.pretty_config

(* Backend Section *)

val set_java_imports : comp_config -> string -> unit
val get_java_imports : comp_config -> string
