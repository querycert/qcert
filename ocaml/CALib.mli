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

(* Proto CALib *)

(* Note: Attempt for now is no visible dependency on any other module.
   I.e., they will be hiden and the API is self contained. *)

(* Abstract AST types *)

type camp
type nraenv
type nnrc
type dnnrc
type nnrcmr
type cldmr

(*
 *  Frontend section
 *)

(* From source to CAMP *)
val rule_to_camp : string -> camp

(* From camp to NRAEnv *)
val camp_to_nraenv : camp -> nraenv

(* From source to NRAEnv *)
val rule_to_nraenv : string -> nraenv
val oql_to_nraenv : string -> nraenv

(*
 *  Core compiler section
 *)

(* Translations *)
val translate_nraenv_to_nnrc : nraenv -> nnrc
val translate_nnrc_to_nnrcmr : nnrc -> nnrcmr
(* Doesn't work on ocamljava with Java 8 (generics typing issue with the way lists are wrapped by ocamljava *)
(* val translate_nnrc_to_dnnrc : string list -> nnrc -> dnnrc *)

(* NRAEnv Optimizer *)
val optimize_nraenv : nraenv -> nraenv

(* NNRC Optimizer *)
val optimize_nnrc : nnrc -> nnrc

(* NNRCMR Optimizer *)
val optimize_nnrcmr : nnrcmr -> nnrcmr
val optimize_nnrcmr_for_cloudant : nnrcmr -> nnrcmr
val optimize_nnrcmr_for_spark : nnrcmr -> nnrcmr

(* For convenience *)
(* Note: This includes optimization phases *)
val compile_nraenv_to_nnrc : nraenv -> nnrc
val compile_nraenv_to_nnrcmr : nraenv -> nnrcmr


(*
 *  Backend section
 *)

val nnrc_to_js : nnrc -> string
val nnrc_to_java : string -> string -> nnrc -> string
val nnrcmr_to_spark : string -> nnrcmr -> string

val translate_nnrcmr_to_cldmr : nnrcmr -> cldmr

val cldmr_to_cloudant : string -> string -> cldmr -> string

(* For convenience *)

val compile_nraenv_to_js : nraenv -> string
val compile_nraenv_to_java : string -> string -> nraenv -> string
val compile_nraenv_to_spark : string -> nraenv -> string
val compile_nraenv_to_cloudant : string -> string -> nraenv -> string
val compile_nnrcmr_to_cloudant : string -> string -> nnrcmr -> string


(*
 *  ASTs support
 *)

(* Import/Export ASTs *)
(* WARNING: Not supported yet *)

val export_camp : camp -> string
val import_camp : string -> camp

val export_nraenv : nraenv -> string
val import_nraenv : string -> nraenv

val export_nnrc : nnrc -> string
val import_nnrc : string -> nnrc

val export_nnrcmr : nnrcmr -> string
val import_nnrcmr : string -> nnrcmr

val export_cldmr : cldmr -> string
val import_cldmr : string -> cldmr

(* Pretties *)

val pretty_nraenv : bool -> int -> nraenv -> string
val pretty_nnrc : bool -> int -> nnrc -> string
val pretty_nnrcmr_for_spark : bool -> int -> nnrcmr -> string
val pretty_nnrcmr_for_cloudant : bool -> int -> nnrcmr -> string

(* Options *)

val set_optim_trace : unit -> unit
val unset_optim_trace : unit -> unit


