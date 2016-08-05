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

(* This module contains a few basic utilities *)

(* CACo Exception *)

exception CACo_Error of string

(* this can't go in Logger, since that creates a circular dependency *)
type logger_token_type = string

(**************)
(* Data types *)
(**************)

(* Data type conversions between Coq and OCaml *)

val string_of_char_list : char list -> string
val char_list_of_string : string -> char list
val coq_Z_of_int : int -> int


(*******)
(* I/O *)
(*******)

val os_newline : string
val string_of_file : string -> string

(* File print *)

val make_file : string -> string -> unit

(* Make up target file name *)

val target_f : string option -> string -> string
val outname : string -> string -> string


(**********)
(* Lookup *)
(**********)

(*
val get_data : string -> (string * 'a) list -> 'a
val get_data_raise : string -> (string * 'a) list -> 'a
*)

(**********************************)
(* Support for Enhanced operators *)
(**********************************)

val float_sum : float list -> float
val float_arithmean : float list -> float
val float_listmin : float list -> float
val float_listmax : float list -> float

val qcert_string_of_float : float -> string

