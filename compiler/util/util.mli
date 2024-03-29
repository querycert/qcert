(*
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

(* Qcert Exception *)

exception Qcert_Error of string

(* this can't go in Logger, since that creates a circular dependency *)
type nraenv_logger_token_type = string
type nnrc_logger_token_type = string
type nnrs_imp_expr_logger_token_type = string
type nnrs_imp_stmt_logger_token_type = string
type nnrs_imp_logger_token_type = string
type dnnrc_logger_token_type = string

(**************)
(* Data types *)
(**************)

(* Data type conversions between Coq and OCaml *)

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


(**********************************)
(* Support for Enhanced operators *)
(**********************************)

val qcert_string_of_float : float -> string
val string_of_enhanced_float : float -> string
val string_of_enhanced_string : string -> string

val float_sign : float -> float
(* Timing function for CompStat   *)

val time : ('a -> 'b) -> 'a -> string * 'b


(* String Manipulation *)

val global_replace : string -> string -> string -> string
(** [global_replace const templ s] returns a string identical to [s],
except thta all substrings of [s] that match the string [const] have
been replaced by [templ]. This is intended as a replacement for the
corresponding function in Str when matching against a constant
string. *)


