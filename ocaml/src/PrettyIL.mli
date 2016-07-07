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

(* This module contains pretty-printers for intermediate languages *)

open Compiler.EnhancedCompiler

(* Character sets *)

type charkind =
  | Ascii
  | Greek

type pretty_config

val default_pretty_config : unit -> pretty_config

val set_ascii : pretty_config -> unit -> unit
val set_greek : pretty_config -> unit -> unit
val get_charset : pretty_config -> charkind
val get_charset_bool : pretty_config -> bool

val set_margin : pretty_config -> int -> unit
val get_margin : pretty_config -> int

(* Pretty data *)

val pretty_data : Format.formatter -> Data.data -> unit

(* Useful for SExp support *)
val string_of_foreign_data : Compiler.enhanced_data -> string
val foreign_data_of_string : string -> Compiler.enhanced_data

val string_of_foreign_unop : Compiler.enhanced_unary_op -> string
val string_of_unarith : Compiler.arithUOp -> string

val foreign_unop_of_string : string -> Compiler.enhanced_unary_op
val unarith_of_string : string -> Compiler.arithUOp

val string_of_foreign_binop : Compiler.enhanced_binary_op -> string
val string_of_binarith : Compiler.arithBOp -> string

val binarith_of_string : string -> Compiler.arithBOp
val foreign_binop_of_string : string -> Compiler.enhanced_binary_op

val string_of_binop : Compiler.binOp -> string

(* Pretty NRA^e *)
	
val pretty_nraenv : bool -> int -> Compiler.algenv -> string

(* Pretty NNRC *)

val pretty_nnrc : bool -> int -> Compiler.nrc -> string

(* Pretty NNRCMR *)

val pretty_nnrcmr : bool -> int -> Compiler.nrcmr -> string


(* Pretty RType *)

val pretty_rtype : bool -> int -> RType.camp_type -> string

