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

(* This module contains parsing utilities *)

open Compiler.EnhancedCompiler
open Asts

(******************)
(* Specific Parse *)
(******************)

val parse_io : Lexing.lexbuf -> io_ast
val parse_json : Lexing.lexbuf -> json_ast

val parse_rule : Lexing.lexbuf -> string * Asts.rORc_ast
val parse_camp : Lexing.lexbuf -> camp

val parse_oql : Lexing.lexbuf -> oql_ast

(****************)
(* S-Expr Parse *)
(****************)

val parse_sexp : Lexing.lexbuf -> sexp_ast
val parse_io_sexp : Lexing.lexbuf -> io_ast
val parse_nra_sexp : Lexing.lexbuf -> algenv
val parse_nrc_sexp : Lexing.lexbuf -> nrc
val parse_nrcmr_sexp : Lexing.lexbuf -> nrcmr
val parse_cldmr_sexp : Lexing.lexbuf -> cldmr

