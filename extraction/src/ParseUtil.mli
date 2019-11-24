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

open QcertCompiler.EnhancedCompiler

(******************
 * Specific Parse *
 ******************)

val parse_io : Lexing.lexbuf -> QData.json
val parse_json : Lexing.lexbuf -> QData.json

val parse_rule : Lexing.lexbuf -> string * QLang.camp_rule
val parse_camp : Lexing.lexbuf -> string * QLang.camp

val parse_oql : Lexing.lexbuf -> QLang.oql

(****************
 * S-Expr Parse *
 ****************)

val parse_sexp : Lexing.lexbuf -> SExp.sexp
val parse_io_sexp : Lexing.lexbuf -> QData.qdata

val parse_camp_sexp : Lexing.lexbuf -> QLang.camp
val parse_nraenv_sexp : Lexing.lexbuf -> QLang.nraenv_core
val parse_nnrc_sexp : Lexing.lexbuf -> QLang.nnrc
val parse_nnrs_sexp : Lexing.lexbuf -> QLang.nnrs
val parse_nnrcmr_sexp : Lexing.lexbuf -> QLang.nnrcmr

(*******************
 * Languages Parse *
 *******************)

val parse_query : QLang.language -> Lexing.lexbuf -> string * QLang.query

