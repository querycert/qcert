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

open Util
open LexUtil
open Compiler.EnhancedCompiler
open Asts


(*****************)
(* Generic Parse *)
(*****************)

let parse parser lexer buf =
    try
      parser lexer buf
    with
    | LexError msg ->
	begin
	  let pos = buf.Lexing.lex_start_p in
	  let msg = Printf.sprintf "At line %d column %d: %s%!" pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol) msg in
	  raise (LexError msg)
	end
    | _ ->
	begin
	  let pos = buf.Lexing.lex_start_p in
	  let msg = Printf.sprintf "At line %d column %d: syntax error%!" pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol) in
	  raise (LexError msg)
	end



(******************)
(* Specific Parse *)
(******************)


let parse_io f : io_ast = parse DataParser.main (DataLexer.token (string_buff ())) f
let parse_json f : json_ast = parse DataParser.main (DataLexer.token (string_buff ())) f

let parse_rule f : string * rORc_ast = parse RuleParser.rulemain (RuleLexer.token (string_buff ())) f
let parse_camp f : camp = parse RuleParser.patmain (RuleLexer.token (string_buff ())) f
  
let parse_oql f : oql_ast = OQL.tableify (parse OQLParser.main (OQLLexer.token (string_buff ())) f)

(****************)
(* S-Expr Parse *)
(****************)

let parse_sexp f : sexp_ast = parse SExpParser.main (SExpLexer.token (string_buff ())) f
let parse_io_sexp f : data_ast = sexp_to_data (parse_sexp f)
let parse_nra_sexp f : algenv = sexp_to_alg (parse_sexp f)
let parse_nrc_sexp f : nrc = sexp_to_nrc (parse_sexp f)
let parse_nrcmr_sexp f : nrcmr = sexp_to_nrcmr (parse_sexp f)
let parse_cldmr_sexp f : cldmr = sexp_to_cldmr (parse_sexp f)

