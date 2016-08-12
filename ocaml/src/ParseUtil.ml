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


let parse_io f : Asts.io_ast = parse DataParser.main (DataLexer.token (string_buff ())) f
let parse_json f : Asts.json_ast = parse DataParser.main (DataLexer.token (string_buff ())) f

let parse_rule f : string * CompDriver.query = parse RuleParser.rulemain (RuleLexer.token (string_buff ())) f
let parse_camp f : CompDriver.camp = parse RuleParser.patmain (RuleLexer.token (string_buff ())) f
  
let parse_oql f : CompDriver.oql = OQL.tableify (parse OQLParser.main (OQLLexer.token (string_buff ())) f)

(****************)
(* S-Expr Parse *)
(****************)

let parse_sexp f : SExp.sexp = parse SExpParser.main (SExpLexer.token (string_buff ())) f
let parse_io_sexp f : Asts.data_ast = AstsToSExp.sexp_to_data (parse_sexp f)
let parse_camp_sexp f : CompDriver.camp = AstsToSExp.sexp_to_camp (parse_sexp f)
let parse_nraenv_sexp f : CompDriver.nraenv = AstsToSExp.sexp_to_nraenv (parse_sexp f)
let parse_nnrc_sexp f : CompDriver.nnrc = AstsToSExp.sexp_to_nnrc (parse_sexp f)
let parse_nnrcmr_sexp f : CompDriver.nnrcmr = AstsToSExp.sexp_to_nnrcmr (parse_sexp f)
let parse_cldmr_sexp f : CompDriver.cldmr = AstsToSExp.sexp_to_cldmr (parse_sexp f)

