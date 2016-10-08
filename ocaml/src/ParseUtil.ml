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


let parse_io f : QData.json = parse DataParser.main (DataLexer.token (string_buff ())) f
let parse_json f : QData.json = parse DataParser.main (DataLexer.token (string_buff ())) f

let parse_rule f : string * QLang.query = parse RuleParser.rulemain (RuleLexer.token (string_buff ())) f
let parse_camp f : QLang.camp = parse RuleParser.patmain (RuleLexer.token (string_buff ())) f
  
let parse_oql f : QLang.oql = QOQL.tableify (parse OQLParser.main (OQLLexer.token (string_buff ())) f)

let parse_lambda_nra f : QLang.lambda_nra = QLambdaNRA.latableify (parse LambdaNRAParser.main (LambdaNRALexer.token (string_buff ())) f)

(****************)
(* S-Expr Parse *)
(****************)

let parse_sexp f : SExp.sexp = parse SExpParser.main (SExpLexer.token (string_buff ())) f
let parse_io_sexp f : QData.data = AstsToSExp.sexp_to_data (parse_sexp f)
let parse_camp_sexp f : QLang.camp = AstsToSExp.sexp_to_camp (parse_sexp f)
let parse_nraenv_sexp f : QLang.nraenv = AstsToSExp.sexp_to_nraenv (parse_sexp f)
let parse_nnrc_sexp f : QLang.nnrc = AstsToSExp.sexp_to_nnrc (parse_sexp f)
let parse_nnrcmr_sexp f : QLang.nnrcmr = AstsToSExp.sexp_to_nnrcmr (parse_sexp f)
let parse_cldmr_sexp f : QLang.cldmr = AstsToSExp.sexp_to_cldmr (parse_sexp f)

(*******************
 * Languages Parse *
 *******************)

let parse_query l f : (string * QLang.query) =
  begin match l with
  | Compiler.L_rule -> parse_rule f
  | Compiler.L_camp -> ("CAMP", Compiler.Q_camp (parse_camp f))
  | Compiler.L_oql -> ("OQL", Compiler.Q_oql (parse_oql f))
  | Compiler.L_sql -> raise (CACo_Error "No parser for SQL available")
  | Compiler.L_lambda_nra -> ("LambdaNRA", Compiler.Q_lambda_nra (parse_lambda_nra f))
  | Compiler.L_nra -> raise (CACo_Error "No parser for NRA available")
  | Compiler.L_nraenv -> ("NRAEnv", Compiler.Q_nraenv (parse_nraenv_sexp f))
  | Compiler.L_nnrc -> ("NNRC", Compiler.Q_nnrc (parse_nnrc_sexp f))
  | Compiler.L_nnrcmr -> ("NNRCMR", Compiler.Q_nnrcmr (parse_nnrcmr_sexp f))
  | Compiler.L_cldmr -> ("CldMR", Compiler.Q_cldmr (parse_cldmr_sexp f))
  | Compiler.L_dnnrc_dataset -> raise (CACo_Error "No parser for DNNRC available")
  | Compiler.L_dnnrc_typed_dataset -> raise (CACo_Error "No parser for typed DNNRC available")
  | Compiler.L_javascript -> raise (CACo_Error "No parser for Javascript available")
  | Compiler.L_java -> raise (CACo_Error "No parser for Java available")
  | Compiler.L_spark -> raise (CACo_Error "No parser for Spark available")
  | Compiler.L_spark2 -> raise (CACo_Error "No parser for Spark 2.0 available")
  | Compiler.L_cloudant -> raise (CACo_Error "No parser for Cloudant available")
  | Compiler.L_error err ->
      let err = string_of_char_list err in
      raise (CACo_Error ("No parser for Error language available: "^err))
  end
