(*
 * Copyright 2015-2017 IBM Corporation
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

open QcertUtils.Util
open QcertUtils.LexUtil
open QcertExtracted
open QcertParsers

open QcertCompiler.EnhancedCompiler


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

let parse_rule f : string * QLang.camp_rule = parse RuleParser.rulemain (RuleLexer.token (string_buff ())) f
let parse_camp f : string * QLang.camp = parse RuleParser.campmain (RuleLexer.token (string_buff ())) f
  
let parse_oql f : QLang.oql = parse OQLParser.main (OQLLexer.token (string_buff ())) f

let parse_lambda_nra f : QLang.lambda_nra = QLambdaNRA.latableify (parse LambdaNRAParser.main (LambdaNRALexer.token (string_buff ())) f)

(****************)
(* S-Expr Parse *)
(****************)

let parse_sexp f : QcertUtils.SExp.sexp = parse SExpParser.main (SExpLexer.token (string_buff ())) f
let parse_io_sexp f : QData.qdata = AstsToSExp.sexp_to_data (parse_sexp f)
let parse_camp_sexp f : QLang.camp = AstsToSExp.sexp_to_camp (parse_sexp f)
let parse_sql_sexp f : QLang.sql = AstsToSExp.sexp_to_sql (parse_sexp f)
let parse_nraenv_sexp f : QLang.nraenv_core = AstsToSExp.sexp_to_nraenv (parse_sexp f)
let parse_nnrc_sexp f : QLang.nnrc = AstsToSExp.sexp_to_nnrc (parse_sexp f)
let parse_nnrs_sexp f : QLang.nnrs = AstsToSExp.sexp_to_nnrs (parse_sexp f)
let parse_nnrs_imp_sexp f : QLang.nnrs_imp = AstsToSExp.sexp_to_nnrs_imp (parse_sexp f)
let parse_imp_qcert_sexp f : QLang.imp_qcert = AstsToSExp.sexp_to_imp_qcert (parse_sexp f)
let parse_imp_json_sexp f : QLang.imp_json = AstsToSExp.sexp_to_imp_json (parse_sexp f)
let parse_nnrcmr_sexp f : QLang.nnrcmr = AstsToSExp.sexp_to_nnrcmr (parse_sexp f)

(*******************
 * Languages Parse *
 *******************)

let parse_query l f : (string * QLang.query) =
  begin match l with
  | QcertCompiler.L_camp_rule -> let (n,r) = parse_rule f in (n, QcertCompiler.Q_camp_rule r)
  | QcertCompiler.L_camp -> let (n,c) = parse_camp f in (n, QcertCompiler.Q_camp c)
  | QcertCompiler.L_oql -> ("OQL", QcertCompiler.Q_oql (parse_oql f))
  | QcertCompiler.L_sql -> raise (Qcert_Error "SQL should be parsed from String, not lexer")
  | QcertCompiler.L_sqlpp -> raise (Qcert_Error "SQL++ should be parsed from String, not lexer")
  | QcertCompiler.L_tech_rule -> raise (Qcert_Error "Technical rule should be parsed from String, not lexer")
  | QcertCompiler.L_designer_rule -> raise (Qcert_Error "Designer rule should be parsed from binary file contents, not lexer")
  | QcertCompiler.L_lambda_nra -> ("LambdaNRA", QcertCompiler.Q_lambda_nra (parse_lambda_nra f))
  | QcertCompiler.L_nra -> raise (Qcert_Error "No parser for NRA available")
  | QcertCompiler.L_nraenv_core -> ("NRAEnvCore", QcertCompiler.Q_nraenv_core (parse_nraenv_sexp f))
  | QcertCompiler.L_nraenv -> raise (Qcert_Error "No parser for NRAEnv available")
  | QcertCompiler.L_nnrc_core -> ("NNRCCore", QcertCompiler.Q_nnrc_core (parse_nnrc_sexp f))
  | QcertCompiler.L_nnrc -> ("NNRC", QcertCompiler.Q_nnrc (parse_nnrc_sexp f))
  | QcertCompiler.L_nnrs_core -> ("NNRSCore", QcertCompiler.Q_nnrs_core (parse_nnrs_sexp f)) (* XXX TODO: check is core XXX *)
  | QcertCompiler.L_nnrs -> ("NNRS", QcertCompiler.Q_nnrs (parse_nnrs_sexp f))
  | QcertCompiler.L_nnrs_imp -> ("NNRSimp", QcertCompiler.Q_nnrs_imp (parse_nnrs_imp_sexp f))
  | QcertCompiler.L_imp_qcert -> ("ImpQcert", QcertCompiler.Q_imp_qcert (parse_imp_qcert_sexp f))
  | QcertCompiler.L_imp_json -> ("ImpJson", QcertCompiler.Q_imp_json (parse_imp_json_sexp f))
  | QcertCompiler.L_nnrcmr -> ("NNRCMR", QcertCompiler.Q_nnrcmr (parse_nnrcmr_sexp f))
  | QcertCompiler.L_dnnrc -> raise (Qcert_Error "No parser for DNNRC available")
  | QcertCompiler.L_dnnrc_typed -> raise (Qcert_Error "No parser for typed DNNRC available")
  | QcertCompiler.L_js_ast -> raise (Qcert_Error "No parser for Javascript AST available")
  | QcertCompiler.L_javascript -> raise (Qcert_Error "No parser for Javascript available")
  | QcertCompiler.L_java -> raise (Qcert_Error "No parser for Java available")
  | QcertCompiler.L_spark_df -> raise (Qcert_Error "No parser for Spark (Dataframe) available")
  | QcertCompiler.L_error err ->
      let err = string_of_char_list err in
      raise (Qcert_Error ("No parser for Error language available: "^err))
  end
