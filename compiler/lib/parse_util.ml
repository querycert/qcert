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

(* This module contains parsing utilities *)

open Util
open Lex_util
open CompLang
open EnhancedCompiler.EnhancedCompiler

open Imp_ejson_parser

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


let parse_io f : QData.json = parse Data_parser.main (Data_lexer.token (string_buff ())) f
let parse_json f : QData.json = parse Data_parser.main (Data_lexer.token (string_buff ())) f

let parse_rule f : string * QLang.camp_rule = parse Rule_parser.rulemain (Rule_lexer.token (string_buff ())) f
let parse_camp f : string * QLang.camp = parse Rule_parser.campmain (Rule_lexer.token (string_buff ())) f
  
let parse_oql f : QLang.oql = parse Oql_parser.main (Oql_lexer.token (string_buff ())) f

let parse_lambda_nra f : QLang.lambda_nra = QLambdaNRA.latableify (parse Lambda_nra_parser.main (Lambda_nra_lexer.token (string_buff ())) f)

let parse_imp_ejson f : QLang.imp_ejson = parse Imp_ejson_parser.main (Imp_ejson_lexer.token (string_buff ())) f

(****************)
(* S-Expr Parse *)
(****************)

let parse_sexp f : Sexp.sexp = parse Sexp_parser.main (Sexp_lexer.token (string_buff ())) f
let parse_io_sexp f : QData.qdata = Ast_to_sexp.sexp_to_data (parse_sexp f)
let parse_camp_sexp f : QLang.camp = Ast_to_sexp.sexp_to_camp (parse_sexp f)
let parse_sql_sexp f : QLang.sql = Ast_to_sexp.sexp_to_sql (parse_sexp f)
let parse_nraenv_sexp f : QLang.nraenv_core = Ast_to_sexp.sexp_to_nraenv (parse_sexp f)
let parse_nnrc_sexp f : QLang.nnrc = Ast_to_sexp.sexp_to_nnrc (parse_sexp f)
let parse_nnrs_sexp f : QLang.nnrs = Ast_to_sexp.sexp_to_nnrs (parse_sexp f)
let parse_nnrs_imp_sexp f : QLang.nnrs_imp = Ast_to_sexp.sexp_to_nnrs_imp (parse_sexp f)
let parse_imp_data_sexp f : QLang.imp_data = Ast_to_sexp.sexp_to_imp_data (parse_sexp f)
(* let parse_imp_ejson_sexp f : QLang.imp_ejson = Ast_to_sexp.sexp_to_imp_ejson (parse_sexp f) *)
let parse_nnrcmr_sexp f : QLang.nnrcmr = Ast_to_sexp.sexp_to_nnrcmr (parse_sexp f)

(*******************
 * Languages Parse *
 *******************)

let parse_query l f : (string * QLang.query) =
  begin match l with
  | L_camp_rule -> let (n,r) = parse_rule f in (n, Q_camp_rule r)
  | L_camp -> let (n,c) = parse_camp f in (n, Q_camp c)
  | L_oql -> ("OQL", Q_oql (parse_oql f))
  | L_sql -> raise (Qcert_Error "SQL should be parsed from String, not lexer")
  | L_sqlpp -> raise (Qcert_Error "SQL++ should be parsed from String, not lexer")
  | L_tech_rule -> raise (Qcert_Error "Technical rule should be parsed from String, not lexer")
  | L_designer_rule -> raise (Qcert_Error "Designer rule should be parsed from binary file contents, not lexer")
  | L_lambda_nra -> ("LambdaNRA", Q_lambda_nra (parse_lambda_nra f))
  | L_nra -> raise (Qcert_Error "No parser for NRA available")
  | L_nraenv_core -> ("NRAEnvCore", Q_nraenv_core (parse_nraenv_sexp f))
  | L_nraenv -> raise (Qcert_Error "No parser for NRAEnv available")
  | L_nnrc_core -> ("NNRCCore", Q_nnrc_core (parse_nnrc_sexp f))
  | L_nnrc -> ("NNRC", Q_nnrc (parse_nnrc_sexp f))
  | L_nnrs_core -> ("NNRSCore", Q_nnrs_core (parse_nnrs_sexp f)) (* XXX TODO: check is core XXX *)
  | L_nnrs -> ("NNRS", Q_nnrs (parse_nnrs_sexp f))
  | L_nnrs_imp -> ("NNRSimp", Q_nnrs_imp (parse_nnrs_imp_sexp f))
  | L_imp_data -> ("ImpData", Q_imp_data (parse_imp_data_sexp f))
  | L_imp_ejson -> ("ImpEJson", Q_imp_ejson (parse_imp_ejson f))
  | L_nnrcmr -> ("NNRCMR", Q_nnrcmr (parse_nnrcmr_sexp f))
  | L_dnnrc -> raise (Qcert_Error "No parser for DNNRC available")
  | L_dnnrc_typed -> raise (Qcert_Error "No parser for typed DNNRC available")
  | L_js_ast -> raise (Qcert_Error "No parser for Javascript AST available")
  | L_javascript -> raise (Qcert_Error "No parser for Javascript available")
  | L_java -> raise (Qcert_Error "No parser for Java available")
  | L_spark_df -> raise (Qcert_Error "No parser for Spark (Dataframe) available")
  | L_wasm_ast -> raise (Qcert_Error "No parser for WASM (Ast) available")
  | L_wasm -> raise (Qcert_Error "No parser for WASM (Binary) available")
  | L_error err ->
      let err = string_of_char_list err in
      raise (Qcert_Error ("No parser for Error language available: "^err))
  end
