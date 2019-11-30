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

open QcertExtracted
open Util
open ParseUtil
open LexUtil

open QcertCompiler.EnhancedCompiler

(*****************)
(* Generic Parse *)
(*****************)

let parse_string p_fun s =
  let buf = Lexing.from_string s in
  begin try
    p_fun buf
  with
  | Qcert_Error msg -> raise (Qcert_Error msg)
  | LexError msg ->
      Printf.fprintf stderr "[%s] in string%!\n" msg; raise (Qcert_Error ("Parse error ["^ msg ^"] in string [" ^ s ^ "]"))
  | _ ->
      Printf.fprintf stderr "Error in string%!\n"; raise (Qcert_Error ("Parse error [???] in string"))
  end

(******************)
(* Specific Parse *)
(******************)

let parse_io_from_string s : QData.json = parse_string parse_io s
let parse_json_from_string s : QData.json = parse_string parse_json s

let parse_rule_from_string s : string * QLang.camp_rule = parse_string parse_rule s
let parse_camp_from_string s : string * QLang.camp = parse_string parse_camp s

let parse_oql_from_string s : QLang.oql = parse_string parse_oql s

(****************)
(* S-Expr Parse *)
(****************)

let parse_sexp_from_string s : SExp.sexp = parse_string parse_sexp s
let parse_io_sexp_from_string s : QData.qdata = parse_string parse_io_sexp s
let parse_camp_sexp_from_string s : QLang.camp = parse_string parse_camp_sexp s
let parse_nraenv_sexp_from_string s : QLang.nraenv_core = parse_string parse_nraenv_sexp s
let parse_nnrc_sexp_from_string s : QLang.nnrc = parse_string parse_nnrc_sexp s
let parse_nnrs_sexp_from_string s : QLang.nnrs = parse_string parse_nnrs_sexp s
let parse_nnrcmr_sexp_from_string s : QLang.nnrcmr = parse_string parse_nnrcmr_sexp s

(*******************
 * Languages Parse *
 *******************)

let parse_tech_rule_from_string s : QLang.tech_rule =
  QCAMPRule.rule_match
    (parse_camp_sexp_from_string
       (JavaService.main "techRule2CAMP" s))
let parse_designer_rule_from_string s : QLang.designer_rule =
  QCAMPRule.rule_match
    (parse_camp_sexp_from_string
       (JavaService.main "serialRule2CAMP" (Base64.encode_string s)))

let parse_query_from_string l s : string * QLang.query =
  begin match l with
  | QcertCompiler.L_sql -> ("SQL", QcertCompiler.Q_sql (AstsToSExp.sexp_to_sql(parse_sexp_from_string (JavaService.main "parseSQL" s))))
  | QcertCompiler.L_sqlpp -> ("SQLPP", QcertCompiler.Q_sqlpp (AstsToSExp.sexp_to_sqlpp(parse_sexp_from_string (JavaService.main "parseSQLPP" s))))
  | QcertCompiler.L_tech_rule -> ("TechRule", QcertCompiler.Q_tech_rule (parse_tech_rule_from_string s))
  | QcertCompiler.L_designer_rule -> ("DesignerRule", QcertCompiler.Q_designer_rule (parse_designer_rule_from_string s))
  | _ ->  parse_string (parse_query l) s
  end
