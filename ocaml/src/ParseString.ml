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
open ParseUtil
open Compiler.EnhancedCompiler

(*****************)
(* Generic Parse *)
(*****************)

let parse_string p_fun s =
    let buf = Lexing.from_string s in
    try
      p_fun buf
    with
    | CACo_Error msg -> raise (CACo_Error msg)
    | LexError msg ->
	Printf.fprintf stderr "[%s] in string%!\n" msg; raise (CACo_Error ("Parse error ["^ msg ^"] in string [" ^ s ^ "]"))
    | _ ->
	Printf.fprintf stderr "Error in string%!\n"; raise (CACo_Error ("Parse error [???] in string"))
  

(******************)
(* Specific Parse *)
(******************)

let parse_io_from_string s : Data.json = parse_string parse_io s
let parse_json_from_string s : Data.json = parse_string parse_json s

let parse_rule_from_string s : string * CompDriver.query = parse_string parse_rule s
let parse_camp_from_string s : CompDriver.camp = parse_string parse_camp s
  
let parse_oql_from_string s : CompDriver.oql = parse_string parse_oql s

(****************)
(* S-Expr Parse *)
(****************)

let parse_sexp_from_string s : SExp.sexp = parse_string parse_sexp s
let parse_io_sexp_from_string s : Data.data = parse_string parse_io_sexp s
let parse_camp_sexp_from_string s : CompDriver.camp = parse_string parse_camp_sexp s
let parse_nraenv_sexp_from_string s : CompDriver.nraenv = parse_string parse_nraenv_sexp s
let parse_nnrc_sexp_from_string s : CompDriver.nnrc = parse_string parse_nnrc_sexp s
let parse_nnrcmr_sexp_from_string s : CompDriver.nnrcmr = parse_string parse_nnrcmr_sexp s
let parse_cldmr_sexp_from_string s : CompDriver.cldmr = parse_string parse_cldmr_sexp s

(*******************
 * Languages Parse *
 *******************)

let parse_query_from_string l s : string * CompDriver.query =
  parse_string (parse_query l) s

