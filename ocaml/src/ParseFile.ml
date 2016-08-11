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
open Asts


(*****************)
(* Generic Parse *)
(*****************)

let parse_file p_fun f =
    let ic = open_in f in
    let buf = Lexing.from_channel ic in
    try
      let res = p_fun buf in
      close_in ic; res
    with
    | CACo_Error msg -> raise (CACo_Error msg)
    | LexError msg ->
	close_in ic;
	Printf.fprintf stderr "[%s] in file %s%!\n" msg f; raise (CACo_Error ("Parse error in file " ^ f))
    | _ ->
	close_in ic;
	Printf.fprintf stderr "Error in file %s%!\n" f; raise (CACo_Error ("Parse error in file " ^ f))
  

(******************)
(* Specific Parse *)
(******************)

let parse_io_from_file f : io_ast = parse_file parse_io f
let parse_json_from_file f : json_ast = parse_file parse_json f

let parse_rule_from_file f : string * rORc_ast = parse_file parse_rule f
let parse_camp_from_file f : camp = parse_file parse_camp f
  
let parse_oql_from_file f : oql_ast = parse_file parse_oql f


(****************)
(* S-Expr Parse *)
(****************)

let parse_sexp_from_file s : SExp.sexp = parse_file parse_sexp s
let parse_io_sexp_from_file s : data_ast = parse_file parse_io_sexp s
let parse_camp_sexp_from_file s : camp = parse_file parse_camp_sexp s
let parse_nraenv_sexp_from_file s : nraenv = parse_file parse_nraenv_sexp s
let parse_nnrc_sexp_from_file s : nnrc = parse_file parse_nnrc_sexp s
let parse_nnrcmr_sexp_from_file s : nnrcmr = parse_file parse_nnrcmr_sexp s
let parse_cldmr_sexp_from_file s : cldmr = parse_file parse_cldmr_sexp s

