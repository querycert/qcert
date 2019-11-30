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

open QcertExtracted
open Util
open LexUtil
open ParseUtil

open QcertCompiler.EnhancedCompiler

(*****************)
(* Generic Parse *)
(*****************)

let parse_file p_fun f =
  let ic = open_in f in
  let buf = Lexing.from_channel ic in
  begin try
    let res = p_fun buf in
    close_in ic; res
  with
  | Qcert_Error msg -> raise (Qcert_Error msg)
  | LexError msg ->
      close_in ic;
      Printf.fprintf stderr "[%s] in file %s%!\n" msg f; raise (Qcert_Error ("Parse error in file " ^ f))
  | _ ->
      close_in ic;
      Printf.fprintf stderr "Error in file %s%!\n" f; raise (Qcert_Error ("Parse error in file " ^ f))
  end

(******************)
(* Specific Parse *)
(******************)

let parse_io_from_file f : QData.json = parse_file parse_io f
let parse_json_from_file f : QData.json = parse_file parse_json f

let parse_rule_from_file f : string * QLang.camp_rule = parse_file parse_rule f
let parse_camp_from_file f : string * QLang.camp = parse_file parse_camp f
  
let parse_oql_from_file f : QLang.oql = parse_file parse_oql f


(****************)
(* S-Expr Parse *)
(****************)

let parse_sexp_from_file s : SExp.sexp = parse_file parse_sexp s
let parse_io_sexp_from_file s : QData.qdata = parse_file parse_io_sexp s
let parse_camp_sexp_from_file s : QLang.camp = parse_file parse_camp_sexp s
let parse_nraenv_sexp_from_file s : QLang.nraenv_core = parse_file parse_nraenv_sexp s
let parse_nnrc_sexp_from_file s : QLang.nnrc = parse_file parse_nnrc_sexp s
let parse_nnrs_sexp_from_file s : QLang.nnrs = parse_file parse_nnrs_sexp s
let parse_nnrcmr_sexp_from_file s : QLang.nnrcmr = parse_file parse_nnrcmr_sexp s

(*******************
 * Languages Parse *
 *******************)

let parse_query_from_file l s : string * QLang.query =
  parse_file (parse_query l) s

