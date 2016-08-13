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

open Util
open ConfigUtil
open ParseUtil
open CloudantUtil
open DisplayUtil
open FrontUtil
open Compiler.EnhancedCompiler

module C = CompStat


(* Set configuration *)
let args conf =
  [ ("-source", Arg.String (change_source (get_comp_lang_config conf)), "(Rule/OQL)");
    (* ("-display-ascii", Arg.Unit (PrettyIL.set_ascii (get_pretty_config conf)), "Avoid unicode symbols"); *)
    ("-display-margin", Arg.Int (PrettyIL.set_margin (get_pretty_config conf)), "Set right margin for pretty printer"); ]

let anon_args conf f = set_comp_input conf f

let usage = "CAPp [-source language] rule1 rule2 ..."

let conf =
  let conf = default_comp_config () in
  Arg.parse (args conf) (anon_args conf) usage;
  conf

(* *)

type nnrc_pp =
    { nnrc_no_optim_string : string;
      nnrc_optim_string : string; }

type nra_pp =
    { nra_no_optim : nra_pp_body;
      nra_optim : nra_pp_body; }
and nra_pp_body =
    { nra_string : string;
      nra_to_nnrc : nnrc_pp; }

type nraenv_pp =
    { nraenv_no_optim : nraenv_pp_body;
      nraenv_optim : nraenv_pp_body;
      nraenv_compiler : nnrc_pp; }
and nraenv_pp_body =
    { nraenv_string : string;
      nraenv_to_nnrc : nnrc_pp;
      nraenv_to_nra : nra_pp; }

type pat_pp =
    { pat_string : string;
      pat_to_nraenv : nraenv_pp;
      pat_to_nra : nra_pp; }
type rule_pp =
    { rule_string : string;
      rule_to_nraenv : nraenv_pp;
      rule_to_nra : nra_pp; }
type oql_pp =
    { oql_string : string;
      oql_to_nraenv : nraenv_pp; }

type pp =
  | Pp_rule of string * rule_pp
  | Pp_pat of string * pat_pp
  | Pp_oql of string * oql_pp


let greek = false (* PrettyIL.get_charset_bool (get_pretty_config conf) *)
let margin = PrettyIL.get_margin (get_pretty_config conf)

let pretty_nnrc op = String.escaped (PrettyIL.pretty_nnrc greek margin op)
let pretty_nra op = String.escaped (PrettyIL.pretty_nraenv greek margin (C.nra_to_nraenv op))
let pretty_nraenv op = String.escaped (PrettyIL.pretty_nraenv greek margin op)

let pp_nnrc e =
  { nnrc_no_optim_string = pretty_nnrc e;
    nnrc_optim_string = pretty_nnrc (C.nnrc_optim e); }

let pp_body_nra op =
  { nra_string = pretty_nra op;
    nra_to_nnrc = pp_nnrc (C.nra_to_nnrc op); }

let pp_nra op =
  { nra_no_optim = pp_body_nra op;
    nra_optim = pp_body_nra (C.nra_optim op); }

let pp_body_nraenv op =
  { nraenv_string = pretty_nraenv op;
    nraenv_to_nnrc = pp_nnrc (C.nraenv_to_nnrc op);
    nraenv_to_nra = pp_nra (C.nraenv_to_nra op); }

let pp_nraenv op =
  { nraenv_no_optim = pp_body_nraenv op;
    nraenv_optim = pp_body_nraenv (C.nraenv_optim op);
    nraenv_compiler = pp_nnrc (C.nraenv_compiler op); }

let pp_pat p =
  { pat_string = "pat";
    pat_to_nraenv = pp_nraenv (C.pat_to_nraenv p);
    pat_to_nra = pp_nra (C.pat_to_nra p); }

let pp_rule r =
  { rule_string = "TODO";
    rule_to_nraenv = pp_nraenv (C.rule_to_nraenv r);
    rule_to_nra = pp_nra (C.rule_to_nra r); }

let pp_oql e =
  { oql_string = "TODO";
    oql_to_nraenv = pp_nraenv (C.oql_to_nraenv e); }


let pp_source conf f =
  begin
    match language_of_name (get_source_lang conf) with
    | CompDriver.L_rule ->
	let (rn,ru) = ParseFile.parse_rule_from_file f in
	begin match ru with
	| CompDriver.Q_rule ru ->
            Pp_rule (rn, pp_rule ru)
	| CompDriver.Q_camp ru ->
            Pp_pat (rn, pp_pat ru)
	| _ ->
	    raise (CACo_Error "Input language not supported")
	end
    | CompDriver.L_oql ->
	let o = ParseFile.parse_oql_from_file f in
	Pp_oql (f, pp_oql o)
    | _ ->
	raise (CACo_Error "Input language not supported")
  end


(* Printer *)

let fprint_pp_nnrc ff pp =
  Format.fprintf ff
    "{ @[\"nnrc_no_optim_string\" : \"%s\",@\n\"nnrc_optim_string\" : \"%s\"@] }"
    pp.nnrc_no_optim_string
    pp.nnrc_optim_string

let fprint_pp_nra_body ff pp =
  Format.fprintf ff
    "{ @[\"nra_string\" : \"%s\",@\n\"nra_to_nnrc\" : %a@] }"
    pp.nra_string
    fprint_pp_nnrc pp.nra_to_nnrc

let fprint_pp_nra ff pp =
  Format.fprintf ff
    "{ @[\"nra_no_optim\" : %a,@\n\"nra_optim\" : %a@] }"
    fprint_pp_nra_body pp.nra_no_optim
    fprint_pp_nra_body pp.nra_optim

let fprint_pp_nraenv_body ff pp =
  Format.fprintf ff
    "{ @[\"nraenv_string\" : \"%s\", \"nraenv_to_nnrc\" : %a, \"nraenv_to_nra\" : %a@] }"
    pp.nraenv_string
    fprint_pp_nnrc pp.nraenv_to_nnrc
    fprint_pp_nra pp.nraenv_to_nra


let fprint_pp_nraenv ff pp =
  Format.fprintf ff
    "{ @[\"nraenv_no_optim\" : %a, \"nraenv_optim\" : %a, \"nraenv_compiler\" : %a@] }"
    fprint_pp_nraenv_body pp.nraenv_no_optim
    fprint_pp_nraenv_body pp.nraenv_optim
    fprint_pp_nnrc pp.nraenv_compiler

let fprint_pp ff pp =
  begin match pp with
  | Pp_rule (f, s) ->
      Format.fprintf ff "{ @[\"rule_name\":\"%s\", \"rule_to_nraenv\": %a, \"rule_to_nra\": %a@] }"
        f
        fprint_pp_nraenv s.rule_to_nraenv
        fprint_pp_nra s.rule_to_nra
  | Pp_pat (f, s) ->
      Format.fprintf ff "{ @[\"pat_name\":\"%s\", \"pat_to_nraenv\": %a, \"pat_to_nra\": %a@] }"
        f
        fprint_pp_nraenv s.pat_to_nraenv
        fprint_pp_nra s.pat_to_nra
  | Pp_oql (f, s) ->
      Format.fprintf ff "{ @[\"rule_name\":\"%s\", \"rule_to_nraenv\": %a@] }"
        f
        fprint_pp_nraenv s.oql_to_nraenv
  end


(* Main *)

let pp_file conf f =
  if f <> "" then
    let pp = pp_source (get_comp_lang_config conf) f in
    Format.printf "%a" fprint_pp pp

let () =
  List.iter (pp_file conf) (get_comp_inputs conf)

