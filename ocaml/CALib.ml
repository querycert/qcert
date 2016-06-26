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

(* This is main interface for CALib, the CAMP Compiler library *)

open Util
open ConfigUtil
open ParseString
open CloudantUtil
open Stats
open DisplayUtil
open FrontUtil
open Compiler.EnhancedCompiler


(* Abstract AST types *)

type camp = Asts.camp
type nraenv = Asts.algenv
type nnrc = Asts.nrc
type dnnrc = Asts.dnrc
type nnrcmr = Asts.nrcmr
type cldmr = Asts.cldmr

let dlocal_conv l =
  if l then Compiler.Vlocal else Compiler.Vdistr

let dvar_conv x =
  (Util.char_list_of_string x, Compiler.Vdistr)
    
(*
 *  Frontend section
 *)

(* From source to CAMP *)

let rule_to_camp (s:string) : camp =
  let (_,op) = camp_of_rule_string s in op

(* From camp to NRAEnv *)

let camp_to_nraenv (c:camp) =
  alg_of_camp c

(* From source to NRAEnv *)

let rule_to_nraenv (s:string) : nraenv =
  let (_,op) = alg_of_rule_string s in op

let oql_to_nraenv (s:string) : nraenv =
  let (_,op) = alg_of_oql_string s in op

(*
 *  Core compiler section
 *)

(* Translations *)

let translate_nraenv_to_nnrc (op:nraenv) : nnrc = CompCore.translate_nraenv_to_nnrc op
let translate_nnrc_to_nnrcmr (n:nnrc) : nnrcmr = CompCore.translate_nnrc_to_nnrcmr_chain n
let translate_nnrc_to_dnnrc (tenv: string list) (n:nnrc) : dnnrc =
  let tenv = List.map dvar_conv tenv in
  CompCore.translate_nnrc_to_dnnrc tenv n

(* NRAEnv Optimizer *)
let optimize_nraenv (op:nraenv) =
  CompCore.toptimize_algenv_typed_opt op

(* NNRC Optimizer *)
let optimize_nnrc (n:nnrc) =
  CompCore.trew_nnrc_typed_opt n

(* NNRCMR Optimizer *)
let optimize_nnrcmr (n:nnrcmr) =
  let (vars,n) = n in
  (vars, CompCore.trew_nnrcmr_typed_opt n)

let optimize_nnrcmr_for_cloudant (n:nnrcmr) =
  let (vars,n) = n in
  (vars,CompBack.nrcmr_to_nrcmr_prepared_for_cldmr vars n)

let optimize_nnrcmr_for_spark (n:nnrcmr) =
  let (vars,n) = n in
  (vars,CompBack.nrcmr_to_nrcmr_prepared_for_spark vars n)

(* For convenience *)
(* Note: This includes optimization phases *)

let compile_nraenv_to_nnrc (op:nraenv) =
  CompCore.tcompile_nraenv_to_nnrc_typed_opt op
let compile_nraenv_to_nnrcmr (op:nraenv) =
  CompCore.tcompile_nraenv_to_nnrcmr_chain_typed_opt op


(*
 *  Backend section
 *)

let nnrc_to_js (n:nnrc) =
  string_of_char_list (CompBack.nrc_to_js_code_gen n)
let nnrc_to_java (basename:string) (imports:string) (n:nnrc) =
  string_of_char_list (CompBack.nrc_to_java_code_gen (Util.char_list_of_string basename) (Util.char_list_of_string imports) n)
let nnrcmr_to_spark (nrule:string) (n:nnrcmr) =
  string_of_char_list (CompBack.mrchain_to_spark_code_gen (Util.char_list_of_string nrule) (fst n) (snd n))

let translate_nnrcmr_to_cldmr (n:nnrcmr) : cldmr =
  CloudantUtil.cloudant_translate_no_harness n

let cldmr_to_cloudant (prefix:string) (nrule:string) (cl:cldmr) : string =
  CloudantUtil.cloudant_code_gen_no_harness (idioticize prefix nrule) cl

(* For convenience *)
      
let compile_nraenv_to_js (op:nraenv) : string =
  string_of_char_list (CompBack.nrc_to_js_code_gen (CompCore.tcompile_nraenv_to_nnrc_typed_opt op))

let compile_nraenv_to_java (basename:string) (imports:string) (op:nraenv) : string =
  string_of_char_list (CompBack.nrc_to_java_code_gen (Util.char_list_of_string basename) (Util.char_list_of_string imports) (CompCore.tcompile_nraenv_to_nnrc_typed_opt op))

let compile_nraenv_to_spark (nrule:string) (op:nraenv) : string =
  let (env_var,mr) = CompCore.tcompile_nraenv_to_nnrcmr_chain_typed_opt op in
  string_of_char_list (CompBack.mrchain_to_spark_code_gen_with_prepare (Util.char_list_of_string nrule) env_var mr)

let compile_nraenv_to_cloudant (prefix:string) (nrule:string) (op:nraenv) : string =
  cloudant_compile_no_harness_from_nra (idioticize prefix nrule) op

let compile_nnrcmr_to_cloudant (prefix:string) (nrule:string) (n:nnrcmr) : string =
  cloudant_compile_no_harness_from_nnrcmr (idioticize prefix nrule) n
  
(*
 *  ASTs support
 *)

(* Import/Export ASTs *)
(* WARNING: Not supported yet *)

(* Import/Export ASTs *)

let export_camp (p:camp) = raise (CACo_Error "CAMP export not implemented")
let import_camp (ps:string) = raise (CACo_Error "CAMP import not implemented")

let export_nraenv (op:nraenv) = DisplayUtil.nra_to_sexp_string op
let import_nraenv (ops:string) = DisplayUtil.sexp_string_to_nra ops

let export_nnrc (n:nnrc) = DisplayUtil.nrc_to_sexp_string n
let import_nnrc (ns:string) = DisplayUtil.sexp_string_to_nrc ns

let export_nnrcmr (n:nnrcmr) = DisplayUtil.nrcmr_to_sexp_string n
let import_nnrcmr (ns:string) = DisplayUtil.sexp_string_to_nrcmr ns

let export_cldmr (n:cldmr) = DisplayUtil.cldmr_to_sexp_string n
let import_cldmr (ns:string) = DisplayUtil.sexp_string_to_cldmr ns


(* Pretties *)

let pretty_nraenv (greek:bool) (margin:int) (op:nraenv) = PrettyIL.pretty_nraenv greek margin op
let pretty_nnrc (greek:bool) (margin:int) (n:nnrc) = PrettyIL.pretty_nnrc greek margin n
let pretty_nnrcmr_for_spark (greek:bool) (margin:int) (nmr:nnrcmr) =
  let (env_var, opt_nnrcmr) = nmr in
  PrettyIL.pretty_nnrcmr greek margin (CompBack.nrcmr_to_nrcmr_prepared_for_spark env_var opt_nnrcmr)
let pretty_nnrcmr_for_cloudant (greek:bool) (margin:int) (nmr:nnrcmr) =
  let (env_var, opt_nnrcmr) = nmr in
  PrettyIL.pretty_nnrcmr greek margin (CompBack.nrcmr_to_nrcmr_prepared_for_cldmr env_var opt_nnrcmr)

(* Options *)

let set_optim_trace = Logger.set_trace
let unset_optim_trace = Logger.unset_trace

