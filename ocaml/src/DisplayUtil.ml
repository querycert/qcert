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

open Compiler.EnhancedCompiler
open Util
open ConfigUtil
open PrettyIL

(* Display ILs *)

let display_to_string conf modelandtype op =
  let opt_nraenv = CompCore.toptimize_algenv_typed_opt op in
  let opt_nnrc = CompCore.tcompile_nraenv_to_nnrc_typed_opt op in
  let (env_var, opt_nnrcmr) = CompCore.tcompile_nraenv_to_nnrcmr_chain_typed_opt op in
  let nnrcmr_spark = CompBack.nrcmr_to_nrcmr_prepared_for_spark env_var opt_nnrcmr in
  let nnrcmr_cldmr = CompBack.nrcmr_to_nrcmr_prepared_for_cldmr env_var opt_nnrcmr in
  let nrastring = PrettyIL.pretty_nraenv (get_charset_bool conf) (get_margin conf) opt_nraenv in
  let nrcstring = PrettyIL.pretty_nnrc (get_charset_bool conf) (get_margin conf) opt_nnrc in
  let nrcmrstring = PrettyIL.pretty_nnrcmr (get_charset_bool conf) (get_margin conf) opt_nnrcmr in
  let nrcmr_spark_string = PrettyIL.pretty_nnrcmr (get_charset_bool conf) (get_margin conf) nnrcmr_spark in
  let nrcmr_cldmr_string = PrettyIL.pretty_nnrcmr (get_charset_bool conf) (get_margin conf) nnrcmr_cldmr in
  let opt_dnrc_dataset_string =
    begin
    match modelandtype with
    | Some (brand_model, inputType) ->
       begin
	 match CompCore.tcompile_nraenv_to_dnnrc_dataset_opt
				brand_model
				(Enhanced.Model.foreign_typing brand_model)
				op
				inputType with
	 | Some ds -> PrettyIL.pretty_dnrc
			(PrettyIL.pretty_annotate_annotated_rtype
			   (get_charset_bool conf) PrettyIL.pretty_annotate_ignore)
			(PrettyIL.pretty_plug_dataset (get_charset_bool conf))
			(get_charset_bool conf) (get_margin conf) ds
	 | None -> "DNRC expression was not well typed"
       end
    | None -> "Optimized DNRC expression can't be determined without a schema"
    end
  in (nrastring,nrcstring, nrcmrstring, nrcmr_spark_string, nrcmr_cldmr_string, opt_dnrc_dataset_string)


let display_algenv_top conf modelandtype (fname,op) =
  let modelandtype' =
    begin
    match modelandtype with
    | Some bm -> Some bm
    | None ->
       begin
       match get_comp_io conf with
       | Some io ->
	  let (schema_content,wmType) = TypeUtil.extract_schema io in
	  let (brand_model,wmRType) = TypeUtil.process_schema schema_content wmType in
	  Some (brand_model, wmRType)
	| None -> None
       end
    end
    in
    let (display_nra,display_nrc,display_nrcmr,display_nrcmr_spark,display_nrcmr_cldmr, display_opt_dnrc_dataset) =
      display_to_string (get_pretty_config conf) modelandtype' op
    in
    let fpref = Filename.chop_extension fname in
    let fout_nra = outname (target_f (get_display_dir conf) fpref) (suffix_nra ()) in
    let fout_nrc = outname (target_f (get_display_dir conf) fpref) (suffix_nrc ()) in
    let fout_nrcmr = outname (target_f (get_display_dir conf) fpref) (suffix_nrcmr ()) in
    let fout_nrcmr_spark = outname (target_f (get_display_dir conf) fpref) (suffix_nrcmr_spark ()) in
    let fout_nrcmr_cldmr = outname (target_f (get_display_dir conf) fpref) (suffix_nrcmr_cldmr ()) in
    let fout_dnrc_dataset = outname (target_f (get_display_dir conf) fpref) (suffix_dnrc ()) in
    begin
      make_file fout_nra display_nra;
      make_file fout_nrc display_nrc;
      make_file fout_nrcmr display_nrcmr;
      make_file fout_nrcmr_spark display_nrcmr_spark;
      make_file fout_nrcmr_cldmr display_nrcmr_cldmr;
      make_file fout_dnrc_dataset display_opt_dnrc_dataset;
    end

(* S-expression hooks *)
      
let sexp_string_to_camp s = ParseString.parse_camp_sexp_from_string s
let camp_to_sexp_string p = SExp.sexp_to_string (Asts.camp_to_sexp p)

let sexp_string_to_nra s = ParseString.parse_nra_sexp_from_string s
let nra_to_sexp_string op = SExp.sexp_to_string (Asts.alg_to_sexp op)

let sexp_string_to_nrc s = ParseString.parse_nrc_sexp_from_string s
let nrc_to_sexp_string n = SExp.sexp_to_string (Asts.nrc_to_sexp n)

let sexp_string_to_nrcmr s = ParseString.parse_nrcmr_sexp_from_string s
let nrcmr_to_sexp_string n = SExp.sexp_to_string (Asts.nrcmr_to_sexp n)

let sexp_string_to_cldmr s = ParseString.parse_cldmr_sexp_from_string s
let cldmr_to_sexp_string n = SExp.sexp_to_string (Asts.cldmr_to_sexp n)

(* Top-level *)
    
let sexp_algenv_top conf (fname,op) =
  let opt_nnrc = CompCore.tcompile_nraenv_to_nnrc_typed_opt op in
  let display_nra = nra_to_sexp_string op in
  let display_nrc = nrc_to_sexp_string opt_nnrc in
  let (env_var, nnrcmr) = CompCore.tcompile_nraenv_to_nnrcmr_chain_typed_opt op in
  let nrcmr_spark = CompBack.nrcmr_to_nrcmr_prepared_for_spark env_var nnrcmr in
  let nrcmr_cldmr = CompBack.nrcmr_to_nrcmr_prepared_for_cldmr env_var nnrcmr in
  let display_nrcmr_spark = nrcmr_to_sexp_string (env_var,nrcmr_spark) in
  let display_nrcmr_cldmr = nrcmr_to_sexp_string (env_var,nrcmr_cldmr) in
  let fpref = Filename.chop_extension fname in
  let fout_nra = outname (target_f (get_display_dir conf) fpref) (suffix_nrasexp ()) in
  let fout_nrc = outname (target_f (get_display_dir conf) fpref) (suffix_nrcsexp ()) in
  let fout_nrcmr_spark = outname (target_f (get_display_dir conf) fpref) (suffix_nrcmr_sparksexp ()) in
  let fout_nrcmr_cldmr = outname (target_f (get_display_dir conf) fpref) (suffix_nrcmr_cldmrsexp ()) in
  begin
    make_file fout_nra display_nra;
    make_file fout_nrc display_nrc;
    make_file fout_nrcmr_spark display_nrcmr_spark;
    make_file fout_nrcmr_cldmr display_nrcmr_cldmr
  end

(* SData section *)
    
let display_sdata (conf : data_config) (fname:string) (sdata:string list) =
  let fpref = Filename.chop_extension fname in
  let fout_sdata = outname (target_f (get_data_dir conf) fpref) (suffix_sdata ()) in
  let sdata =
    String.concat "\n" sdata
  in
  make_file fout_sdata sdata

