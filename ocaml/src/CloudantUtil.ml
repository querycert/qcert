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

(* Some Cloudant Utils *)

open Util
open Compiler.EnhancedCompiler

(* Cloudant format *)

type cld_config =
    { mutable prefix : string;
      mutable harness : string }

let default_cld_config () =
  { prefix = "";
    harness = "" }

let get_prefix conf = conf.prefix
let set_prefix conf s = conf.prefix <- s

(* Javascript harness (for inlining in Cloudant) *)

let print_hierarchy d = Util.string_of_char_list (QData.dataToJS (Util.char_list_of_string "\"") (QData.json_to_data [] d))

let fix_harness harness h =
  let hs =
    try print_hierarchy h with
    | _ -> "[]"
  in
  let harness_with_inh = Str.global_replace (Str.regexp "%INHERITANCE%") hs harness in
  let s1 = Str.global_replace (Str.regexp "\t") " " harness_with_inh in
  let s2 = Str.global_replace (Str.regexp "\"") "\\\"" s1 in
  let s3 = Str.global_replace (Str.regexp Util.os_newline) "\\n" s2 in
  s3

let get_harness conf = conf.harness
let set_harness conf f = conf.harness <- Util.string_of_file f

(* Cloudant stuff *)

let idioticize pref dbname =
  String.lowercase (pref ^ dbname)

let add_harness_to_designdoc harness h (db,dd) =
  let dbname = (string_of_char_list db) in
  let designdoc = string_of_char_list dd in
  let harnessed_designdoc = Str.global_replace (Str.regexp "%HARNESS%") (fix_harness harness h) designdoc in
  (char_list_of_string dbname, char_list_of_string harnessed_designdoc)

let stringify_designdoc (db,dd) =
  let dbname = string_of_char_list db in
  let designdoc = string_of_char_list dd in
  (dbname, designdoc)

(* Java equivalent: CloudantBackend.makeOneDesign *)
let makeOneDesign (db,dd) : string =
  "{ \"dbname\": \"" ^ db ^ "\",\n  \"design\":\ " ^ dd ^ " }"

(* Java equivalent: CloudantBackend.makeOneInput *)
let makeOneInput (input:char list) =
  "\"" ^ (Util.string_of_char_list input) ^ "\""

(* Java equivalent: CloudantBackend.makeLastInputs *)
let makeLastInputs (last_inputs:char list list) =
  "[ " ^ (String.concat ", " (List.map makeOneInput last_inputs)) ^ " ]"

(* Java equivalent: CloudantBackend.makeTopCld *)
let makeTopCld dbs last last_inputs : string =
  "{ \"designs\": " ^ dbs ^ ",\n  \"post\":\ \"" ^ last ^ "\",\n \"post_input\":\ " ^ (makeLastInputs last_inputs) ^ " }"

(* Java equivalent: CloudantBackend.fold_design *)
let fold_design (dds:(string * string) list) (last_expr:string) (last_inputs: char list list) : string =
  makeTopCld
    ("[ " ^ (String.concat ",\n" (List.map makeOneDesign dds)) ^ " ]")
    last_expr
    last_inputs

let cloudant_compile_from_nra harness nrule op h =
  let mr = QDriver.nraenv_optim_to_nnrc_optim_to_nnrcmr_comptop_optim op in
  let (design_docs, (last_expr, last_inputs)) = QDriver.cldmr_to_cloudant (char_list_of_string nrule) [] (QDriver.nnrcmr_to_cldmr [] mr) in
  let harnessed_design_docs = List.map (fun doc -> stringify_designdoc (add_harness_to_designdoc harness h doc)) design_docs in
  fold_design harnessed_design_docs (Util.string_of_char_list last_expr) last_inputs

let cloudant_compile_from_nnrcmr harness nrule nnrcmr h =
  let mr = nnrcmr in
  let (design_docs, (last_expr, last_inputs)) = QDriver.cldmr_to_cloudant (char_list_of_string nrule) [] (QDriver.nnrcmr_to_cldmr [] mr) in
  let harnessed_design_docs = List.map (fun doc -> stringify_designdoc (add_harness_to_designdoc harness h doc)) design_docs in
  fold_design harnessed_design_docs (Util.string_of_char_list last_expr) last_inputs

let cloudant_compile_no_harness_from_nra nrule op =
  let mr = QDriver.nraenv_optim_to_nnrc_optim_to_nnrcmr_comptop_optim op in
  let (design_docs, (last_expr, last_inputs)) = QDriver.cldmr_to_cloudant (char_list_of_string nrule) [] (QDriver.nnrcmr_to_cldmr [] mr) in
  fold_design (List.map stringify_designdoc design_docs) (Util.string_of_char_list last_expr) last_inputs

let cloudant_compile_no_harness_from_nnrcmr nrule nnrcmr =
  let (design_docs, (last_expr, last_inputs)) = QDriver.cldmr_to_cloudant (char_list_of_string nrule) [] (QDriver.nnrcmr_to_cldmr [] nnrcmr) in
  fold_design (List.map stringify_designdoc design_docs) (Util.string_of_char_list last_expr) last_inputs

let cloudant_translate_no_harness nnrcmr =
  QDriver.nnrcmr_prepared_to_cldmr [] nnrcmr

(* Java equivalent: CloudantBackend.generateCloudantDesign *)
let cloudant_code_gen_no_harness nrule cldmr =
  let (design_docs, (last_expr, last_inputs)) = QDriver.cldmr_to_cloudant (char_list_of_string nrule) [] cldmr in
  fold_design (List.map stringify_designdoc design_docs) (Util.string_of_char_list last_expr) last_inputs

(* Important functions *)

let add_harness harness h ((design_docs, (last_expr, last_inputs)): QLang.cloudant) : QLang.cloudant =
  let harnessed_design_docs = List.map (add_harness_to_designdoc harness h) design_docs in
  (harnessed_design_docs, (last_expr, last_inputs))

let string_of_cloudant (design_docs, (last_expr, last_inputs)) =
  fold_design (List.map stringify_designdoc design_docs) (Util.string_of_char_list last_expr) last_inputs
