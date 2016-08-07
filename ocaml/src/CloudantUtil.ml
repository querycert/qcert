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
open ParseUtil
open Compiler.EnhancedCompiler

(* Cloudant format *)

type cldkind =
  | Curl
  | Design

type cld_config =
    { mutable cld : cldkind;
      mutable prefix : string;
      mutable harness : string }

let default_cld_config () =
  { cld = Design;
    prefix = "";
    harness = "" }

let get_cld conf = conf.cld
let set_curl conf () = conf.cld <- Curl

let get_prefix conf = conf.prefix
let set_prefix conf s = conf.prefix <- s

(* Javascript harness (for inlining in Cloudant) *)

let print_hierarchy d = Util.string_of_char_list (Data.dataToJS (Util.char_list_of_string "\"") (Data.json_to_data [] d))

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

let add_harness harness h (db,dd) =
  let dbname = (string_of_char_list db) in
  let designdoc = string_of_char_list dd in
  let harnessed_designdoc = Str.global_replace (Str.regexp "%HARNESS%") (fix_harness harness h) designdoc in
  (dbname, harnessed_designdoc)

let dont_add_harness (db,dd) =
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

let makeOneCurl (db,dd) : string =
  "curl -X PUT \"https://fe0a4004-9ff8-4bc4-9de8-906e1831cc78-bluemix:8a67972aa73304b3b7cc9b0cc4525d2e6c26988dd08c787ae29d5d68079c0b54@fe0a4004-9ff8-4bc4-9de8-906e1831cc78-bluemix.cloudant.com/" ^ db ^ "/_design/" ^ db ^ "\" -H 'Content-type: application/json' -d '" ^ dd ^ "'"

(* Java equivalent: CloudantBackend.fold_design *)
let fold_design (dds:(string * string) list) (last_expr:string) (last_inputs: char list list) : string =
  makeTopCld
    ("[ " ^ (String.concat ",\n" (List.map makeOneDesign dds)) ^ " ]")
    last_expr
    last_inputs

let fold_curl (dds:(string * string) list) : string =
  String.concat Util.os_newline (List.map makeOneCurl dds)

let rec print_string_list = function 
    [] -> ()
  | e::l -> print_string (string_of_char_list e) ; print_string " " ; print_string_list l

let cloudant_compile_from_nra cld harness nrule op h =
  let (env_var,mr) = CompCore.tcompile_nraenv_to_nnrcmr_chain_typed_opt op in
  let (design_docs, (last_expr, last_inputs)) = (CompBack.nrcmr_to_cloudant_code_gen_with_prepare [] mr (char_list_of_string nrule)) in
  let harnessed_design_docs = List.map (add_harness harness h) design_docs in
  match cld with
  | Design -> fold_design harnessed_design_docs (Util.string_of_char_list last_expr) last_inputs
  | Curl -> fold_curl harnessed_design_docs

let cloudant_compile_from_nnrcmr cld harness nrule nnrcmr h =
  let (env_var,mr) = nnrcmr in
  let (design_docs, (last_expr, last_inputs)) = (CompBack.nrcmr_to_cloudant_code_gen_with_prepare [] mr (char_list_of_string nrule)) in
  let harnessed_design_docs = List.map (add_harness harness h) design_docs in
  match cld with
  | Design -> fold_design harnessed_design_docs (Util.string_of_char_list last_expr) last_inputs
  | Curl -> fold_curl harnessed_design_docs

let cloudant_compile_no_harness_from_nra nrule op =
  let (env_var,mr) = CompCore.tcompile_nraenv_to_nnrcmr_chain_typed_opt op in
  let (design_docs, (last_expr, last_inputs)) = (CompBack.nrcmr_to_cloudant_code_gen_with_prepare [] mr (char_list_of_string nrule)) in
  fold_design (List.map dont_add_harness design_docs) (Util.string_of_char_list last_expr) last_inputs

let cloudant_compile_no_harness_from_nnrcmr nrule nnrcmr =
  let (env_var,mr) = nnrcmr in
  let (design_docs, (last_expr, last_inputs)) = (CompBack.nrcmr_to_cloudant_code_gen_with_prepare [] mr (char_list_of_string nrule)) in
  fold_design (List.map dont_add_harness design_docs) (Util.string_of_char_list last_expr) last_inputs

let cloudant_translate_no_harness nnrcmr =
  let (env_var,mr) = nnrcmr in
  CompBack.nrcmr_to_cldmr_chain_translate [] mr

(* Java equivalent: CloudantBackend.generateCloudantDesign *)
let cloudant_code_gen_no_harness nrule cldmr =
  let (design_docs, (last_expr, last_inputs)) = CompBack.cldmr_code_gen [] cldmr (char_list_of_string nrule) in
  fold_design (List.map dont_add_harness design_docs) (Util.string_of_char_list last_expr) last_inputs
  

