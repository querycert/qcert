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

open QcertCompiler.EnhancedCompiler

(* Javascript js_runtime (for inlining in Cloudant) *)

let print_inheritance d =
  Util.string_of_char_list (QData.qdataToJS (Util.char_list_of_string "\"") (QData.json_to_qdata [] d))

let quote_js_runtime s h =
  let s = "var inheritance = %INHERITANCE%;\n" ^ s in
  let hs =
    try print_inheritance h with
    | _ -> "[]"
  in
  let s = Util.global_replace "%INHERITANCE%" hs s in
  let s = global_replace "\\" "\\\\" s in
  let s = global_replace "\t" " " s in
  let s = global_replace "\"" "\\\"" s in
  let s = global_replace "\n" "\\n" s in
  s

(* Cloudant stuff *)

let link_js_runtime link h s =
  let js_runtime =
    if link then QcertJsRuntime.runtime else "[HARNESS]"
  in
  Util.global_replace "%HARNESS%" (quote_js_runtime js_runtime h) s
  
let link_js_runtime_to_designdoc link h design_doc =
  let designdoc = string_of_char_list design_doc.QcertCompiler.cloudant_design_doc in
  let js_runtimeed_designdoc = link_js_runtime link h designdoc in
  { QcertCompiler.cloudant_design_inputdb = design_doc.QcertCompiler.cloudant_design_inputdb;
    QcertCompiler.cloudant_design_name = design_doc.QcertCompiler.cloudant_design_name;
    QcertCompiler.cloudant_design_doc = char_list_of_string js_runtimeed_designdoc; }
    
let stringify_designdoc design_doc =
  let dbname = string_of_char_list design_doc.QcertCompiler.cloudant_design_inputdb in
  let designdoc = string_of_char_list design_doc.QcertCompiler.cloudant_design_doc in
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

(* Important functions *)

let link_js_runtime_top link h (cloudant: QLang.cloudant) : QLang.cloudant =
  let design_docs = cloudant.QcertCompiler.cloudant_designs in
  let last_expr = cloudant.QcertCompiler.cloudant_final_expr in
  let last_inputs = cloudant.QcertCompiler.cloudant_effective_parameters in
  let js_runtimeed_design_docs =
    List.map (fun doc -> (link_js_runtime_to_designdoc link h) doc) design_docs
  in
  let js_runtimeed_last_expr =
    link_js_runtime link h (Util.string_of_char_list last_expr)
  in
  { QcertCompiler.cloudant_designs = js_runtimeed_design_docs;
    QcertCompiler.cloudant_final_expr = Util.char_list_of_string js_runtimeed_last_expr;
    QcertCompiler.cloudant_effective_parameters = last_inputs }

let string_of_cloudant cloudant =
  let design_docs = cloudant.QcertCompiler.cloudant_designs in
  let last_expr = cloudant.QcertCompiler.cloudant_final_expr in
  let last_inputs = cloudant.QcertCompiler.cloudant_effective_parameters in
  fold_design (List.map stringify_designdoc design_docs) (Util.string_of_char_list last_expr) last_inputs

