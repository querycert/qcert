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
open DataUtil
open Compiler.EnhancedCompiler

type schema_content =
    ((string * string) list
       * string
       * (string * string) list
       * (string * rtype_content) list)

(* Data utils for the Camp evaluator and compiler *)

let make_brand_relation (br:  (string * string) list) = 
  List.map (fun xy -> (Util.char_list_of_string (fst xy), Util.char_list_of_string (snd xy))) br

let lookup_brand_type (brand_type:string) type_defs =
  try
    List.assoc brand_type type_defs
  with
  | Not_found -> raise (Failure ("Type: " ^ brand_type ^ " not found in type defs list"))
    
let rtype_content_to_rtype (br: (string * string) list) (j:rtype_content) =
  match RType.json_to_rtype_with_fail (make_brand_relation br) j with
  | None -> raise (Failure ("type parsing failed for JSON:" ^ (Util.string_of_char_list (Data.jsonToJS ['"'] j))))
  | Some t -> t

let make_brand_context (br: (string * string) list) brand_types (type_defs : (string * rtype_content) list) =
  List.map (fun (x,y) -> (Util.char_list_of_string x, rtype_content_to_rtype br (lookup_brand_type y type_defs))) brand_types
    
let model_content_to_model (br: (string * string) list) (mc: model_content) : RType.brand_model option =
  let (model_name, brand_types, type_defs) = mc in
  let brand_relation = make_brand_relation br in
  let brand_context = make_brand_context br brand_types type_defs in
  RType.make_brand_model brand_relation brand_context

let extract_schema io =
  let (_,hierarchy,_,model,wmType) = DataUtil.get_io_content (Some io) in
  let (modelName,brandTypes,typeDefs) = DataUtil.get_model_content model in
  ((DataUtil.build_hierarchy hierarchy,modelName,brandTypes,typeDefs),wmType)

let process_schema (hierarchy,modelName,brandTypes,typeDefs) wmType =
  let bm =
    match model_content_to_model hierarchy (modelName,brandTypes,typeDefs) with
    | Some bm -> bm
    | None -> raise (Failure "...Brand model creation failed")
  in
  let wmTypeC =
    match RType.camp_type_uncoll bm (rtype_content_to_rtype hierarchy wmType) with
    | Some wmTypeC -> wmTypeC
    | None -> raise (Failure "WMType isn't a collection")
  in
  (bm,wmTypeC)
	
