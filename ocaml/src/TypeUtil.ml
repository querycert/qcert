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
open DataUtil
open Compiler.EnhancedCompiler

type io_schema = {
    io_brand_model : (string * string) list;
    io_name : string;
    io_brand_type : (string * string) list;
    io_type_definitions : (string * rtype_content) list;
  }

type schema = {
    sch_brand_model : RType.brand_model;
    sch_camp_type : RType.camp_type;
    sch_foreign_typing : Compiler.foreign_typing;
    sch_io_schema : io_schema option;
  }

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
  let (_, hierarchy, _, model, wmType) = DataUtil.get_io_content (Some io) in
  let (modelName, brandTypes, typeDefs) = DataUtil.get_model_content model in
  let sch =
    { io_brand_model = DataUtil.build_hierarchy hierarchy;
      io_name = modelName;
      io_brand_type = brandTypes;
      io_type_definitions = typeDefs; }
  in
  (sch, wmType)

let process_schema io_sch wmType =
  let hierarchy, modelName, brandTypes, typeDefs =
    (io_sch.io_brand_model, io_sch.io_name, io_sch.io_brand_type, io_sch.io_type_definitions)
  in
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


(* The only functions that should be exported *)

let empty_schema =
  let brand_model = RType.empty_brand_model () in
  let camp_type = RType.bottom brand_model.Compiler.brand_model_relation in (* XXX TODO: ask Jerome XXX *)
  let foreign_typing = Enhanced.Model.foreign_typing brand_model in
  { sch_brand_model = brand_model;
    sch_camp_type = camp_type;
    sch_foreign_typing = foreign_typing;
    sch_io_schema = None; }

let schema_of_io_json (io:Data.json) =
  let (io_schema, wmType) = extract_schema io in
  let bm, ct = process_schema io_schema wmType in
  { sch_brand_model = bm;
    sch_camp_type = ct;
    sch_foreign_typing = Enhanced.Model.foreign_typing bm;
    sch_io_schema = Some io_schema; }
