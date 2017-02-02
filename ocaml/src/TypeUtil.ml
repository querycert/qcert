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

type schema = {
    sch_brand_model : QType.brand_model;
    sch_foreign_typing : Compiler.foreign_typing;
    sch_io_schema : content_schema option;
    sch_globals : QDriver.constants_config;
  }

(* Data utils for the Camp evaluator and compiler *)

let lookup_brand_type (brand_type:string) type_defs =
  try
    List.assoc brand_type type_defs
  with
  | Not_found -> raise (Failure ("Type: " ^ brand_type ^ " not found in type defs list"))

let rtype_content_to_rtype (br: (char list * char list) list) (j:rtype_content) =
  match QType.json_to_rtype_with_fail br j with
  | None -> raise (Failure ("type parsing failed for JSON:" ^ (Util.string_of_char_list (QData.jsonToJS ['"'] j))))
  | Some t -> t

let rtype_content_to_vrtype (br: (char list * char list) list) (j:vrtype_content) =
  begin match QType.json_to_vrtype_with_fail br j with
  | None -> raise (Failure ("global type parsing failed for JSON:" ^ (Util.string_of_char_list (QData.jsonToJS ['"'] j))))
  | Some t -> t
  end

let make_brand_context (br: (char list * char list) list) brand_types (type_defs : (string * rtype_content) list) =
  List.map (fun (x,y) -> (Util.char_list_of_string x, rtype_content_to_rtype br (lookup_brand_type y type_defs))) brand_types

let content_schema_to_model (mc: content_schema) : QType.brand_model option =
  let (h, brand_types, type_defs, _) = mc in
  let brand_types =
    begin match brand_types with
    | Some bt -> build_brandTypes bt
    | None -> []
    end
  in
  let type_defs =
    begin match type_defs with
    | Some td -> build_typeDefs td
    | None -> []
    end
  in
  let brand_context = make_brand_context h brand_types type_defs in
  QType.make_brand_model h brand_context

let localization_of_string (x:char list) =
  begin match Util.string_of_char_list x with
  | "local" -> QLang.vlocal
  | "distr" -> QLang.vdistr
  | _ -> raise (Failure ("global localization parsing failed for: " ^ (Util.string_of_char_list x)))
  end
    
let content_schema_to_globals (bm:QType.brand_model) (mc: content_schema) : QDriver.constants_config =
  let (br, _, _, globals) = mc in
  let globals =
    begin match globals with
    | Some gb -> build_globals gb
    | None -> []
    end
  in
  List.map (fun (x,y) -> let (z,k) = rtype_content_to_vrtype br y in (Util.char_list_of_string x, QDriver.mk_constant_config bm (localization_of_string z) k)) globals

let process_schema mc =
  let bm = 
    begin match content_schema_to_model mc with
    | Some bm -> bm
    | None -> raise (Failure "...Brand model creation failed")
    end
  in
  let globs = content_schema_to_globals bm mc in
  (bm,globs)

(* The functions that should be exported *)

let brand_relation_of_brand_model brand_model =
  brand_model.Compiler.brand_model_relation

let empty_schema =
  let brand_model = QType.empty_brand_model () in
  let foreign_typing = Enhanced.Model.foreign_typing brand_model in
  { sch_brand_model = brand_model;
    sch_foreign_typing = foreign_typing;
    sch_io_schema = None;
    sch_globals = [] }

let schema_of_io_json (io:QData.json) =
  let content_schema = build_schema io in
  let (bm,globs) = process_schema content_schema in
  { sch_brand_model = bm;
    sch_foreign_typing = Enhanced.Model.foreign_typing bm;
    sch_io_schema = Some content_schema;
    sch_globals = globs }

let hierarchy_of_schema sc =
  begin match sc.sch_io_schema with
  | None -> []
  | Some (h,_,_,_) -> h
  end
