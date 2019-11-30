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

open QcertExtracted
open Util
open QcertCompiler.EnhancedCompiler

open DataUtil

type schema = {
    sch_brand_model : QType.brand_model;
    sch_foreign_typing : QcertCompiler.foreign_typing;
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
  | None -> raise (Failure ("type parsing failed for JSON:" ^ (string_of_char_list (QData.jsonToJS ['"'] j))))
  | Some t -> t

let rtype_content_to_vrtype (br: (char list * char list) list) (j:vrtype_content) =
  begin match QType.json_to_vrtype_with_fail br j with
  | None -> raise (Failure ("global type parsing failed for JSON:" ^ (string_of_char_list (QData.jsonToJS ['"'] j))))
  | Some t -> t
  end

let make_brand_context (br: (char list * char list) list) brand_types (type_defs : (string * rtype_content) list) =
  List.map (fun (x,y) -> (char_list_of_string x, rtype_content_to_rtype br (lookup_brand_type y type_defs))) brand_types

let content_schema_to_model (mc: content_schema) : QType.brand_model =
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
  let brand_context = make_brand_context (fst h) brand_types type_defs in
  QcertUtil.lift_qerror (QType.make_brand_model (fst h)) brand_context

let localization_of_string (x:char list) =
  begin match string_of_char_list x with
  | "local" -> QLang.vlocal
  | "distr" -> QLang.vdistr
  | _ -> raise (Qcert_Error ("global localization parsing failed for: " ^ (string_of_char_list x)))
  end

let lift_constant_types (bm:QType.brand_model) br glb =
  let (vname,gbj) = glb in
  let (locs,gbt) = rtype_content_to_vrtype br gbj in
  let loc = localization_of_string locs in
  let t =
    begin match loc with
    | QcertCompiler.Vlocal -> gbt
    | QcertCompiler.Vdistr ->
	(* XXX We to 'uncoll' here to check that the type is a collection type and extract its content -- This is an assumption of the Compiler Driver XXX *)
	begin match QType.qtype_uncoll bm gbt with
	| None -> raise (Qcert_Error ("Type for distributed constant " ^ vname ^ " must be a collection type"))
	| Some dt -> dt
	end
    end
  in
  (char_list_of_string vname, QDriver.mk_constant_config bm loc t None)
    
let content_schema_to_globals (bm:QType.brand_model) (mc: content_schema) : QDriver.constants_config =
  let (h, _, _, globals) = mc in
  let globals =
    begin match globals with
    | Some gb -> build_globals gb
    | None -> []
    end
  in
  List.map (lift_constant_types bm (fst h)) globals
(*  List.map (fun (x,y) -> let (z,k) =  in (char_list_of_string x, QDriver.mk_constant_config bm (localization_of_string z) k)) globals *)

let process_schema mc =
  let bm = content_schema_to_model mc in
  let globs = content_schema_to_globals bm mc in
  (bm,globs)

(* The functions that should be exported *)

let brand_relation_of_brand_model brand_model =
  brand_model.QcertCompiler.brand_model_relation

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

let inheritance_of_schema sc =
  begin match sc.sch_io_schema with
  | None -> []
  | Some (h,_,_,_) -> fst h
  end

let raw_inheritance_of_schema sc =
  begin match sc.sch_io_schema with
  | None -> QcertCompiler.Jarray []
  | Some (h,_,_,_) -> snd h
  end

type content_sdata = (char list * char list) list

let get_type bm (glob_constant:QcertCompiler.constant_config) =
  let br = brand_relation_of_brand_model bm in
  begin match glob_constant.QcertCompiler.constant_localization with
  | QcertCompiler.Vlocal -> glob_constant.QcertCompiler.constant_type
  | QcertCompiler.Vdistr -> QType.bag br glob_constant.QcertCompiler.constant_type
  end

let get_constant_name (glob_name:char list) (globs:QDriver.constants_config) : QcertCompiler.constant_config =
  begin try
    List.assoc glob_name globs
  with
  | _ ->
      raise (Failure ("No type declared for constant: " ^ (string_of_char_list glob_name)))
  end

let proc_glob bm (globs:QDriver.constants_config) globd =
  let (glob_name, glob_data) = globd in
  let glob = get_constant_name glob_name globs in
  let glob_type = get_type bm glob in
  begin match QType.data_to_sjson bm glob_data glob_type with
  | Some sdata -> (glob_name,sdata)
  | None -> raise (Failure ("Could not process sdata for constant: " ^ (string_of_char_list glob_name)))
  end
  
let content_sdata_of_data (sc:schema) (data:DataUtil.content_input) =
  let bm = sc.sch_brand_model in
  let globs = sc.sch_globals in
  List.map (proc_glob bm globs) data

