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
open Compiler.EnhancedCompiler

(* Data utils for the Camp evaluator and compiler *)

type serialization_format =
  | META
  | ENHANCED


type io_json = QData.json

type io_input = QData.json
type io_output = QData.json
type io_schema = QData.json
type io_hierarchy = QData.json
type io_model = QData.json
type io_globals = QData.json

type rtype_content = QData.json
type vrtype_content = QData.json

type content_input = (char list * QData.data) list
type content_output = QData.data list

type content_hierarchy = (char list * char list) list
type content_brandTypes = (string * string) list
type content_typeDefs = (string * rtype_content) list
type content_globals = (string * vrtype_content) list
type content_schema = content_hierarchy * content_brandTypes * content_typeDefs * content_globals


let get_field name r =
  List.assoc (Util.char_list_of_string name) r

let get_field_opt name r =
  begin try
    Some (List.assoc (Util.char_list_of_string name) r)
  with
  | Not_found -> None
  end

let get_field_defaults name r d =
  begin try
    List.assoc (Util.char_list_of_string name) r
  with
  | Not_found -> d
  end

let missing_input_default = QData.jobject []  (* Empty object i.e., no input variables *)
let missing_output_default = QData.jarray []  (* Empty array i.e., empty result *)
let missing_schema_default = QData.jobject [] (* Empty object i.e., no schema *)
    
let get_io_components (od:QData.json option) : QData.json * QData.json * QData.json =
  begin match od with
  | Some d ->
      begin
	try
	  match d with
	  | Compiler.Jobject r ->
	      let input = get_field_defaults "input" r missing_input_default in
	      let output = get_field_defaults "output" r missing_output_default in
	      let schema = get_field_defaults "schema" r missing_schema_default in
	      (input,
	       output,
	       schema)
	  | _ ->
	      raise Not_found
	with
	| _ ->
	    raise (Qcert_Error "Ill-formed IO")
      end
  | None ->
      raise (Qcert_Error "No IO file provided")
  end

(* Schema processing first *)

let build_hierarchy h =
  match h with
  | Compiler.Jarray l ->
      List.map (function
        | Compiler.Jobject
            ( [(['s';'u';'b'], Compiler.Jstring sub); (['s';'u';'p'], Compiler.Jstring sup)]
            | [(['s';'u';'p'], Compiler.Jstring sup); (['s';'u';'b'], Compiler.Jstring sub)] ) ->
                (sub, sup)
        | _ ->
            raise (Qcert_Error "Ill-formed hierarchy"))
        l
  | _ ->
      raise (Qcert_Error "Ill-formed hierarchy")

let build_brandTypes bts =
  match bts with
  | Compiler.Jarray l ->
      List.map (function
        | Compiler.Jobject
            ( [(['b';'r';'a';'n';'d'], Compiler.Jstring brandName); (['t';'y';'p';'e';'N';'a';'m';'e'], Compiler.Jstring typeName)]
            | [(['t';'y';'p';'e';'N';'a';'m';'e'], Compiler.Jstring typeName); (['b';'r';'a';'n';'d'], Compiler.Jstring brandName)] ) ->
                (Util.string_of_char_list brandName, Util.string_of_char_list typeName)
        | _ ->
            raise (Qcert_Error "Ill-formed brandTypes"))
        l
  | _ ->
      raise (Qcert_Error "Ill-formed brandTypes")

let build_typeDefs bts =
  match bts with
  | Compiler.Jarray l ->
      List.map (function
        | Compiler.Jobject
            ( [(['t';'y';'p';'e';'N';'a';'m';'e'], Compiler.Jstring typeName); (['t';'y';'p';'e';'D';'e';'f'], typeDef)]
            | [(['t';'y';'p';'e';'D';'e';'f'], typeDef); (['t';'y';'p';'e';'N';'a';'m';'e'], Compiler.Jstring typeName)] ) ->
                (Util.string_of_char_list typeName, typeDef)
        | _ ->
            raise (Qcert_Error "Ill-formed typeDefs"))
        l
  | _ ->
      raise (Qcert_Error "Ill-formed typeDefs")

let build_globals globals =
  match globals with
  | Compiler.Jobject l ->
      List.map (function (varname, typeDef) -> (Util.string_of_char_list varname, typeDef)) l
  | _ ->
      raise (Qcert_Error "Ill-formed globals")

let missing_hierarchy_default = QData.jarray []  (* Empty array i.e., empty hierarchy *)
let missing_brandTypes_default = QData.jarray []  (* Empty array i.e., no brand types *)
let missing_typeDefs_default = QData.jarray []  (* Empty array i.e., no type definitions *)
let missing_globals_default = QData.jobject []  (* Empty object i.e., no global variables *)

let build_schema_from_json (j:QData.json) =
  begin match j with
  | Compiler.Jobject r ->
      let hierarchy = get_field_defaults "hierarchy" r missing_hierarchy_default in
      let brandTypes = get_field_defaults "brandTypes" r missing_brandTypes_default in
      let typeDefs = get_field_defaults "typeDefs" r missing_typeDefs_default in
      let globals = get_field_defaults "globals" r missing_globals_default in
      (build_hierarchy hierarchy,
       build_brandTypes brandTypes,
       build_typeDefs typeDefs,
       build_globals globals)
  | _ ->
      raise (Qcert_Error "Ill-formed model")
  end

let get_hierarchy io_schema =
  let (h,_,_,_) = build_schema_from_json io_schema in h

let build_input format od =
  let (input,_,schema) = get_io_components od in
  let h = get_hierarchy schema in
  begin match input with
  | Compiler.Jobject j ->
      begin match format with
      | META -> List.map (fun (x,y) -> (x, QData.json_to_data h y)) j
      | ENHANCED -> List.map (fun (x,y) -> (x, QData.json_enhanced_to_data h y)) j
      end
  | _ ->
      raise (Qcert_Error "Illed formed working memory: input")
  end

let build_output od =
  let (_,output,schema) = get_io_components od in
  let h = get_hierarchy schema in
  begin match output with
  | Compiler.Jarray l -> List.map (QData.json_to_data h) l (* in coq so we can prove properties on conversions *)
  | _ ->
      raise (Qcert_Error "Ill-formed expected result")
  end

let build_schema od =
  let (_,_,schema) = get_io_components od in build_schema_from_json schema
  
let display_sdata (data_dir : string option) (fname:string) (sdata:string list) (suffix:string) =
  let fpref = Filename.chop_extension fname in
  let fout_sdata = outname (target_f data_dir fpref) suffix in
  let sdata =
    String.concat "\n" sdata
  in
  make_file fout_sdata sdata
