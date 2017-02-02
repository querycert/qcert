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
type io_brandTypes = QData.json
type io_typeDefs = QData.json
type io_globals = QData.json

type rtype_content = QData.json
type vrtype_content = QData.json

type content_input = (char list * QData.data) list
type content_output = QData.data list

type content_hierarchy = (char list * char list) list
type content_brandTypes = (string * string) list
type content_typeDefs = (string * rtype_content) list
type content_globals = (string * vrtype_content) list
type content_schema = content_hierarchy * io_brandTypes option * io_typeDefs option * io_globals option


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

let get_io_components (od:QData.json option) : QData.json option * QData.json option * QData.json option =
  begin match od with
  | Some d ->
      begin
	try
	  match d with
	  | Compiler.Jobject r ->
	      let input = get_field_opt "input" r in
	      let output = get_field_opt "output" r in
	      let schema = get_field_opt "schema" r in
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
  begin match h with
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
  end

let build_brandTypes bts =
  begin match bts with
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
  end

let build_typeDefs bts =
  begin match bts with
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
  end

let build_globals globals =
  begin match globals with
  | Compiler.Jobject l ->
      List.map (function (varname, typeDef) -> (Util.string_of_char_list varname, typeDef)) l
  | _ ->
      raise (Qcert_Error "Ill-formed globals")
  end

let missing_hierarchy_default = QData.jarray []  (* Empty array i.e., empty hierarchy *)

let build_schema (j:QData.json) =
  begin match j with
  | Compiler.Jobject r ->
      let hierarchy = get_field_defaults "hierarchy" r missing_hierarchy_default in
      let brandTypes = get_field_opt "brandTypes" r in
      let typeDefs = get_field_opt "typeDefs" r in
      let globals = get_field_opt "globals" r in
      (build_hierarchy hierarchy,
       brandTypes,
       typeDefs,
       globals)
  | _ ->
      raise (Qcert_Error "Ill-formed model")
  end

let get_hierarchy io_schema =
  let (h,_,_,_) = build_schema io_schema in h

let build_input format h input =
  begin match input with
  | Compiler.Jobject j ->
      begin match format with
      | META -> List.map (fun (x,y) -> (x, QData.json_to_data h y)) j
      | ENHANCED -> List.map (fun (x,y) -> (x, QData.json_enhanced_to_data h y)) j
      end
  | _ -> raise (Qcert_Error "Illed formed working memory: input")
  end

let build_output h output =
  begin match output with
  | Compiler.Jarray l -> List.map (QData.json_to_data h) l (* in coq so we can prove properties on conversions *)
  | _ -> raise (Qcert_Error "Ill-formed output")
  end

