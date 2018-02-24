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

open QcertCompiler.EnhancedCompiler

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

type content_input = (char list * QData.qdata) list
type content_output = QData.qdata

type content_hierarchy = (char list * char list) list
type full_content_hierarchy = (content_hierarchy * io_hierarchy)
type content_brandTypes = (string * string) list
type content_typeDefs = (string * rtype_content) list
type content_globals = (string * vrtype_content) list
type content_schema = full_content_hierarchy * io_brandTypes option * io_typeDefs option * io_globals option

(* Optimization support *)
type optim_phase =
    { mutable optim_phase_name : string;
      mutable optim_phase_iter : int;
      mutable optim_phase_optims : string list; }
type optim_language =
    { mutable optim_language_name : string;
      mutable optim_phases : optim_phase list; }
type optim_config = optim_language list

let optim_phase_from_ocaml_conf (gp: optim_phase)
    : (char list * char list list) * int =
  let phase_name = Util.char_list_of_string gp.optim_phase_name in
  let phase_iter = gp.optim_phase_iter in
  let phase_list = List.map Util.char_list_of_string gp.optim_phase_optims in
  ((phase_name, phase_list),phase_iter)
    

let get_field name r =
  begin try
    List.assoc (Util.char_list_of_string name) r
  with
  | Not_found ->
      raise (Qcert_Error ("Field " ^ name ^ " not found"))
  end
let get_string j =
  begin match j with
  | QcertCompiler.Jstring s -> Util.string_of_char_list s
  | _ ->
      raise (Qcert_Error ("JSON value not a string"))
  end
let get_field_string name r =
  begin match get_field name r with
  | QcertCompiler.Jstring s -> Util.string_of_char_list s
  | _ ->
      raise (Qcert_Error ("Field " ^ name ^ " not a string"))
  end

let get_field_string_array name r =
  begin match get_field name r with
  | QcertCompiler.Jarray l -> List.map get_string l
  | _ ->
      raise (Qcert_Error ("Field " ^ name ^ " not a string"))
  end
   
let get_field_int name r =
  begin match get_field name r with
  | QcertCompiler.Jnumber i -> i
  | _ ->
      raise (Qcert_Error ("Field " ^ name ^ " not an integer"))
  end

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
	  | QcertCompiler.Jobject r ->
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
  | QcertCompiler.Jarray l ->
      List.map (function
        | QcertCompiler.Jobject
            ( [(['s';'u';'b'], QcertCompiler.Jstring sub); (['s';'u';'p'], QcertCompiler.Jstring sup)]
        | [(['s';'u';'p'], QcertCompiler.Jstring sup); (['s';'u';'b'], QcertCompiler.Jstring sub)] ) ->
            (sub, sup)
        | _ ->
            raise (Qcert_Error "Ill-formed hierarchy"))
        l
  | _ ->
      raise (Qcert_Error "Ill-formed hierarchy")
  end

let build_brandTypes bts =
  begin match bts with
  | QcertCompiler.Jarray l ->
      List.map (function
        | QcertCompiler.Jobject
            ( [(['b';'r';'a';'n';'d'], QcertCompiler.Jstring brandName); (['t';'y';'p';'e';'N';'a';'m';'e'], QcertCompiler.Jstring typeName)]
        | [(['t';'y';'p';'e';'N';'a';'m';'e'], QcertCompiler.Jstring typeName); (['b';'r';'a';'n';'d'], QcertCompiler.Jstring brandName)] ) ->
            (Util.string_of_char_list brandName, Util.string_of_char_list typeName)
        | _ ->
            raise (Qcert_Error "Ill-formed brandTypes"))
        l
  | _ ->
      raise (Qcert_Error "Ill-formed brandTypes")
  end

let build_typeDefs bts =
  begin match bts with
  | QcertCompiler.Jarray l ->
      List.map (function
        | QcertCompiler.Jobject
            ( [(['t';'y';'p';'e';'N';'a';'m';'e'], QcertCompiler.Jstring typeName); (['t';'y';'p';'e';'D';'e';'f'], typeDef)]
        | [(['t';'y';'p';'e';'D';'e';'f'], typeDef); (['t';'y';'p';'e';'N';'a';'m';'e'], QcertCompiler.Jstring typeName)] ) ->
            (Util.string_of_char_list typeName, typeDef)
        | _ ->
            raise (Qcert_Error "Ill-formed typeDefs"))
        l
  | _ ->
      raise (Qcert_Error "Ill-formed typeDefs")
  end

let build_globals globals =
  begin match globals with
  | QcertCompiler.Jobject l ->
      List.map (function (varname, typeDef) -> (Util.string_of_char_list varname, typeDef)) l
  | _ ->
      raise (Qcert_Error "Ill-formed globals")
  end

let missing_hierarchy_default = QData.jarray []  (* Empty array i.e., empty hierarchy *)

let build_schema (j:QData.json) =
  begin match j with
  | QcertCompiler.Jobject r ->
      let hierarchy = get_field_defaults "hierarchy" r missing_hierarchy_default in
      let brandTypes = get_field_opt "brandTypes" r in
      let typeDefs = get_field_opt "typeDefs" r in
      let globals = get_field_opt "globals" r in
      ((build_hierarchy hierarchy,hierarchy),
       brandTypes,
       typeDefs,
       globals)
  | _ ->
      raise (Qcert_Error "Ill-formed model")
  end

let get_hierarchy io_schema =
  let (h,_,_,_) = build_schema io_schema in fst h

let build_input format h input =
  begin match input with
  | QcertCompiler.Jobject j ->
      begin match format with
      | META -> List.map (fun (x,y) -> (x, QData.json_to_qdata h y)) j
      | ENHANCED -> List.map (fun (x,y) -> (x, QData.json_enhanced_to_qdata h y)) j
      end
  | _ -> raise (Qcert_Error "Illed formed working memory: input")
  end

let build_output h output =
  QData.json_to_qdata h output

let build_phase_config j =
  begin match j with
  | QcertCompiler.Jobject r ->
      let phase_name = get_field_string "name" r in
      let phase_iter = int_of_float (get_field_int "iter" r) in
      let phase_optims = get_field_string_array "optims" r in
      { optim_phase_name = phase_name;
	optim_phase_iter = phase_iter;
	optim_phase_optims = phase_optims; }
  | _ ->
      raise (Qcert_Error "Ill-formed language optim config")
  end
let build_phases_config j =
  begin match j with
  | QcertCompiler.Jarray l ->
      List.map build_phase_config l
  | _ ->
      raise (Qcert_Error "Illed formed phase optim configuration")
  end

let build_language_config j =
  begin match j with
  | QcertCompiler.Jobject r ->
      let language_name = get_field_string "language" r in
      let phases = build_phases_config (get_field "phases" r) in
      { optim_language_name = language_name;
	optim_phases = phases; }
  | _ ->
      raise (Qcert_Error "Ill-formed language optim config")
  end
let build_optim_config j =
  begin match j with
  | QcertCompiler.Jarray l ->
      List.map build_language_config l
  | _ ->
      raise (Qcert_Error "Illed formed optim configuration")
  end
