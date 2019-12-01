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
open QcertUtils.Util
open QcertCompiler.EnhancedCompiler

(* Data utils for the Camp evaluator and compiler *)

type io_json = QData.json

type io_input = QData.json
type io_output = QData.json
type io_schema = QData.json

type io_inheritance = QData.json
type io_brandTypes = QData.json
type io_typeDefs = QData.json
type io_globals = QData.json

type rtype_content = QData.json
type vrtype_content = QData.json

type content_input = (char list * QData.qdata) list
type content_output = QData.qdata

type content_inheritance = (char list * char list) list
type full_content_inheritance = (content_inheritance * io_inheritance)
type content_brandTypes = (string * string) list
type content_typeDefs = (string * rtype_content) list
type content_globals = (string * vrtype_content) list
type content_schema = full_content_inheritance * io_brandTypes option * io_typeDefs option * io_globals option

(* Optimization support *)
type optim_phase =
    { mutable optim_phase_name : string;
      mutable optim_phase_iter : int;
      mutable optim_phase_optims : string list; }
type optim_language =
    { mutable optim_language_name : string;
      mutable optim_phases : optim_phase list; }

let get_field_opt name r =
  begin try
    Some (List.assoc (char_list_of_string name) r)
  with
  | Not_found -> None
  end

let get_field_defaults name r d =
  begin try
    List.assoc (char_list_of_string name) r
  with
  | Not_found -> d
  end

let get_io_components (od:QData.json option) : QData.json option * QData.json option * QData.json option =
  begin match od with
  | Some d ->
      begin	try
	      begin match d with
	      | QcertCompiler.Jobject r ->
	          let input = get_field_opt "input" r in
	          let output = get_field_opt "output" r in
	          let schema = get_field_opt "schema" r in
	          (input,
	           output,
	           schema)
	      | _ ->
	          raise Not_found
        end
	    with
	    | _ ->
	        raise (Qcert_Error "Ill-formed IO")
      end
  | None ->
      raise (Qcert_Error "No IO file provided")
  end

(* Schema processing first *)

let check_inheritance h =
  QcertUtil.lift_qerror QType.make_brand_relation h

let build_inheritance h =
  begin match h with
  | QcertCompiler.Jarray l ->
    let raw_h =
      List.map (function
          | QcertCompiler.Jobject
              ( [(['s';'u';'b'], QcertCompiler.Jstring sub); (['s';'u';'p'], QcertCompiler.Jstring sup)]
              | [(['s';'u';'p'], QcertCompiler.Jstring sup); (['s';'u';'b'], QcertCompiler.Jstring sub)] ) ->
            (sub, sup)
          | _ ->
            raise (Qcert_Error "Ill-formed inheritance"))
        l
    in
    check_inheritance raw_h
  | _ ->
    raise (Qcert_Error "Ill-formed inheritance")
  end

let build_brandTypes bts =
  begin match bts with
  | QcertCompiler.Jarray l ->
      List.map (function
        | QcertCompiler.Jobject
            ( [(['b';'r';'a';'n';'d'], QcertCompiler.Jstring brandName); (['t';'y';'p';'e';'N';'a';'m';'e'], QcertCompiler.Jstring typeName)]
        | [(['t';'y';'p';'e';'N';'a';'m';'e'], QcertCompiler.Jstring typeName); (['b';'r';'a';'n';'d'], QcertCompiler.Jstring brandName)] ) ->
            (string_of_char_list brandName, string_of_char_list typeName)
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
            (string_of_char_list typeName, typeDef)
        | _ ->
            raise (Qcert_Error "Ill-formed typeDefs"))
        l
  | _ ->
      raise (Qcert_Error "Ill-formed typeDefs")
  end

let build_globals globals =
  begin match globals with
  | QcertCompiler.Jobject l ->
      List.map (function (varname, typeDef) -> (string_of_char_list varname, typeDef)) l
  | _ ->
      raise (Qcert_Error "Ill-formed globals")
  end

let missing_inheritance_default = QData.jarray []  (* Empty array i.e., empty inheritance *)

let build_schema (j:QData.json) =
  begin match j with
  | QcertCompiler.Jobject r ->
      let inheritance = get_field_defaults "inheritance" r missing_inheritance_default in
      let brandTypes = get_field_opt "brandTypes" r in
      let typeDefs = get_field_opt "typeDefs" r in
      let globals = get_field_opt "globals" r in
      ((build_inheritance inheritance,inheritance),
       brandTypes,
       typeDefs,
       globals)
  | _ ->
      raise (Qcert_Error "Ill-formed model")
  end

let build_input h input =
  begin match input with
  | QcertCompiler.Jobject j -> List.map (fun (x,y) -> (x, QData.json_to_qdata h (QData.json_to_qjson y))) j
  | _ -> raise (Qcert_Error "Illed formed working memory: input")
  end

let build_output h output =
  QData.json_to_qdata h (QData.json_to_qjson output)

let build_optim_config j =
  begin match QDriver.json_to_optim_config j with
  | QcertCompiler.Inl e -> raise (Qcert_Error (string_of_char_list e))
  | QcertCompiler.Inr oc -> oc
  end
