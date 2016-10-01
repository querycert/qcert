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

type io_hierarchy = QData.json
type io_json = QData.json option

type io_hierarchy_list = (string * string) list
type io_input = QData.data list
type io_output = QData.data list

type rtype_content = QData.json
type json_schema = (io_hierarchy_list * QData.json * QData.json) option
type model_content = string * (string * string) list * (string * rtype_content) list

let get_io_content (od:QData.json option) : QData.json * QData.json * QData.json * QData.json * QData.json =
    match od with
    | Some d ->
	begin
	  try
	    match d with
	    | Compiler.Jobject r ->
		let input = List.assoc ['i';'n';'p';'u';'t'] r in
		let output = List.assoc ['o';'u';'t';'p';'u';'t'] r in
		let hierarchy = List.assoc ['i';'n';'h';'e';'r';'i';'t';'a';'n';'c';'e'] r in
		let model = List.assoc ['m';'o';'d';'e';'l'] r in
		let wmType = List.assoc ['W';'M';'T';'y';'p';'e'] r in
		(input, hierarchy, output, model, wmType)
	    | _ ->
		raise Not_found
	  with
	  | _ ->
	      raise (CACo_Error "Ill-formed IO")
	end
    | None ->
	raise (CACo_Error "No IO file provided")

let get_hierarchy od =
  match get_io_content od with
  | (_, h, _, _, _) -> h

let get_hierarchy_cloudant od =
  try
    match get_io_content od with
    | (_, h, _, _, _) -> h
  with
  | _ -> Compiler.Jarray []

let build_hierarchy h =
  match h with
  | Compiler.Jarray l ->
      List.map (function
        | Compiler.Jobject
            ( [(['s';'u';'b'], Compiler.Jstring sub); (['s';'u';'p'], Compiler.Jstring sup)]
            | [(['s';'u';'p'], Compiler.Jstring sup); (['s';'u';'b'], Compiler.Jstring sub)] ) ->
                (Util.string_of_char_list sub, Util.string_of_char_list sup)
        | _ ->
            raise (CACo_Error "Ill-formed hierarchy"))
        l
  | _ ->
      raise (CACo_Error "Ill-formed hierarchy")

let build_brand_types bts =
  match bts with
  | Compiler.Jarray l ->
      List.map (function
        | Compiler.Jobject
            ( [(['b';'r';'a';'n';'d'], Compiler.Jstring brandName); (['t';'y';'p';'e';'N';'a';'m';'e'], Compiler.Jstring typeName)]
            | [(['t';'y';'p';'e';'N';'a';'m';'e'], Compiler.Jstring typeName); (['b';'r';'a';'n';'d'], Compiler.Jstring brandName)] ) ->
                (Util.string_of_char_list brandName, Util.string_of_char_list typeName)
        | _ ->
            raise (CACo_Error "Ill-formed brandTypes"))
        l
  | _ ->
      raise (CACo_Error "Ill-formed brandTypes")

let build_type_defs bts =
  match bts with
  | Compiler.Jarray l ->
      List.map (function
        | Compiler.Jobject
            ( [(['t';'y';'p';'e';'N';'a';'m';'e'], Compiler.Jstring typeName); (['t';'y';'p';'e';'D';'e';'f'], typeDef)]
            | [(['t';'y';'p';'e';'D';'e';'f'], typeDef); (['t';'y';'p';'e';'N';'a';'m';'e'], Compiler.Jstring typeName)] ) ->
                (Util.string_of_char_list typeName, typeDef)
        | _ ->
            raise (CACo_Error "Ill-formed typeDefs"))
        l
  | _ ->
      raise (CACo_Error "Ill-formed typeDefs")

let get_input format od =
  match get_io_content od with
  | (i, h, _, _, _) ->
      let h = List.map (fun (x,y) -> (Util.char_list_of_string x, Util.char_list_of_string y)) (build_hierarchy h) in
      match i with
      | Compiler.Jarray l ->
	  begin
	    match format with
	    | META -> List.map (QData.json_to_data h) l (* in coq so we can prove properties on conversions *)
	    | ENHANCED -> List.map (QData.json_enhanced_to_data h) l (* in coq so we can prove properties on conversions *)
	  end
      | _ ->
	  raise (CACo_Error "Illed formed working memory")

let get_model_content (j:QData.json) =
  match j with
  | Compiler.Jobject r ->
      let modelName = List.assoc ['m';'o';'d';'e';'l';'N';'a';'m';'e'] r in
      let brandTypes = List.assoc ['b';'r';'a';'n';'d';'T';'y';'p';'e';'s'] r in
      let typeDefs = List.assoc ['t';'y';'p';'e';'D';'e';'f';'s'] r in
      begin
	match modelName with
	| Compiler.Jstring name ->
	    (Util.string_of_char_list name,build_brand_types brandTypes,build_type_defs typeDefs)
	| _ ->
	    raise (CACo_Error "Ill-formed model")
      end
  | _ ->
      raise (CACo_Error "Ill-formed model")

let get_output od =
  match get_io_content od with
  | (_, h, o, _, _) ->
      let h = List.map (fun (x,y) -> (Util.char_list_of_string x, Util.char_list_of_string y)) (build_hierarchy h) in
      match o with
      | Compiler.Jarray l -> List.map (QData.json_to_data h) l (* in coq so we can prove properties on conversions *)
      | _ ->
	  raise (CACo_Error "Ill-formed expected result")

let display_sdata (data_dir : string option) (fname:string) (sdata:string list) (suffix:string) =
  let fpref = Filename.chop_extension fname in
  let fout_sdata = outname (target_f data_dir fpref) suffix in
  let sdata =
    String.concat "\n" sdata
  in
  make_file fout_sdata sdata
