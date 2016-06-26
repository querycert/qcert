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
open Compiler.EnhancedCompiler

(* Data utils for the Camp evaluator and compiler *)

type io_hierarchy = Data.data
type io_hierarchy_list = (string * string) list
type io_input = Data.data list
type io_output = Data.data list

type io_data = Data.data option

let get_io_content (od:Data.data option) : Data.data * Data.data * Data.data =
    match od with
    | Some d ->
	begin
	  try
	    match d with
	    | Compiler.Drec r ->
		let input = List.assoc ['i';'n';'p';'u';'t'] r in
		let output = List.assoc ['o';'u';'t';'p';'u';'t'] r in
		let hierarchy = List.assoc ['i';'n';'h';'e';'r';'i';'t';'a';'n';'c';'e'] r in
		(input, hierarchy, output)
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
  | (_, h, _) -> h

let get_hierarchy_cloudant od =
  try
    match get_io_content od with
    | (_, h, _) -> h
  with
  | _ -> Compiler.Dcoll []

let build_hierarchy h =
  match h with
  | Compiler.Dcoll l ->
      List.map (function
        | Compiler.Drec
            ( [(['s';'u';'b'], Compiler.Dstring sub); (['s';'u';'p'],Compiler.Dstring sup)]
            | [(['s';'u';'p'], Compiler.Dstring sup); (['s';'u';'b'], Compiler.Dstring sub)] ) ->
                (Util.string_of_char_list sub, Util.string_of_char_list sup)
        | _ ->
            raise (CACo_Error "Ill-formed hierarchy"))
        l
  | _ ->
      raise (CACo_Error "Ill-formed hierarchy")

let get_input conf od =
  match get_io_content od with
  | (i, h, _) ->
      let h = List.map (fun (x,y) -> (Util.char_list_of_string x, Util.char_list_of_string y)) (build_hierarchy h) in
      match i with
      | Compiler.Dcoll l ->
	  begin
	    match get_format conf with
	    | META -> List.map (Data.json_to_data h) l (* in coq so we can prove properties on conversions *)
	    | ENHANCED -> List.map (Data.json_enhanced_to_data h) l (* in coq so we can prove properties on conversions *)
	  end
      | _ ->
	  raise (CACo_Error "Illed formed working memory")

let get_output od =
  match get_io_content od with
  | (_, h, o) ->
      let h = List.map (fun (x,y) -> (Util.char_list_of_string x, Util.char_list_of_string y)) (build_hierarchy h) in
      match o with
      | Compiler.Dcoll l -> List.map (Data.json_to_data h) l (* in coq so we can prove properties on conversions *)
      | _ ->
	  raise (CACo_Error "Ill-formed expected result")

