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

(* This is main for the Camp Data processor *)

open Util
open ConfigUtil
open ParseFile
open Compiler.EnhancedCompiler

(* Command line args *)
let args conf = []

let print_hierarchy hi =
  List.iter (fun (x,y) -> Printf.printf "\t\t%s derives from %s\n" x y) hi

let print_brand_types bts =
  List.iter (fun (x,y) -> Printf.printf "\t\t\tBrand %s = %s\n" x y) bts

let print_type_defs br bts =
  List.iter (fun (x,y) -> (ignore (TypeUtil.rtype_content_to_rtype br y))) bts;
  List.iter (fun (x,y) -> Printf.printf "\t\t\ttypeDef %s = isValid\n" x) bts

let print_wm_type br wmType =
  ignore (TypeUtil.rtype_content_to_rtype br wmType);
  Printf.printf "\t\t%s\n" "TYPE"
    
let anon_args conf f =
  begin
    Printf.printf "Parsing I/O file: %s\n" f;
    let json : Data.json = parse_json_from_file f in
    Printf.printf "\tExtracting components from I/O file: %s\n" f;
    let (input,hierarchy,output,model,wmType) = DataUtil.get_io_content (Some json) in
    Printf.printf "\tHierarchy:\n";
    let hi = DataUtil.build_hierarchy hierarchy in
    print_hierarchy hi;
    let (modelName,brandTypes,typeDefs) = DataUtil.get_model_content model in
    Printf.printf "\tModel:\n";
    Printf.printf "\t\tmodelName: %s\n" modelName;
    Printf.printf "\t\tbrandTypes:\n";
    print_brand_types brandTypes;
    Printf.printf "\t\ttypeDefs:\n";
    print_type_defs hi typeDefs;
    Printf.printf "\tWorking Memory Type:";
    print_wm_type hi wmType;
    Printf.printf "\t\tLOADING BRAND MODEL...\n";
    let brand_model = TypeUtil.model_content_to_model hi (modelName,brandTypes,typeDefs) in
    Printf.printf "\t\t... DONE!\n";
    match brand_model with
    | Some bm ->
	let datalist = (DataUtil.get_input (get_data_format conf) (Some json)) in
	List.iter (fun d ->
	  match RType.data_to_sjson bm d wmType with
	  | Some sdata -> Printf.printf "SDATA:%s\n" (Util.string_of_char_list sdata)
	  | None -> Printf.printf "SDATA Serialization failed!")
	  datalist
    | None ->
	raise (Failure "...BRAND MODEL CREATION FAILED!")
  end

let usage = Sys.argv.(0)^" jsonfile1 jsonfile2 ..."

(* Main *)
let () =
  let conf = default_data_config () in
  begin
    Arg.parse (args conf) (anon_args conf) usage
  end
