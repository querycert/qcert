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

let verbose = ref false
  
(* Command line args *)
let args conf =
  [ ("-io-format", Arg.String (set_data_format conf), "(META/ENHANCED)");
    ("-dir", Arg.String (set_data_dir conf), "Target directory");
    ("-verbose", Arg.Set verbose, "Print out a debug trace") ]

let print_hierarchy hi =
  if !verbose
  then
    List.iter (fun (x,y) -> Printf.printf "\t\t%s derives from %s\n" x y) hi
  else
    ()

let print_brand_types bts =
  if !verbose
  then
    List.iter (fun (x,y) -> Printf.printf "\t\t\tBrand %s = %s\n" x y) bts
  else
    ()

let print_type_defs br bts =
  List.iter (fun (x,y) -> (ignore (TypeUtil.rtype_content_to_rtype br y))) bts;
  if !verbose
  then
    List.iter (fun (x,y) -> Printf.printf "\t\t\ttypeDef %s = isValid\n" x) bts
  else
    ()

let print_wm_type br wmType =
  if !verbose
  then
    Printf.printf "\t\t%s\n" (PrettyIL.pretty_rtype true 0 wmType)
  else
    ()
    
let process_data_file conf f : string list =
  begin
    if !verbose
    then
      Printf.printf "Parsing I/O file: %s\n" f
    else ();
    let json : Data.json = parse_json_from_file f in
    if !verbose
    then
      Printf.printf "\tExtracting components from I/O file: %s\n" f
    else ();
    let (input,hierarchy,output,model,wmType) = DataUtil.get_io_content (Some json) in
    if !verbose
    then
      Printf.printf "\tHierarchy:\n"
    else ();
    let hi = DataUtil.build_hierarchy hierarchy in
    print_hierarchy hi;
    let (modelName,brandTypes,typeDefs) = DataUtil.get_model_content model in
    if !verbose
    then
      begin
	Printf.printf "\tModel:\n";
	Printf.printf "\t\tmodelName: %s\n" modelName;
	Printf.printf "\t\tbrandTypes:\n"
      end
    else ();
    print_brand_types brandTypes;
    if !verbose
    then
      Printf.printf "\t\ttypeDefs:\n"
    else ();
    print_type_defs hi typeDefs;
    if !verbose
    then
      Printf.printf "\t\tLOADING BRAND MODEL...\n"
    else ();
    let brand_model = TypeUtil.model_content_to_model hi (modelName,brandTypes,typeDefs) in
    if !verbose
    then
      Printf.printf "\t\t... DONE!\n"
    else ();
    match brand_model with
    | Some bm ->
	if !verbose
	then
	  Printf.printf "\tWorking Memory Type:"
	else ();
	let wmTypeContent = RType.camp_type_uncoll bm (TypeUtil.rtype_content_to_rtype hi wmType) in
	begin
	  match wmTypeContent with
	  | Some wmTypeC ->
	      print_wm_type hi wmTypeC;
	      let datalist = (DataUtil.get_input (get_data_format conf) (Some json)) in
	      List.map (fun d ->
		match RType.data_to_sjson bm d wmTypeC with
		| Some sdata ->
		    let sdata = Util.string_of_char_list sdata in
		    if !verbose
		    then
		      Printf.printf "SDATA:%s\n" sdata
		    else ();
		    sdata
		| None ->
		    raise (Failure "SDATA Serialization failed!"))
		datalist
	  | None ->
	      raise (Failure "WMType isn't a collection!")
	end
    | None ->
	raise (Failure "...BRAND MODEL CREATION FAILED!")
  end

let anon_args conf f =
  let sdata_list = process_data_file conf f in
  DisplayUtil.display_sdata conf f sdata_list

let usage = Sys.argv.(0)^" jsonfile1 jsonfile2 ..."

(* Main *)
let () =
  let conf = default_data_config () in
  begin
    Arg.parse (args conf) (anon_args conf) usage
  end
