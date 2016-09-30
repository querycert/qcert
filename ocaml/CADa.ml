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
  [ ("-io-format", Arg.String (set_data_format conf), "Input Serialization (META/ENHANCED)");
    ("-schema", Arg.String (fun f -> set_data_schema conf (ParseFile.parse_json_from_file f)), "Input Schema");
    ("-dir", Arg.String (set_data_dir conf), "Target directory");
    ("-verbose", Arg.Set verbose, "Print out a debug trace") ]

let print_hierarchy hi =
  List.iter (fun (x,y) -> Printf.printf "\t\t%s derives from %s\n" x y) hi

let print_brand_types bts =
  List.iter (fun (x,y) -> Printf.printf "\t\t\tBrand %s = %s\n" x y) bts

let print_type_defs br bts =
  List.iter (fun (x,y) -> Printf.printf "\t\t\ttypeDef %s = isValid\n" x) bts

let print_wm_type br wmType =
  Printf.printf "\t\t%s\n" (PrettyIL.pretty_rtype true 0 wmType)

let process_data_file_verbose conf f : string list =
  begin
    Printf.printf "Parsing I/O file: %s\n" f;
    let io : Data.json = parse_io_from_file f in
    Printf.printf "\tExtracting schema components...\n";
    let json_schema_io =
      match get_data_schema conf with
      | Some sio -> sio
      | None -> io
    in
    let sch = TypeUtil.schema_of_io_json json_schema_io in
    let ((hierarchy,modelName,brandTypes,typeDefs),wmType) =
      let open TypeUtil in
      begin match sch.sch_io_schema with
      | Some io_sch ->
          ((io_sch.io_brand_model,
            io_sch.io_name,
            io_sch.io_brand_type,
            io_sch.io_type_definitions),
           sch.sch_camp_type)
      | None -> assert false
      end
    in
    begin
      Printf.printf "\tHierarchy:\n";
      print_hierarchy hierarchy;
      Printf.printf "\tModel:\n";
      Printf.printf "\t\tmodelName: %s\n" modelName;
      Printf.printf "\t\tbrandTypes:\n";
      print_brand_types brandTypes;
      Printf.printf "\t\ttypeDefs:\n";
      print_type_defs hierarchy typeDefs
    end;
    Printf.printf "\t\tLoading schema components...\n";
    let (brand_model,wmTypeC) =
      (sch.TypeUtil.sch_brand_model,
       sch.TypeUtil.sch_camp_type)
    in
    Printf.printf "\t\t... DONE\n";
    print_wm_type hierarchy wmTypeC;
    Printf.printf "\tParsing I/O file\n";
    let datalist = (DataUtil.get_input (get_data_format conf) (Some io)) in
    Printf.printf "\tTranslating I/O file\n";
    List.map (fun d ->
      match RType.data_to_sjson brand_model d wmTypeC with
      | Some sdata ->
	  let sdata = Util.string_of_char_list sdata in
	  Printf.printf "Spark I/O:%s\n" sdata;
	  sdata
      | None ->
	  raise (Failure "Spark I/O serialization failed"))
      datalist
  end

let process_data_file conf f : string list =
  begin
    let io : Data.json = parse_io_from_file f in
    let json_schema_io =
      match get_data_schema conf with
      | Some sio -> sio
      | None -> io
    in
    let sch = TypeUtil.schema_of_io_json json_schema_io in
    let (brand_model,wmTypeC) =
      (sch.TypeUtil.sch_brand_model,
       sch.TypeUtil.sch_camp_type)
    in
    let datalist = (DataUtil.get_input (get_data_format conf) (Some io)) in
    List.map (fun d ->
      match RType.data_to_sjson brand_model d wmTypeC with
      | Some sdata ->
	  let sdata = Util.string_of_char_list sdata in
	  sdata
      | None ->
	  raise (Failure "Spark I/O serialization failed"))
      datalist
  end

let anon_args conf f =
  let sdata_list =
    if !verbose
    then
      process_data_file_verbose conf f
    else
      process_data_file conf f
  in
  DataUtil.display_sdata (get_data_dir conf) f sdata_list (suffix_sdata ())

let usage = Sys.argv.(0)^" jsonfile1 jsonfile2 ..."

(* Main *)
let () =
  let conf = default_data_config () in
  begin
    Arg.parse (args conf) (anon_args conf) usage
  end
