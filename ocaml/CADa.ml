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

let print_hierarchy h =
  let hi = DataUtil.build_hierarchy h in
  List.iter (fun (x,y) -> Printf.printf "\t\t%s derives from %s\n" x y) hi

let print_brand_types bts =
  List.iter (fun (x,y) -> Printf.printf "\t\t\tBrand %s = %s\n" x y) bts

let anon_args conf f =
  begin
    Printf.printf "Parsing I/O file: %s\n" f;
    let json : Data.json = parse_json_from_file f in
    Printf.printf "\tExtracting components from I/O file: %s\n" f;
    let (input,hierarchy,output,model) = DataUtil.get_io_content (Some json) in
    Printf.printf "\tHierarchy:\n";
    print_hierarchy hierarchy;
    let (modelName,brandTypes,typeDefs) = DataUtil.get_model_content model in
    Printf.printf "\tModel:\n";
    Printf.printf "\t\tmodelName: %s\n" modelName;
    Printf.printf "\t\tbrandTypes:\n";
    print_brand_types brandTypes
  end

let usage = Sys.argv.(0)^" jsonfile1 jsonfile2 ..."

(* Main *)
let () =
  let conf = default_data_config () in
  begin
    Arg.parse (args conf) (anon_args conf) usage
  end
