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
let anon_args conf f = set_json conf (parse_json_from_file f)

let usage = Sys.argv.(0)^" jsonfile1 jsonfile2 ..."

(* Main *)
let () =
  let conf = default_data_config () in
  begin
    Arg.parse (args conf) (anon_args conf) usage
  end
