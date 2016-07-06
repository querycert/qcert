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
open DataUtil
open Compiler.EnhancedCompiler

(* Data utils for the Camp evaluator and compiler *)

let rtype_content_to_rtype (br: (string * string) list) (j:rtype_content) =
  match RType.json_to_rtype_with_fail (List.map (fun xy -> (Util.char_list_of_string (fst xy), Util.char_list_of_string (snd xy))) br) j with
  | None -> raise (Failure ("type parsing failed for JSON:" ^ (Util.string_of_char_list (Data.jsonToJS ['"'] j))))
  | Some t -> t

