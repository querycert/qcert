(*
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

let arg =
  match Sys.argv with
  | [| _; x |] -> x
  | _ -> failwith "binary_to_string: provide file as single argument"

let rt =
  if Sys.file_exists arg then arg
  else failwith (Printf.sprintf "%s does not exist" arg)

let bin =
  let ic = open_in rt in
  let rec read acc =
    match input_line ic with
    | l -> read (l :: acc)
    | exception End_of_file ->
      List.rev acc |> String.concat "\n"
  in
  read []

let () = String.iter (fun c -> Printf.printf "\\x%02x" (int_of_char c)) bin
