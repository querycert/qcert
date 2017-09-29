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

open Qcert_runtime

(* String manipulation *)    

let string_before s n = String.sub s 0 n
let string_after s n = String.sub s n (String.length s - n)
let first_chars s n = String.sub s 0 n
let last_chars s n = String.sub s (String.length s - n) n

let re_match re s pos =
  if pos >= String.length s then raise Not_found
  else
    let rec pos_match re s pos_re pos_s =
      if pos_re >= String.length re
      then true
      else
	try
	  if re.[pos_re] = s.[pos_s]
	  then pos_match re s (pos_re+1) (pos_s+1)
	  else false
	with
	| _ -> false
    in
    pos_match re s 0 pos
  
let search_forward re s pos =
  if re = "" then raise (Invalid_argument "Matching string should not be empty")
  else
    let rec find start =
      if re_match re s start
      then start
      else find (start+1)
    in
    find pos

let opt_search_forward re s pos =
  try Some(search_forward re s pos) with Not_found -> None

let global_replace const_expr repl text =
  let rec replace accu start last_was_empty =
    let startpos = if last_was_empty then start + 1 else start in
    if startpos > String.length text then
      string_after text start :: accu
    else
      match opt_search_forward const_expr text startpos with
      | None ->
          string_after text start :: accu
      | Some pos ->
          let end_pos = pos + String.length const_expr in
          let repl_text = repl in
          replace (repl_text :: String.sub text start (pos-start) :: accu)
                  end_pos (end_pos = pos)
  in
  String.concat "" (List.rev (replace [] 0 false))

let quoting s =
  let s = global_replace "\\" "\\\\" s in
  let s = global_replace "\t" " " s in
  let s = global_replace "\"" "\\\"" s in
  let s = global_replace "\n" "\\n" s in
  s

let _ =
  let quoted_runtime = quoting runtime in
  print_string "const runtime = \"";
  print_string quoted_runtime;
  print_string "\"";
  print_newline ();
  flush stdout

