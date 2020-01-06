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

(* This module contains a few basic utilities *)

(* Qcert Exception *)

exception Qcert_Error of string

(* this can't go in Logger, since that creates a circular dependency *)
type nraenv_logger_token_type = string
type nnrc_logger_token_type = string
type nnrs_imp_expr_logger_token_type = string
type nnrs_imp_stmt_logger_token_type = string
type nnrs_imp_logger_token_type = string
type dnnrc_logger_token_type = string

(**************)
(* Data types *)
(**************)

(* Data type conversions between Coq and OCaml *)

let string_of_char_list l =
  let b = Bytes.create (List.length l) in
  let i = ref 0 in
  List.iter (fun c -> Bytes.set b !i c; incr i) l;
  Bytes.to_string b

let char_list_of_string s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let string = string_of_char_list

let flat_map_string f s =
  let sl = ref [] in
  String.iter (fun c -> sl := (f c) :: !sl) s;
  let sl' = List.rev !sl in
  String.concat "" sl'

(* coq Z's are now replaced by native OCaml ints, but here is the way to get things back to coq Z's:

open BinNums

let rec coq_nat_of_pos i =
  if i = 0 then Datatypes.O else Datatypes.S (coq_nat_of_pos (i-1))

let coq_positive_of_pos i =
  BinPos.Pos.of_nat (coq_nat_of_pos i)

let coq_Z_of_int i =
  if (i = 0) then Z0
  else if (i < 0)
  then (Zneg (coq_positive_of_pos (-i)))
  else (Zpos (coq_positive_of_pos i))
 *)

let coq_Z_of_int i = i


(*******)
(* I/O *)
(*******)

(* Temporarily disabled -- JS
   let os_newline = if Sys.win32 then "\r\n" else "\n" *)
let os_newline = "\n"

let string_of_file file =
  try
    let inchan = open_in_bin file in
    let len = in_channel_length inchan in
    let buf = Buffer.create len in
    Buffer.add_channel buf inchan len;
    close_in inchan;
    Buffer.contents buf
  with
    Sys_error err ->
      Printf.eprintf
        "Could not read the file %s, got error Sys_error %s\n@?"
        file
        err;
      raise(Sys_error err)

(* File print *)

let make_file fout scomp =
  let oc = open_out fout in
  begin
    output_string oc scomp;
    close_out oc
  end

(* Make up target file name *)

let target_f dir f =
  match dir with
  | None -> f
  | Some d ->
    Filename.concat d (Filename.basename f)

let outname f suff = f ^ suff


(**********************************)
(* Support for Enhanced operators *)
(**********************************)

let qcert_string_of_float f =
  let ocaml_string = string_of_float f in
  let last_char = ocaml_string.[(String.length ocaml_string)-1] in
  match last_char with
  | '.' -> ocaml_string ^ "0"
  | _ -> ocaml_string

let string_of_enhanced_float f = char_list_of_string (string_of_float f)
let string_of_enhanced_string s = char_list_of_string ("S\"" ^ s ^ "\"")
	
(**********************************)
(* Timing function for CompStat   *)
(**********************************)

let time f x =
  let start = Sys.time() in
  let v = f x in
  let stop = Sys.time() in
  let t = string_of_float (stop -. start) in
  (char_list_of_string t, v)

(* String manipulation *)    

let string_after s n = String.sub s n (String.length s - n)

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

  
