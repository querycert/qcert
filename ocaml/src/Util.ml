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

(* This module contains a few basic utilities *)

(* CACo Exception *)

exception CACo_Error of string

(* this can't go in Logger, since that creates a circular dependency *)
type logger_token_type = string
				      
(**************)
(* Data types *)
(**************)

(* Data type conversions between Coq and OCaml *)

let rec string_of_char_list l =
  match l with
  | [] -> ""
  | c :: l -> (String.make 1 c) ^ (string_of_char_list l)

let char_list_of_string s =
  let l = ref [] in
  String.iter (fun c -> l := c :: !l) s;
  List.rev !l

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


(**********)
(* Lookup *)
(**********)

let get_data x io =
  try List.assoc x io
  with Not_found ->
    Printf.fprintf stderr "Unbound variable %s\n" x;
    raise (CACo_Error ("Unbound variable" ^ x))

let get_data_raise x io =
  List.assoc x io


(**********************************)
(* Support for Enhanced operators *)
(**********************************)

let float_sum l =
  List.fold_left (+.) 0. l

(* note that this is inefficient, becase it uses two passes over the list *)
let float_arithmean l =
  let ll = List.length l in
  if(ll == 0)
  then 0.
  else List.fold_left (+.) 0. l /. (float ll)

let rec float_listmin_aux l x =
  match l with
  | [] -> x
  | c :: ls -> float_listmin_aux ls (if x<c then x else c)
  
let float_listmin l =
  match l with
  | [] -> infinity
  | c :: ls -> float_listmin_aux ls c

let rec float_listmax_aux l x =
  match l with
  | [] -> x
  | c :: ls -> float_listmax_aux ls (if x>c then x else c)
  
let float_listmax l =
  match l with
  | [] -> neg_infinity
  | c :: ls -> float_listmax_aux ls c

let qcert_string_of_float f =
  let ocaml_string = string_of_float f in
  let last_char = ocaml_string.[String.length ocaml_string] in
  match last_char with
  | '.' -> ocaml_string ^ "0"
  | _ -> ocaml_string


