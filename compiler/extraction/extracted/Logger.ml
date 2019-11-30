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

(* This module contains the implementation for the optimization logger *)

open SExp
open Util

type logger_verbosity =
  | LOG_NONE
  | LOG_NAMES
  | LOG_PHASES_AND_NAMES
  | LOG_VERBOSE_SEXP of (Obj.t -> sexp)

let logger_verbosity_of_string conv s
  = match s with
  | "none" -> LOG_NONE
  | "names" -> LOG_NAMES
  | "phases_and_names" -> LOG_PHASES_AND_NAMES
  | "sexp" -> LOG_VERBOSE_SEXP conv
  | _ -> raise (Qcert_Error ("Unknown logging verbosity level: "^s^".  Supported levels: none, names, phases_and_names, sexp"))

(* TODO: refactor this code *)
	    
(* nra logger *)
let nra_trace = ref LOG_NONE
let nra_set_trace conv (s:string) = nra_trace := (logger_verbosity_of_string conv s)

let nra_log_startPass name input =
  if !nra_trace != LOG_NONE
  then
    (begin
	match !nra_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_string "starting nra optimization pass: "; print_endline name
	| LOG_VERBOSE_SEXP conv -> print_string ("(phase \"nra\" \""^name^"\"")
	| _ -> ()
    end;
  name)
  else
    name
  
let nra_log_step tok name input output =
  if !nra_trace != LOG_NONE
  then
    begin
      if (input == output)
      then () (* (print_string "skipping optimization: "; print_endline name) *)
      else
	begin
	  match !nra_trace with
	  | LOG_NAMES ->
	     (print_string "running nra optimization: "; print_endline name) ;
	  | LOG_PHASES_AND_NAMES ->
	     (print_string "  running nra optimization: "; print_endline name) ;
	  | LOG_VERBOSE_SEXP conv ->
	       let sexp_input = conv (Obj.magic input) in
	       let sexp_output = conv (Obj.magic output) in
	       let sexp_opt = STerm ("opt", [SString name; sexp_input; sexp_output]) in
	       print_endline ""; print_string ("  " ^ (sexp_to_string sexp_opt))
	  | _ -> ()
	end;
      tok
    end
  else
    tok

let nra_log_endPass tok output =
  if !nra_trace != LOG_NONE
  then
    (begin
	match !nra_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_endline "ending nra optimization pass: "
	| LOG_VERBOSE_SEXP conv -> print_endline ")"
	| _ -> ()
    end;
     tok)
  else
    tok

(* nrc logger *)
  
let nrc_trace = ref LOG_NONE
let nrc_set_trace conv s = nrc_trace := (logger_verbosity_of_string conv s)

let nrc_log_startPass name input =
  if !nrc_trace != LOG_NONE
  then
    (begin
	match !nrc_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_string "starting nrc optimization pass: "; print_endline name
	| LOG_VERBOSE_SEXP conv -> print_string ("(phase \"nrc\" \""^name^"\"")
	| _ -> ()
    end;
     name)
  else
    name
  
let nrc_log_step tok name input output =
  if !nrc_trace != LOG_NONE
  then
    begin
     if (input == output)
      then () (* (print_string "skipping optimization: "; print_endline name) *)
      else
	begin
	  match !nrc_trace with
	  | LOG_NAMES ->
	     (print_string "running nrc optimization: "; print_endline name) ;
	  | LOG_PHASES_AND_NAMES ->
	     (print_string "  running nrc optimization: "; print_endline name) ;
	  | LOG_VERBOSE_SEXP conv ->
	     begin
	       let sexp_input = conv (Obj.magic input) in
	       let sexp_output = conv (Obj.magic output) in
	       let sexp_opt = STerm ("opt", [SString name; sexp_input; sexp_output]) in
	       print_endline ""; print_string ("  " ^ (sexp_to_string sexp_opt))
	     end
	  | _ -> ()
	end;
     tok
    end
  else
    tok

let nrc_log_endPass tok output =
  if !nrc_trace != LOG_NONE
  then
    (begin
	match !nrc_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_endline "ending nrc optimization pass: "
	| LOG_VERBOSE_SEXP conv -> print_endline ")"
	| _ -> ()
    end;
     tok)
  else
    tok

(* nnrs_imp logger *)  
let nnrs_imp_expr_trace = ref LOG_NONE
let nnrs_imp_expr_set_trace conv s = nnrs_imp_expr_trace := (logger_verbosity_of_string conv s)

let nnrs_imp_expr_log_startPass name input =
  if !nnrs_imp_expr_trace != LOG_NONE
  then
    (begin
	match !nnrs_imp_expr_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_string "starting nnrs_imp_expr optimization pass: "; print_endline name
	| LOG_VERBOSE_SEXP conv -> print_string ("(phase \"nnrs_imp_expr\" \""^name^"\"")
	| _ -> ()
    end;
     name)
  else
    name
  
let nnrs_imp_expr_log_step tok name input output =
  if !nnrs_imp_expr_trace != LOG_NONE
  then
    begin
     if (input == output)
      then () (* (print_string "skipping optimization: "; print_endline name) *)
      else
	begin
	  match !nnrs_imp_expr_trace with
	  | LOG_NAMES ->
	     (print_string "running nnrs_imp_expr optimization: "; print_endline name) ;
	  | LOG_PHASES_AND_NAMES ->
	     (print_string "  running nnrs_imp_expr optimization: "; print_endline name) ;
	  | LOG_VERBOSE_SEXP conv ->
	     begin
	       let sexp_input = conv (Obj.magic input) in
	       let sexp_output = conv (Obj.magic output) in
	       let sexp_opt = STerm ("opt", [SString name; sexp_input; sexp_output]) in
	       print_endline ""; print_string ("  " ^ (sexp_to_string sexp_opt))
	     end
	  | _ -> ()
	end;
     tok
    end
  else
    tok

let nnrs_imp_expr_log_endPass tok output =
  if !nnrs_imp_expr_trace != LOG_NONE
  then
    (begin
	match !nnrs_imp_expr_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_endline "ending nnrs_imp_expr optimization pass: "
	| LOG_VERBOSE_SEXP conv -> print_endline ")"
	| _ -> ()
    end;
     tok)
  else
    tok

let nnrs_imp_stmt_trace = ref LOG_NONE
let nnrs_imp_stmt_set_trace conv s = nnrs_imp_stmt_trace := (logger_verbosity_of_string conv s)

let nnrs_imp_stmt_log_startPass name input =
  if !nnrs_imp_stmt_trace != LOG_NONE
  then
    (begin
	match !nnrs_imp_stmt_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_string "starting nnrs_imp_stmt optimization pass: "; print_endline name
	| LOG_VERBOSE_SEXP conv -> print_string ("(phase \"nnrs_imp_stmt\" \""^name^"\"")
	| _ -> ()
    end;
     name)
  else
    name
  
let nnrs_imp_stmt_log_step tok name input output =
  if !nnrs_imp_stmt_trace != LOG_NONE
  then
    begin
     if (input == output)
      then () (* (print_string "skipping optimization: "; print_endline name) *)
      else
	begin
	  match !nnrs_imp_stmt_trace with
	  | LOG_NAMES ->
	     (print_string "running nnrs_imp_stmt optimization: "; print_endline name) ;
	  | LOG_PHASES_AND_NAMES ->
	     (print_string "  running nnrs_imp_stmt optimization: "; print_endline name) ;
	  | LOG_VERBOSE_SEXP conv ->
	     begin
	       let sexp_input = conv (Obj.magic input) in
	       let sexp_output = conv (Obj.magic output) in
	       let sexp_opt = STerm ("opt", [SString name; sexp_input; sexp_output]) in
	       print_endline ""; print_string ("  " ^ (sexp_to_string sexp_opt))
	     end
	  | _ -> ()
	end;
     tok
    end
  else
    tok

let nnrs_imp_stmt_log_endPass tok output =
  if !nnrs_imp_stmt_trace != LOG_NONE
  then
    (begin
	match !nnrs_imp_stmt_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_endline "ending nnrs_imp_stmt optimization pass: "
	| LOG_VERBOSE_SEXP conv -> print_endline ")"
	| _ -> ()
    end;
     tok)
  else
    tok

let nnrs_imp_trace = ref LOG_NONE
let nnrs_imp_set_trace conv s = nnrs_imp_trace := (logger_verbosity_of_string conv s)

let nnrs_imp_log_startPass name input =
  if !nnrs_imp_trace != LOG_NONE
  then
    (begin
	match !nnrs_imp_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_string "starting nnrs_imp optimization pass: "; print_endline name
	| LOG_VERBOSE_SEXP conv -> print_string ("(phase \"nnrs_imp\" \""^name^"\"")
	| _ -> ()
    end;
     name)
  else
    name
  
let nnrs_imp_log_step tok name input output =
  if !nnrs_imp_trace != LOG_NONE
  then
    begin
     if (input == output)
      then () (* (print_string "skipping optimization: "; print_endline name) *)
      else
	begin
	  match !nnrs_imp_trace with
	  | LOG_NAMES ->
	     (print_string "running nnrs_imp optimization: "; print_endline name) ;
	  | LOG_PHASES_AND_NAMES ->
	     (print_string "  running nnrs_imp optimization: "; print_endline name) ;
	  | LOG_VERBOSE_SEXP conv ->
	     begin
	       let sexp_input = conv (Obj.magic input) in
	       let sexp_output = conv (Obj.magic output) in
	       let sexp_opt = STerm ("opt", [SString name; sexp_input; sexp_output]) in
	       print_endline ""; print_string ("  " ^ (sexp_to_string sexp_opt))
	     end
	  | _ -> ()
	end;
     tok
    end
  else
    tok

let nnrs_imp_log_endPass tok output =
  if !nnrs_imp_trace != LOG_NONE
  then
    (begin
	match !nnrs_imp_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_endline "ending nnrs_imp optimization pass: "
	| LOG_VERBOSE_SEXP conv -> print_endline ")"
	| _ -> ()
    end;
     tok)
  else
    tok

let nnrs_imp_all_set_trace conv_e conv_s conv_t s =
  nnrs_imp_expr_set_trace conv_e s;
  nnrs_imp_stmt_set_trace conv_s s;
  nnrs_imp_set_trace conv_t s

(* dnrc logger *)
  
let dnrc_trace = ref LOG_NONE
let dnrc_set_trace conv s = dnrc_trace := (logger_verbosity_of_string conv s)

let dnrc_log_startPass name input =
  if !dnrc_trace != LOG_NONE
  then
    (begin
	match !dnrc_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_string "starting dnrc optimization pass: "; print_endline name
	| LOG_VERBOSE_SEXP conv -> print_string ("(phase \"dnrc\" \""^name^"\"")
	| _ -> ()
    end;
     name)
  else
    name
  
let dnrc_log_step tok name input output =
  if !dnrc_trace != LOG_NONE
  then
    begin
     if (input == output)
      then () (* (print_string "skipping optimization: "; print_endline name) *)
      else
	begin
	  match !dnrc_trace with
          | LOG_NONE -> ()
	  | LOG_NAMES ->
	     (print_string "running dnrc optimization: "; print_endline name) ;
	  | LOG_PHASES_AND_NAMES ->
	     (print_string "  running dnrc optimization: "; print_endline name) ;
	  | LOG_VERBOSE_SEXP conv ->
             failwith "sexp logging not supported for dnrc"
	end;
     tok
    end
  else
    tok

let dnrc_log_endPass tok output =
  if !dnrc_trace != LOG_NONE
  then
    (begin
	match !dnrc_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_endline "ending dnrc optimization pass: "
	| LOG_VERBOSE_SEXP conv -> print_endline ")"
	| _ -> ()
    end;
     tok)
  else
    tok
