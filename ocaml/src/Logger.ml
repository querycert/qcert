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

(* nra logger *)
let nra_trace = ref false
let nra_set_trace () = nra_trace := true
let nra_unset_trace () = nra_trace := false

let nra_log_startPass name input =
  if !nra_trace
  then
    begin
      (* Probably too much noise ... *)
      (* print_string "starting pass: "; print_endline name; *)
      name
    end
  else
    name
  
let nra_log_step tok name input output =
  if !nra_trace
  then
    begin
      if (input == output)
      then () (* (print_string "skipping optimization: "; print_endline name) *)
      else (print_string "running optimization: "; print_endline name) ;
      tok
    end
  else
    tok

let nra_log_endPass tok output =
  if !nra_trace
  then
    begin
      (* Probably too much noise ... *)
      (* print_string "ending pass: "; print_endline tok; *)
      tok
    end
  else
    tok

(* nrc logger *)
  
let nrc_trace = ref false
let nrc_set_trace () = nrc_trace := true
let nrc_unset_trace () = nrc_trace := false

let nrc_log_startPass name input =
  if !nrc_trace
  then
    begin
      (* Probably too much noise ... *)
      (* print_string "starting pass: "; print_endline name; *)
      name
    end
  else
    name
  
let nrc_log_step tok name input output =
  if !nrc_trace
  then
    begin
      if (input == output)
      then () (* (print_string "skipping optimization: "; print_endline name) *)
      else (print_string "running optimization: "; print_endline name) ;
      tok
    end
  else
    tok

let nrc_log_endPass tok output =
  if !nrc_trace
  then
    begin
      (* Probably too much noise ... *)
      (* print_string "ending pass: "; print_endline tok; *)
      tok
    end
  else
    tok
