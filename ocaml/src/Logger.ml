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

let trace = ref false
let set_trace () = trace := true
let unset_trace () = trace := false

let log_startPass name input =
  if !trace
  then
    begin
      (* Probably too much noise ... *)
      (* print_string "starting pass: "; print_endline name; *)
      name
    end
  else
    name
  
let log_step tok name input output =
  if !trace
  then
    begin
      if (input == output)
      then () (* (print_string "skipping optimization: "; print_endline name) *)
      else (print_string "running optimization: "; print_endline name) ;
      tok
    end
  else
    tok

let log_endPass tok output =
  if !trace
  then
    begin
      (* Probably too much noise ... *)
      (* print_string "ending pass: "; print_endline tok; *)
      tok
    end
  else
    tok

  
