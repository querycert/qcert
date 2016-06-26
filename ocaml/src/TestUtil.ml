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

open Compiler.EnhancedCompiler
open Util
open ConfigUtil
open PrettyIL

let sexp_string_to_nra s =
  ParseString.parse_nra_sexp_from_string s

let nra_to_sexp_string op =
  SExp.sexp_to_string (Asts.alg_to_sexp op)

let sexp_algenv_top_test (fname,op) =
  try
    let display_nra = nra_to_sexp_string op in
    let reparsed_nra = sexp_string_to_nra display_nra in
    begin
      Printf.fprintf stdout "\n\t[Round trip successful for %s]\n" fname;
      reparsed_nra
    end
  with
  | Util.CACo_Error msg ->
      Printf.fprintf stdout "\n\t[Round trip FAILED for %s][%s][%s]\n" fname msg (nra_to_sexp_string op);
      op
  | _ ->
      Printf.fprintf stdout "\n\t[Round trip FAILED for %s]\n" fname;
      op
