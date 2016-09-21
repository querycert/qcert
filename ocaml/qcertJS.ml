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
open QcertUtil
open Compiler.EnhancedCompiler

let compile source_lang_s target_lang_s q_s =
  begin try
    let source_lang = language_of_name source_lang_s in
    let target_lang = language_of_name target_lang_s in
    let (qname, q) = ParseString.parse_query_from_string source_lang q_s in
    let schema = TypeUtil.empty_schema in
    let brand_model = schema.TypeUtil.sch_brand_model in
    let foreign_typing = schema.TypeUtil.sch_foreign_typing in
    let dv_conf = CompDriver.default_dv_config in
    let q_target =
      CompDriver.compile_from_source_target brand_model foreign_typing dv_conf source_lang target_lang q
    in
    let p_conf = PrettyIL.default_pretty_config () in
    PrettyIL.pretty_query p_conf q_target
  with CACo_Error err -> "compilation error: "^err
  | _ -> "compilation error"
  end

let main input =
    let source = Js.to_string input##.source in
    let target = Js.to_string input##.target in
    let q = Js.to_string input##.query in
    let q_res = compile source target q in
    object%js
        val result = Js.string q_res
    end

let _ = Js.Unsafe.global##.main :=
    Js.wrap_callback main
