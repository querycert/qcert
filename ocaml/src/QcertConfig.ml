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
open Compiler.EnhancedCompiler

type global_config = {
    mutable gconf_source : CompDriver.language;
    mutable gconf_target : CompDriver.language;
    mutable gconf_path : CompDriver.language list; (* the first element of the path must be source and the last target *)
    mutable gconf_exact_path : bool;
    mutable gconf_dir : string option;
    mutable gconf_dir_target : string option;
    mutable gconf_io : string option;
    mutable gconf_schema : TypeUtil.schema;
    gconf_cld_conf : CloudantUtil.cld_config;
    mutable gconf_emit_all : bool;
    gconf_pretty_config : PrettyIL.pretty_config;
    mutable gconf_emit_sexp : bool;
    mutable gconf_emit_sexp_all : bool;
    mutable gconf_source_sexp : bool;
    mutable gconf_java_imports : string;
    mutable gconf_mr_vinit : string;
    mutable gconf_vdbindings : CompDriver.vdbindings;
  }

let complet_configuration gconf =
  let _schema =
    begin match gconf.gconf_io with
    | Some io ->
        gconf.gconf_schema <- TypeUtil.schema_of_io_json (ParseString.parse_io_from_string io)
    | None ->
        ()
    end
  in
  begin match gconf.gconf_exact_path with
  | true ->
      gconf.gconf_path <-
        gconf.gconf_source :: gconf.gconf_path @ [ gconf.gconf_target ]
  | false ->
      gconf.gconf_path <-
        List.fold_right
          (fun lang1 acc ->
            begin match acc with
            | lang2 :: post ->
                (CompDriver.get_path_from_source_target lang1 lang2) @ post
            | [] -> assert false
            end)
          (gconf.gconf_source :: gconf.gconf_path) [ gconf.gconf_target ]
  end;
  gconf

(* Driver config *)

let driver_conf_of_global_conf gconf qname cname =
  let brand_rel =
    TypeUtil.brand_relation_of_brand_model gconf.gconf_schema.TypeUtil.sch_brand_model
  in
  { CompDriver.comp_qname = char_list_of_string qname;
    CompDriver.comp_class_name = char_list_of_string cname;
    comp_brand_rel = brand_rel;
    comp_input_type = gconf.gconf_schema.TypeUtil.sch_camp_type;
    comp_mr_vinit = char_list_of_string gconf.gconf_mr_vinit;
    comp_vdbindings = gconf.gconf_vdbindings;
    comp_java_imports = char_list_of_string gconf.gconf_java_imports; }
