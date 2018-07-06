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
open DataUtil

open QcertCompiler.EnhancedCompiler

type io_kind =
  | IO_file of string option
  | IO_components of string option * string option * string option
  
type global_config = {
    mutable gconf_qname : string option; (* Query name *)
    mutable gconf_source : QLang.language;
    mutable gconf_target : QLang.language;
    mutable gconf_path : QLang.language list; (* the first element of the path must be source and the last target *)
    mutable gconf_exact_path : bool;
    mutable gconf_dir : string option;
    mutable gconf_dir_target : string option;
    (* Schema, input, output *)
    mutable gconf_io : io_kind option;
    mutable gconf_schema : TypeUtil.schema;
    mutable gconf_input : content_input;
    mutable gconf_output : content_output;
    mutable gconf_emit_all : bool;
    gconf_pretty_config : PrettyCommon.pretty_config;
    mutable gconf_emit_sexp : bool;
    mutable gconf_emit_sexp_all : bool;
    mutable gconf_eval : bool;
    mutable gconf_eval_all : bool;
    mutable gconf_eval_debug : bool;
    mutable gconf_eval_validate : bool;
    mutable gconf_source_sexp : bool;
    mutable gconf_java_imports : string;
    mutable gconf_mr_vinit : string;
    mutable gconf_stat : bool;
    mutable gconf_stat_all : bool;
    mutable gconf_stat_tree : bool;
    mutable gconf_optim_config_file : string option;
    mutable gconf_emit_optim_config : bool;
    mutable gconf_optim_config : QDriver.optim_config;
    mutable gconf_prefix : string;
  }

let inheritance_of_conf gconf =
  TypeUtil.inheritance_of_schema (gconf.gconf_schema)

let parse_io f =
  begin match f with
  | None -> (None,None,None)
  | Some f -> get_io_components (Some (ParseFile.parse_io_from_file f))
  end

let parse_json_component f =
  begin match f with
  | None -> None
  | Some f -> Some (ParseString.parse_json_from_string f)
  end

let parse_io_kind gconf =
  begin match gconf.gconf_io with
  | None -> (None,None,None)
  | Some (IO_file f) -> parse_io f
  | Some (IO_components (fin,fout,fschema)) ->
      (parse_json_component fin,
       parse_json_component fout,
       parse_json_component fschema)
  end
    
(* Optimization support *)

let complete_configuration gconf =
  let _optim_config =
    begin match gconf.gconf_optim_config_file with
    | Some f ->
	let optim_json = ParseFile.parse_json_from_file f in
	let optim_conf = build_optim_config optim_json in
	gconf.gconf_optim_config <- optim_conf
    | None -> ()
    end
  in
  let (io_input,io_output,io_schema) = parse_io_kind gconf in
  let _schema =
    begin match io_schema with
    | Some io -> gconf.gconf_schema <- TypeUtil.schema_of_io_json io
    | None -> ()
    end
  in
  let h = inheritance_of_conf gconf in
  let _input =
    begin match io_input with
    | Some io -> gconf.gconf_input <- (build_input META h io)
    | None -> ()
    end
  in
  let _output =
    begin match io_output with
    | Some io -> gconf.gconf_output <- build_output h io
    | None -> ()
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
                (QDriver.get_path_from_source_target lang1 lang2) @ post
            | [] -> assert false
            end)
          (gconf.gconf_source :: gconf.gconf_path) [ gconf.gconf_target ]
  end;
  gconf

(* Driver config *)

let driver_conf_of_global_conf gconf qname cname =
  let brand_rel = TypeUtil.brand_relation_of_brand_model gconf.gconf_schema.TypeUtil.sch_brand_model in
  let constants_config = gconf.gconf_schema.TypeUtil.sch_globals in
  { QcertCompiler.comp_qname = char_list_of_string qname;
    QcertCompiler.comp_qname_lowercase = char_list_of_string (String.lowercase_ascii (gconf.gconf_prefix ^ qname));
    comp_class_name = char_list_of_string cname;
    comp_brand_rel = brand_rel;
    comp_mr_vinit = char_list_of_string gconf.gconf_mr_vinit;
    comp_constants = constants_config;
    comp_java_imports = char_list_of_string gconf.gconf_java_imports;
    comp_optim_config = gconf.gconf_optim_config; }
