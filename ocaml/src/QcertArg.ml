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


type qcert_config = {
    mutable qconf_source : CompDriver.language option;
    mutable qconf_target : CompDriver.language option;
    mutable qconf_path : CompDriver.language list;
    mutable qconf_dir : string option;
    mutable qconf_io : string option;
    mutable qconf_schema : TypeUtil.schema;
    qconf_cld_conf : CloudantUtil.cld_config;
    mutable qconf_emit_all : bool;
    mutable qconf_pretty_config : PrettyIL.pretty_config;
    mutable qconf_java_imports : string;
    mutable qconf_input_files : string list;
    mutable qconf_mr_vinit : string;
    mutable qconf_vdbindings : CompDriver.vdbindings;
  }

let language_of_name name =
  let name =
    char_list_of_string (String.lowercase name)
  in
  begin match CompDriver.language_of_name_case_sensitive name with
  | CompDriver.L_error err -> raise (CACo_Error ("Unknown language: "^(string_of_char_list err)))
  | lang -> lang
  end

let default_qconf () =
  { qconf_source = None;
    qconf_target = None;
    qconf_path = [];
    qconf_dir = None;
    qconf_io = None;
    qconf_schema = TypeUtil.empty_schema;
    qconf_cld_conf = CloudantUtil.default_cld_config ();
    qconf_emit_all = false;
    qconf_pretty_config = PrettyIL.default_pretty_config ();
    qconf_java_imports = "";
    qconf_input_files = [];
    qconf_mr_vinit = "init";
    qconf_vdbindings = [];
  }

let set_source qconf s = qconf.qconf_source <- Some (language_of_name s)
let set_target qconf s = qconf.qconf_target <- Some (language_of_name s)
let add_path qconf s = qconf.qconf_path <- qconf.qconf_path @ [ language_of_name s ]
let set_dir qconf s = qconf.qconf_dir <- Some s
let set_io qconf file_name = qconf.qconf_io <- Some (Util.string_of_file file_name)
let set_emit_all qconf () = qconf.qconf_emit_all <- true
let set_java_imports qconf s = qconf.qconf_java_imports <- s
let add_input_file qconf file = qconf.qconf_input_files <- qconf.qconf_input_files @ [ file ]
let set_mr_vinit qconf x = qconf.qconf_mr_vinit <- x
let add_vdirst qconf x =
  let x = char_list_of_string x in
  qconf.qconf_vdbindings <- (x, Compiler.Vdistr) :: qconf.qconf_vdbindings
let add_vlocal qconf x =
  let x = char_list_of_string x in
  qconf.qconf_vdbindings <- (x, Compiler.Vlocal) :: qconf.qconf_vdbindings

(* Driver config *)

let driver_conf_of_qcert_conf qconf qname =
  let brand_rel =
    TypeUtil.brand_relation_of_brand_model qconf.qconf_schema.TypeUtil.sch_brand_model
  in
  { CompDriver.comp_qname = char_list_of_string qname;
    comp_brand_rel = brand_rel;
    comp_mr_vinit = char_list_of_string qconf.qconf_mr_vinit;
    comp_vdbindings = qconf.qconf_vdbindings;
    comp_java_imports = char_list_of_string qconf.qconf_java_imports; }

