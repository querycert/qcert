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
    qconf_cld_conf : CloudantUtil.cld_config;
    mutable qconf_display : bool;
    mutable qconf_display_dir : string option;
    mutable qconf_display_config : PrettyIL.pretty_config;
    mutable qconf_java_imports : string;
    mutable qconf_input_files : string list;
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
    qconf_cld_conf = CloudantUtil.default_cld_config ();
    qconf_display = false;
    qconf_display_dir = None;
    qconf_display_config = PrettyIL.default_pretty_config ();
    qconf_java_imports = "";
    qconf_input_files = [];
  }

let set_source qconf s = qconf.qconf_source <- Some (language_of_name s)
let set_target qconf s = qconf.qconf_target <- Some (language_of_name s)
let add_path qconf s = qconf.qconf_path <- qconf.qconf_path @ [ language_of_name s ]
let set_dir qconf s = qconf.qconf_dir <- Some s
let set_io qconf file_name = qconf.qconf_io <- Some (Util.string_of_file file_name)
let set_display qconf () = qconf.qconf_display <- true
let set_display_dir qconf d = qconf.qconf_display_dir <- Some d
let set_java_imports qconf s = qconf.qconf_java_imports <- s
let add_input_file qconf file = qconf.qconf_input_files <- qconf.qconf_input_files @ [ file ]


(* Driver config *)

let driver_conf_of_qcert_conf qconf (* schema *) qname =
  let path = qconf.qconf_path in
  let brand_rel =
    [] (* XXX TODO XXX *)
  in
  let vdbindings =
    [] (* XXX TODO XXX *)
  in
  (* let schema = *)
  (*   begin match schema with *)
  (*   | Some schema -> schema *)
  (*   | None -> *)
  (*       (\* XXX TODO XXX *\) *)
  (*       (\* (RType.make_brand_model brand_rel [], []) *\) *)
  (*       assert false *)
  (*   end *)
  (* in *)
  { CompDriver.comp_qname = char_list_of_string qname;
    comp_path = path;
    comp_brand_rel = brand_rel;
    (* comp_schema = schema; *)
    comp_vdbindings = vdbindings;
    comp_java_imports = char_list_of_string qconf.qconf_java_imports; }

