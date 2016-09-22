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
open QcertConfig
open Compiler.EnhancedCompiler


let set_source gconf s = gconf.gconf_source <- language_of_name s
let set_target gconf s = gconf.gconf_target <- language_of_name s
let add_path gconf s = gconf.gconf_path <- gconf.gconf_path @ [ language_of_name s ]
let set_exact_path gconf () = gconf.gconf_exact_path <- true
let set_dir gconf s = gconf.gconf_dir <- Some s
let set_io gconf file_name = gconf.gconf_io <- Some (Util.string_of_file file_name)
let set_emit_all gconf () = gconf.gconf_emit_all <- true
let set_java_imports gconf s = gconf.gconf_java_imports <- s
let add_input_file gconf file = gconf.gconf_input_files <- gconf.gconf_input_files @ [ file ]
let set_mr_vinit gconf x = gconf.gconf_mr_vinit <- x
let add_vdirst gconf x =
  let x = char_list_of_string x in
  gconf.gconf_vdbindings <- (x, Compiler.Vdistr) :: gconf.gconf_vdbindings
let add_vlocal gconf x =
  let x = char_list_of_string x in
  gconf.gconf_vdbindings <- (x, Compiler.Vlocal) :: gconf.gconf_vdbindings

(* Driver config *)

let driver_conf_of_qcert_conf gconf qname cname =
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

