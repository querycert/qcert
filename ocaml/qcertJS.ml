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

let global_config_and_query_of_json j =
  let gconf =
    { gconf_source = CompDriver.L_rule;
      gconf_target = CompDriver.L_javascript;
      gconf_path = [];
      gconf_exact_path = false;
      gconf_dir = None;
      gconf_dir_target = None;
      gconf_io = None;
      gconf_schema = TypeUtil.empty_schema;
      gconf_cld_conf = CloudantUtil.default_cld_config ();
      gconf_emit_all = false;
      gconf_emit_sexp = false;
      gconf_emit_sexp_all = false;
      gconf_pretty_config = PrettyIL.default_pretty_config ();
      gconf_java_imports = "";
      gconf_input_files = [];
      gconf_mr_vinit = "init";
      gconf_vdbindings = []; }
  in
  let apply f o =
    Js.Optdef.iter o (fun s -> f gconf (Js.to_string s));
  in
  let iter_array f o =
    Js.Optdef.iter o
      (fun a -> ignore (Js.array_map (fun s -> f gconf (Js.to_string s)) a))
  in
  apply QcertArg.set_source j##.source;
  apply QcertArg.set_target j##.target;
  iter_array QcertArg.add_path j##.path;
  Js.Optdef.iter j##.exact_path (fun b -> gconf.gconf_exact_path <- Js.to_bool b);
  apply QcertArg.set_dir j##.dir;
  apply QcertArg.set_dir j##.dirtarget;
  Js.Optdef.iter j##.jsruntime
    (fun s -> CloudantUtil.set_harness gconf.gconf_cld_conf (Js.to_string s));
  apply QcertArg.set_io j##.io;
  Js.Optdef.iter j##.emitall (fun b -> gconf.gconf_emit_all <- Js.to_bool b);
  Js.Optdef.iter j##.emitsexp (fun b -> gconf.gconf_emit_sexp <- Js.to_bool b);
  Js.Optdef.iter j##.emitsexpall (fun b -> gconf.gconf_emit_sexp_all <- Js.to_bool b);
  Js.Optdef.iter j##.ascii
    (fun b -> if Js.to_bool b then
      PrettyIL.set_ascii gconf.gconf_pretty_config ()
    else
      PrettyIL.set_greek gconf.gconf_pretty_config ());
  Js.Optdef.iter j##.margin
    (fun num ->
      let n = int_of_float (Js.float_of_number num) in
      PrettyIL.set_margin gconf.gconf_pretty_config n);
  Js.Optdef.iter j##.cld_prefix
    (fun s -> CloudantUtil.set_prefix gconf.gconf_cld_conf (Js.to_string s));
  apply QcertArg.set_java_imports j##.javaimports;
  apply QcertArg.set_vinit j##.vinit;
  iter_array QcertArg.add_vdirst j##.vdistr;
  iter_array QcertArg.add_vlocal j##.vlocal;
  (complet_configuration gconf, j##.query)

let compile gconf q_s =
  let result =
    begin try
      let source_lang = gconf.gconf_source in
      let target_lang = gconf.gconf_target in
      let (qname, q) = ParseString.parse_query_from_string source_lang (Js.to_string q_s) in
      let schema = TypeUtil.empty_schema in
      let brand_model = schema.TypeUtil.sch_brand_model in
      let foreign_typing = schema.TypeUtil.sch_foreign_typing in
      let dv_conf = QcertConfig.driver_conf_of_global_conf gconf "MyQuery" "MyClass" in
      let q_target =
        CompDriver.compile_from_source_target brand_model foreign_typing dv_conf source_lang target_lang q
      in
      let p_conf = gconf.gconf_pretty_config in
      PrettyIL.pretty_query p_conf q_target
    with CACo_Error err -> "compilation error: "^err
    | _ -> "compilation error"
    end
  in
  Js.string result

let main input =
  try
    let (gconf,q_s) =
      try
	global_config_and_query_of_json input
      with _ -> raise (CACo_Error "[Couldn't load configuration]")
    in
    let q_res = compile gconf q_s in
    object%js
        val result = q_res
    end
  with
  | CACo_Error msg ->
      object%js
        val result = Js.string msg
    end

let _ =
  Js.Unsafe.global##.main :=
    Js.wrap_callback main
