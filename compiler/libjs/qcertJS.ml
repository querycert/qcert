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

open Js_of_ocaml

open Qcert_coq
open Util
open Compiler.EnhancedCompiler

open Qcert_lib
open Qcert_util
open Config


(**********************************)
(* Configuration support          *)
(**********************************)

(* XXX g is applied to json value if it exists, f is the configuration setter, taking the result of g XXX *)
let apply_gen gconf f g o = Js.Optdef.iter o (fun j -> f gconf (g j))
let apply gconf f o = apply_gen gconf f Js.to_string o
let apply_int gconf f o = apply_gen gconf f (fun x ->  int_of_float (Js.float_of_number x)) o
let iter_array_gen gconf f o = Js.Optdef.iter o (fun a -> f gconf a)
let iter_array gconf f o =
  iter_array_gen gconf
    (fun gconf a ->
      let a = Js.str_array a in
      ignore (Js.array_map (fun s -> f gconf (Js.to_string s)) a)) o
let map_array_gen gconf f o =
  Js.Optdef.map o
    (fun a -> f gconf a)

(**********************************)
(* Optim. configuration support   *)
(**********************************)

let optim_config_from_json s : QDriver.optim_config =
  let optim_json = Parse_string.parse_json_from_string s in
  Data_util.build_optim_config optim_json

(**********************************)
(* Equivalent to qcert cmd        *)
(**********************************)

let global_config_of_json j =
  let gconf =
    { gconf_qname = None;
      gconf_source = Compiler.L_camp_rule;
      gconf_target = Compiler.L_javascript;
      gconf_path = [];
      gconf_exact_path = false;
      gconf_dir = None;
      gconf_dir_target = None;
      gconf_schema = Type_util.empty_schema;
      gconf_input = [];
      gconf_output = QData.dunit;
      gconf_io = None;
      gconf_emit_all = false;
      gconf_emit_sexp = false;
      gconf_emit_sexp_all = false;
      gconf_eval = false;
      gconf_eval_all = false;
      gconf_eval_debug = false;
      gconf_eval_validate = false;
      gconf_source_sexp = false;
      gconf_pretty_config = Pretty_common.default_pretty_config ();
      gconf_java_imports = "";
      gconf_mr_vinit = "init";
      gconf_stat = false;
      gconf_stat_all = false;
      gconf_stat_tree = false;
      gconf_optim_config_file = None;
      gconf_emit_optim_config = false;
      gconf_optim_config = [];
      gconf_prefix = ""; }
  in
  (* Specialize apply/iter for this given gconf *)
  let apply = apply gconf in
  let iter_array = iter_array gconf in
  (* Source/Target *)
  apply Args.set_qname j##.qname;
  apply Args.set_source j##.source;
  apply Args.set_target j##.target;
  (* Compilation path *)
  iter_array Args.add_path j##.path;
  Js.Optdef.iter j##.exactpath (fun b -> gconf.gconf_exact_path <- Js.to_bool b);
  (* Target directory -- XXX is that used? XXX *)
  apply Args.set_dir j##.dir;
  apply Args.set_dir j##.dirtarget;
  (* I/O *)
  apply Args.set_schema_content j##.schema;
  apply Args.set_output_content j##.output;
  apply Args.set_input_content j##.input;
  (* Cloudant options *)
  Js.Optdef.iter j##.jsruntime (fun b -> if b then Args.set_link_js_runtime gconf ());
  Js.Optdef.iter j##.cld_prefix
    (fun s -> Args.set_prefix gconf (Js.to_string s));
  (* Emit options *)
  Js.Optdef.iter j##.emitall (fun b -> gconf.gconf_emit_all <- Js.to_bool b);
  Js.Optdef.iter j##.emitsexp (fun b -> gconf.gconf_emit_sexp <- Js.to_bool b);
  Js.Optdef.iter j##.emitsexpall (fun b -> gconf.gconf_emit_sexp_all <- Js.to_bool b);
  (* Eval options *)
  Js.Optdef.iter j##.eval (fun b -> gconf.gconf_eval <- Js.to_bool b);
  Js.Optdef.iter j##.evalall (fun b -> gconf.gconf_eval_all <- Js.to_bool b);
  (* Source options *)
  Js.Optdef.iter j##.sourcesexp (fun b -> gconf.gconf_source_sexp <- Js.to_bool b);
  (* Pretty-printing options *)
  Js.Optdef.iter j##.ascii
    (fun b -> if Js.to_bool b then
      Pretty_common.set_ascii gconf.gconf_pretty_config ()
    else
      Pretty_common.set_greek gconf.gconf_pretty_config ());
  Js.Optdef.iter j##.margin
    (fun num ->
      let n = int_of_float (Js.float_of_number num) in
      Pretty_common.set_margin gconf.gconf_pretty_config n);
  (* Java options *)
  apply Args.set_java_imports j##.javaimports;
  (* NNRCMR options *)
  apply Args.set_vinit j##.vinit;
  (* Optimization configuration *)
  apply (fun gconf o -> Args.set_optims gconf (optim_config_from_json o)) j##.optims;
  (* Return configuration after applying self-consistency constraints *)
  complete_configuration gconf

let wrap_all wrap_f l =
  let a = new%js Js.array_empty in
  List.iter (fun x -> ignore (a##push (wrap_f x))) l;
  a

let json_of_result res =
  let wrap x =
      object%js
        val file = Js.string x.Core.res_file
        val lang = Js.string x.Core.res_lang
        val value = Js.string x.Core.res_content
      end
  in
  object%js
    val emit = Js.def (wrap res.Core.res_emit)
    val emitall = Js.def (wrap_all wrap res.Core.res_emit_all)
    val emitsexp = Js.def (wrap res.Core.res_emit_sexp)
    val emitsexpall = Js.def (wrap_all wrap res.Core.res_emit_sexp_all)
    val result = Js.string res.Core.res_emit.Core.res_content
    val eval = Js.string res.Core.res_eval.Core.res_content
  end

let json_of_error msg =
  object%js
    val emit = Js.undefined
    val emitall = Js.undefined
    val emitsexp = Js.undefined
    val emitsexpall = Js.undefined
    val result = Js.string msg
    val eval = Js.string msg
  end

let json_of_validate_error msg =
  object%js
    val result = Js.bool false
    val error = Js.def (Js.string msg)
  end

let json_of_exported_languages exported_languages =
  let wrap x =
    let ((((_,id),_),lab),desc) = x in
    object%js
      val langid = Js.string (string_of_char_list id)
      val label = Js.string (string_of_char_list lab)
      val description = Js.string (string_of_char_list desc)
    end
  in
  object%js
    val frontend = Js.def (wrap_all wrap exported_languages.Compiler.frontend)
    val core = Js.def (wrap_all wrap exported_languages.Compiler.coreend)
    val distributed = Js.def (wrap_all wrap exported_languages.Compiler.distrend)
    val backend =  Js.def (wrap_all wrap exported_languages.Compiler.backend)
  end
let language_specs () =
  let exported_languages = QLang.export_language_descriptions  in
  json_of_exported_languages exported_languages

let json_of_source_to_target_path j =
  let source_lang = language_of_name (Js.to_string j##.source) in
  let target_lang = language_of_name (Js.to_string j##.target) in
  let path_lang = QDriver.get_path_from_source_target source_lang target_lang in
  let path = List.map name_of_language path_lang in
  let wrap x = Js.string x in
  object%js
    val path = Js.def (wrap_all wrap path)
  end

let rec unsafe_json_to_js (j:QData.json) =
  match j with
  | Compiler.Jnull -> Js.Unsafe.inject (Js.null)
  | Compiler.Jnumber n -> Js.Unsafe.inject (Js.number_of_float n)
  | Compiler.Jbigint n -> Js.Unsafe.inject (Js.number_of_float (float_of_int n)) (* XXX Coerce bigint to number *)
  | Compiler.Jbool b -> Js.Unsafe.inject (Js.bool b)
  | Compiler.Jstring str -> Js.Unsafe.inject (Js.string (string_of_char_list str))
  | Compiler.Jarray a -> Js.Unsafe.inject (wrap_all unsafe_json_to_js a)
  | Compiler.Jobject l ->
     Js.Unsafe.inject (Js.Unsafe.obj (Array.of_list (List.map (fun (str,y) -> ((string_of_char_list str, unsafe_json_to_js y))) l)))
  

let json_of_optim_list() = unsafe_json_to_js QDriver.optim_config_list_to_json

let json_of_optim_default() =
  object%js
    val optims = unsafe_json_to_js QDriver.optim_config_default_to_json
  end
  
let build_config input =
  begin try
	  global_config_of_json input
  with exn ->
    raise (Qcert_Error ("[Couldn't load configuration: "^(Printexc.to_string exn)^"]"))
  end

let validate_output input =
  begin try
    let gconf = input##.gconf in
    let actual = Js.to_string input##.actual in
    let actual_output =
      try Config.data_of_string gconf actual with
      | err ->
          raise (Qcert_Error ("Cannot convert data " ^ actual))
    in
    let expected_output = gconf.gconf_output in
    let queryname = Js.to_string input##.queryName in
    let language_name = Js.to_string input##.source in
    (object%js
      val result = Js.bool (Check_util.validate_result true queryname language_name expected_output (Some actual_output))
      val error = Js.undefined
     end)
  with
  | Qcert_Error msg -> json_of_validate_error msg
  | exn -> json_of_validate_error ("[Main error: "^(Printexc.to_string exn)^"]")
  end

let qcert_compile input =
  begin try
    let gconf = input##.gconf in
    let q_s =
      begin try
       Js.to_string input##.query
      with exn ->
        raise (Qcert_Error ("[Couldn't load query: "^(Printexc.to_string exn)^"]"))
      end
    in
    let res =
      begin try
        Core.main gconf ("Query.string", q_s)
      with Qcert_Error err -> raise (Qcert_Error ("[Compilation error: "^err^"]"))
      | exn -> raise (Qcert_Error ("[Compilation error: "^(Printexc.to_string exn)^"]"))
      end
    in
    json_of_result res
  with
  | Qcert_Error msg -> json_of_error msg
  | exn -> json_of_error ("[Main error: "^(Printexc.to_string exn)^"]")
  end

let _ =
  Js.export "Qcert" (object%js
    val languages = Js.wrap_callback language_specs;
    val languagesPath = Js.wrap_callback json_of_source_to_target_path
    val optimList = Js.wrap_callback json_of_optim_list
    val optimDefaults = Js.wrap_callback json_of_optim_default
    val buildConfig = Js.wrap_callback build_config
    val validateOutput = Js.wrap_callback validate_output
    val compile = Js.wrap_callback qcert_compile
   end)
