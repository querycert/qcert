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
module Hack = Compiler
open Compiler.EnhancedCompiler
   

(**********************************)
(* Library functions              *)
(**********************************)

let compile source_lang_s target_lang_s q_s =
  let result =
    begin try
      let source_lang = language_of_name (Js.to_string source_lang_s) in
      let target_lang = language_of_name (Js.to_string target_lang_s) in
      let (qname, q) = ParseString.parse_query_from_string source_lang (Js.to_string q_s) in
      let schema = TypeUtil.empty_schema in
      let brand_model = schema.TypeUtil.sch_brand_model in
      let foreign_typing = schema.TypeUtil.sch_foreign_typing in
      let dv_conf = QDriver.default_dv_config brand_model in
      let q_target =
        QDriver.compile_from_source_target brand_model foreign_typing dv_conf source_lang target_lang q
      in
      let p_conf = PrettyIL.default_pretty_config () in
      PrettyIL.pretty_query p_conf q_target
    with Qcert_Error err -> "compilation error: "^err
    | _ -> "compilation error"
    end
  in
  Js.string result

(**********************************)
(* Configuration support          *)
(**********************************)

(* XXX g is applied to json value if it exists, f is the configuration setter, taking the result of g XXX *)
let apply_gen gconf f g o = Js.Optdef.iter o (fun j -> f gconf (g j))
let apply gconf f o = apply_gen gconf f Js.to_string o
let iter_array gconf f o =
  Js.Optdef.iter o
    (fun a ->
      let a = Js.str_array a in
      ignore (Js.array_map (fun s -> f gconf (Js.to_string s)) a))

(**********************************)
(* Optim. configuration support   *)
(**********************************)

(* Two levels of conversions for optimization configuration:
     json -> ocaml (in QcertArgs.mli) -> Coq (in Compiler.mli).

   Here is the corresponding TypeScript type for the JSON side.
     type QcertOptimStepDescription = {name: string, description:string, lemma:string};

    type QcertOptimPhase = {name: string; optims: string[]; iter: number};
    type QcertOptimConfig = {language: string; phases: QcertOptimPhase[]};

 *)

let optim_conf_ocaml_from_json_conf j : QcertArg.optim_config_ocaml =
  [] (* XXX to be filled XXX *)

(**********************************)
(* Equivalent to qcert cmd        *)
(**********************************)
  
let global_config_of_json j =
  let gconf =
    { gconf_source = Compiler.L_camp_rule;
      gconf_target = Compiler.L_javascript;
      gconf_path = [];
      gconf_exact_path = false;
      gconf_dir = None;
      gconf_dir_target = None;
      gconf_schema = TypeUtil.empty_schema;
      gconf_input = [];
      gconf_output = [];
      gconf_io = None;
      gconf_cld_conf = CloudantUtil.default_cld_config ();
      gconf_emit_all = false;
      gconf_emit_sexp = false;
      gconf_emit_sexp_all = false;
      gconf_eval = false;
      gconf_eval_all = false;
      gconf_eval_debug = false;
      gconf_eval_validate = false;
      gconf_source_sexp = false;
      gconf_pretty_config = PrettyIL.default_pretty_config ();
      gconf_java_imports = "";
      gconf_mr_vinit = "init";
      gconf_stat = false;
      gconf_stat_all = false;
      gconf_stat_tree = false;
      gconf_optim_config = []; }
  in
  (* Specialize apply/iter for this given gconf *)
  let apply_gen = apply_gen gconf in
  let apply = apply gconf in
  let iter_array = iter_array gconf in
  (* Source/Target *)
  apply QcertArg.set_source j##.source;
  apply QcertArg.set_target j##.target;
  (* Compilation path *)
  iter_array QcertArg.add_path j##.path;
  Js.Optdef.iter j##.exactpath (fun b -> gconf.gconf_exact_path <- Js.to_bool b);
  (* Target directory -- XXX is that used? XXX *)
  apply QcertArg.set_dir j##.dir;
  apply QcertArg.set_dir j##.dirtarget;
  (* I/O *)
  apply QcertArg.set_schema_content j##.schema;
  apply QcertArg.set_input_content j##.input;
  (* Cloudant options *)
  Js.Optdef.iter j##.jsruntime
    (fun s -> CloudantUtil.set_harness gconf.gconf_cld_conf (Js.to_string s));
  Js.Optdef.iter j##.cld_prefix
    (fun s -> CloudantUtil.set_prefix gconf.gconf_cld_conf (Js.to_string s));
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
      PrettyIL.set_ascii gconf.gconf_pretty_config ()
    else
      PrettyIL.set_greek gconf.gconf_pretty_config ());
  Js.Optdef.iter j##.margin
    (fun num ->
      let n = int_of_float (Js.float_of_number num) in
      PrettyIL.set_margin gconf.gconf_pretty_config n);
  (* Java options *)
  apply QcertArg.set_java_imports j##.javaimports;
  (* NNRCMR options *)
  apply QcertArg.set_vinit j##.vinit;
  (* Optimization configuration *)
  apply_gen QcertArg.set_optims optim_conf_ocaml_from_json_conf j##.optims;
  (* Return configuration after applying self-consistency constraints *)
  complete_configuration gconf

let wrap_all wrap_f l =
  let a = new%js Js.array_empty in
  List.iter (fun x -> ignore (a##push (wrap_f x))) l;
  a

let json_of_result res =
  let wrap x =
      object%js
        val file = Js.string x.QcertCore.res_file
        val lang = Js.string x.QcertCore.res_lang
        val value = Js.string x.QcertCore.res_content
      end
  in
  object%js
    val emit = Js.def (wrap res.QcertCore.res_emit)
    val emitall = Js.def (wrap_all wrap res.QcertCore.res_emit_all)
    val emitsexp = Js.def (wrap res.QcertCore.res_emit_sexp)
    val emitsexpall = Js.def (wrap_all wrap res.QcertCore.res_emit_sexp_all)
    val result = Js.string res.QcertCore.res_emit.QcertCore.res_content
    val eval = Js.string res.QcertCore.res_eval.QcertCore.res_content
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

let json_of_exported_languages exported_languages =
  let wrap x =
    let ((((_,id),_),lab),desc) = x in
    object%js
      val langid = Js.string (Util.string_of_char_list id)
      val label = Js.string (Util.string_of_char_list lab)
      val description = Js.string (Util.string_of_char_list desc)
    end
  in
  object%js
    val frontend = Js.def (wrap_all wrap exported_languages.Compiler.frontend)
    val intermediate = Js.def (wrap_all wrap exported_languages.Compiler.middleend)
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

let json_of_optim x =
  Js.string (Util.string_of_char_list x)

let js_of_optim_step_list {Hack.optim_step_name; Hack.optim_step_description; Hack.optim_step_lemma} =
  object%js
    val name = Js.string (Util.string_of_char_list optim_step_name)
    val description = Js.string (Util.string_of_char_list optim_step_description)
    val lemma = Js.string (Util.string_of_char_list optim_step_lemma)
  end
  
let json_of_optim_list () =
  let ocl = QDriver.optim_config_list in
  let wrap (Hack.ExistT (x, (optim_module_name, y))) =
    object%js
      val language =
	object%js
	  val name = Js.string (name_of_language x)
	  val modulebase = Js.string (Util.string_of_char_list optim_module_name)
	end
      val optims = Js.def (wrap_all js_of_optim_step_list y)
    end
  in
  object%js
    val optims = Js.def (wrap_all wrap ocl)
  end
  
let js_of_optim_phase x =
  let ((name,optim_list), iter) = x in
  object%js
    val name = Js.string (Util.string_of_char_list name)
    val optims = Js.def (wrap_all json_of_optim optim_list)
    val iter = Js.number_of_float (float_of_int iter)
  end
  
let json_of_optim_default () =
  let ocd = QDriver.optim_config_default in
  let wrap (x,y) =
    object%js
      val language = Js.string (name_of_language x)
      val phases = Js.def (wrap_all js_of_optim_phase y)
    end
  in
  object%js
    val optims = Js.def (wrap_all wrap ocd)
  end
  
let qcert_compile input =
  begin try
    let gconf =
      begin try
	global_config_of_json input
      with exn ->
        raise (Qcert_Error ("[Couldn't load configuration: "^(Printexc.to_string exn)^"]"))
      end
    in
    let q_s =
      begin try
       Js.to_string input##.query
      with exn ->
        raise (Qcert_Error ("[Couldn't load query: "^(Printexc.to_string exn)^"]"))
      end
    in
    let res =
      begin try
        QcertCore.main gconf ("Query.string", q_s)
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
  Js.Unsafe.global##.qcertLanguages :=
    Js.wrap_callback language_specs;
  Js.Unsafe.global##.qcertLanguagesPath :=
    Js.wrap_callback json_of_source_to_target_path;
  Js.Unsafe.global##.qcertOptimList :=
    Js.wrap_callback json_of_optim_list;
  Js.Unsafe.global##.qcertOptimDefaults :=
    Js.wrap_callback json_of_optim_default;
  Js.Unsafe.global##.qcertCompile :=
    Js.wrap_callback qcert_compile


