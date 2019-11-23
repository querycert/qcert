(*
 * Copyright 2015-2017 IBM Corporation
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
open QcertArg

open QcertCompiler.EnhancedCompiler

(* Configuration utils for the Camp evaluator and compiler *)


type lang_config =
    { mutable slang : string option;
      mutable tlang : string option;
      mutable path : string list }

let default_eval_lang_config () =
  { slang = None; (* default: "rule" *)
    tlang = None; (* default: "rule" *)
    path = [] }

let default_comp_lang_config () =
  { slang = None; (* default: "rule" *)
    tlang = None; (* default: "js" *)
    path = [] }

let get_source_lang conf = conf.slang
let change_source conf s = conf.slang <- Some s
let get_target_lang conf = conf.tlang
let change_target conf s = conf.tlang <- Some s

let get_source_lang_caco conf =
  begin match get_source_lang conf with
  | Some s -> s
  | None -> "camp_rule"
  end
let get_source_lang_caev conf =
  begin match get_source_lang conf with
  | Some s -> s
  | None -> "camp_rule"
  end

let get_target_lang_caco conf =
  begin match get_target_lang conf with
  | Some s -> s
  | None -> "js"
  end
let get_target_lang_caev conf =
  begin match get_target_lang conf with
  | Some s -> s
  | None -> "camp_rule"
  end


let add_path conf s = conf.path <- conf.path @ [s]
let set_path conf path = conf.path <- conf.path @ path
let get_path conf = conf.path

(* Target language *)
let suffix_camp_rule () = "_rule.camp"
let suffix_tech_rule () = "_arl.txt"
let suffix_designer_rule () = "_sem.txt"
let suffix_camp () = "_camp.camp"
let suffix_oql () = "_oql.txt"
let suffix_sql () = "_sql.txt"
let suffix_sqlpp () = "_sqlpp.txt"
let suffix_nra () = "_nra.txt"
let suffix_lambda_nra () = "_lnra.txt"
let suffix_nraenv () = "_nraenv.txt"
let suffix_nraenv_core () = "_nraenv_core.txt"
let suffix_nrasexp () = "_nraenv.sexp"
let suffix_lambda_nrasexp () = "_lambda_nra.sexp"
let suffix_nnrc_core () = "_nnrc_core.txt"
let suffix_nnrc () = "_nnrc.txt"
let suffix_nnrcsexp () = "_nnrc.sexp"
let suffix_dnnrc () = "_dnnrc.txt"
let suffix_dnnrc_typed () = "_tdnnrc.txt"
let suffix_dnnrcsexp () = "_dnnrc.sexp"
let suffix_nnrs () = "_nnrs.txt"
let suffix_nnrs_core () = "_nnrs_core.txt"
let suffix_nnrs_imp () = "_nnrs_imp.txt"
let suffix_imp_qcert () = "_imp_qcert.txt"
let suffix_imp_json () = "_imp_json.txt"
let suffix_nnrcmr () = "_nnrcmr.txt"
let suffix_nnrcmr_spark_df () = "_nnrcmr_spark_df.txt"
let suffix_nnrcmr_spark_dfsexp () = "_nnrcmr_spark_df.sexp"
let suffix_java () = ".java"
let suffix_js_ast () = ".js_ast"
let suffix_javascript () = ".js"
let suffix_spark_df () = "_spark_df.scala"
let suffix_stats () = "_stats.json"
let suffix_error () = ".error"

let suffix_sdata () = ".sio"

let suffix_of_language lang =
  match lang with
  | QcertCompiler.L_camp_rule -> suffix_camp_rule ()
  | QcertCompiler.L_camp -> suffix_camp ()
  | QcertCompiler.L_tech_rule -> suffix_tech_rule ()
  | QcertCompiler.L_designer_rule -> suffix_designer_rule ()
  | QcertCompiler.L_oql -> suffix_oql ()
  | QcertCompiler.L_sql -> suffix_sql ()
  | QcertCompiler.L_sqlpp -> suffix_sql ()
  | QcertCompiler.L_lambda_nra -> suffix_lambda_nra ()
  | QcertCompiler.L_nra -> suffix_nra ()
  | QcertCompiler.L_nraenv -> suffix_nraenv ()
  | QcertCompiler.L_nraenv_core -> suffix_nraenv_core ()
  | QcertCompiler.L_nnrc_core -> suffix_nnrc_core ()
  | QcertCompiler.L_nnrc -> suffix_nnrc ()
  | QcertCompiler.L_dnnrc -> suffix_dnnrc ()
  | QcertCompiler.L_dnnrc_typed -> suffix_dnnrc_typed ()
  | QcertCompiler.L_nnrs -> suffix_nnrs ()
  | QcertCompiler.L_nnrs_core -> suffix_nnrs_core ()
  | QcertCompiler.L_nnrs_imp -> suffix_nnrs_imp ()
  | QcertCompiler.L_imp_qcert -> suffix_imp_qcert ()
  | QcertCompiler.L_imp_json -> suffix_imp_json ()
  | QcertCompiler.L_nnrcmr -> suffix_nnrcmr ()
  | QcertCompiler.L_js_ast -> suffix_js_ast ()
  | QcertCompiler.L_javascript -> suffix_javascript ()
  | QcertCompiler.L_java -> suffix_java ()
  | QcertCompiler.L_spark_df -> suffix_spark_df ()
  | QcertCompiler.L_error _ -> suffix_error ()

(* let suffix_target conf = *)
(*   suffix_of_language (language_of_name (conf.tlang)) *)

(* Evaluator Section *)

type eval_config =
    { debug : bool ref;
      eval_only : bool ref;
      mutable eval_io : QData.json option;
      mutable eval_schema : string option;
      mutable format : serialization_format;
      mutable eval_inputs : string list;
      eval_lang_config : lang_config }

let default_eval_config () =
  { debug = ref false;
    eval_only = ref false;
    eval_io = None;
    eval_schema = None;
    format = META;
    eval_inputs = [];
    eval_lang_config = default_eval_lang_config () }

let set_eval_io conf io = conf.eval_io <- Some io
let set_eval_schema conf schema = conf.eval_schema <- Some schema
let set_input conf f = conf.eval_inputs <- f :: conf.eval_inputs

let set_format conf s =
  match String.lowercase_ascii s with
  | "meta" -> conf.format <- META
  | "enhanced" -> conf.format <- ENHANCED
  | _ -> ()

let get_format conf = conf.format
let get_eval_lang_config conf = conf.eval_lang_config
let get_eval_only conf = conf.eval_only
let get_debug conf = conf.debug
let get_eval_io conf = conf.eval_io
let get_eval_schema conf = conf.eval_schema
let get_eval_inputs conf = conf.eval_inputs

(* Data Section *)

type data_config =
    { mutable in_jsons : QData.json list;
      mutable data_format : serialization_format;
      mutable data_args : string list;
      mutable data_dir : string option;
      mutable data_schema : QData.json option }

let default_data_config () =
  { in_jsons = [];
    data_format = META;
    data_args = [];
    data_dir = None;
    data_schema = None }

let set_json conf json =
  conf.in_jsons <- json :: conf.in_jsons

let set_data_format conf s =
  match String.lowercase_ascii s with
  | "meta" -> conf.data_format <- META
  | "enhanced" -> conf.data_format <- ENHANCED
  | _ -> ()

let set_data_dir conf d = conf.data_dir <- Some d
let set_data_schema conf s = conf.data_schema <- Some s

let get_data_format conf =
  conf.data_format
let get_data_schema conf =
  conf.data_schema
let get_data_dir conf =
  conf.data_dir

(* Compiler Section *)

type comp_config =
    { mutable comp_io : string option;
      mutable dir : string option;
      mutable display_dir : string option;
      mutable comp_inputs : string list;
      target_stats : bool ref;
      target_display : bool ref;
      target_display_sexp : bool ref;
      test_sexp : bool ref;
      comp_lang_config : lang_config;
      comp_pretty_config : PrettyCommon.pretty_config;
      mutable java_imports : string }

let default_comp_config () =
  { comp_io = None;
    dir = None;
    display_dir = None;
    comp_inputs = [];
    target_stats = ref false;
    target_display = ref false;
    target_display_sexp = ref false;
    test_sexp = ref false;
    comp_lang_config = default_comp_lang_config ();
    comp_pretty_config = PrettyCommon.default_pretty_config ();
    java_imports = "" }

let set_comp_io conf io = conf.comp_io <- Some io
let set_comp_input conf f = conf.comp_inputs <- f :: conf.comp_inputs

let set_dir conf d = conf.dir <- Some d
let set_display_dir conf d = conf.display_dir <- Some d
let set_stats conf () = conf.target_stats := true
let set_display conf () = conf.target_display := true
let set_display_sexp conf () = conf.target_display_sexp := true
let set_test_sexp conf () = conf.test_sexp := true

let get_comp_io conf = conf.comp_io
let get_dir conf = conf.dir
let get_display_dir conf = conf.display_dir
let get_comp_inputs conf = conf.comp_inputs
let get_target_display conf = conf.target_display
let get_target_display_sexp conf = conf.target_display_sexp
let get_test_sexp conf = conf.test_sexp
let get_target_stats conf = conf.target_stats
let get_comp_lang_config conf = conf.comp_lang_config
let get_pretty_config conf = conf.comp_pretty_config

(* Backend Section *)

let set_java_imports conf imports = conf.java_imports <- imports
let get_java_imports conf = conf.java_imports
