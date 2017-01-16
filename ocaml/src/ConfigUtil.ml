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
open CloudantUtil
open DataUtil
open Compiler.EnhancedCompiler
open QcertArg

(* Configuration utils for the Camp evaluator and compiler *)


type lang_config =
    { mutable slang : string option;
      mutable tlang : string option;
      mutable path : string list;
      cld_conf : cld_config }

let default_eval_lang_config () =
  { slang = None; (* default: "rule" *)
    tlang = None; (* default: "rule" *)
    path = [];
    cld_conf = default_cld_config () }

let default_comp_lang_config () =
  { slang = None; (* default: "rule" *)
    tlang = None; (* default: "js" *)
    path = [];
    cld_conf = default_cld_config () }

let get_source_lang conf = conf.slang
let change_source conf s = conf.slang <- Some s
let get_target_lang conf = conf.tlang
let change_target conf s = conf.tlang <- Some s

let get_source_lang_caco conf =
  begin match get_source_lang conf with
  | Some s -> s
  | None -> "rule"
  end
let get_source_lang_caev conf =
  begin match get_source_lang conf with
  | Some s -> s
  | None -> "rule"
  end

let get_target_lang_caco conf =
  begin match get_target_lang conf with
  | Some s -> s
  | None -> "js"
  end
let get_target_lang_caev conf =
  begin match get_target_lang conf with
  | Some s -> s
  | None -> "rule"
  end


let add_path conf s = conf.path <- conf.path @ [s]
let set_path conf path = conf.path <- conf.path @ path
let get_path conf = conf.path

let get_cld_config conf = conf.cld_conf

(* Target language *)
let suffix_rule () = "_rule.camp"
let suffix_camp () = "_camp.camp"
let suffix_oql () = "_oql.txt"
let suffix_sql () = "_sql.txt"
let suffix_nra () = "_nra.txt"
let suffix_lambda_nra () = "_lnra.txt"
let suffix_nraenv () = "_nraenv.txt"
let suffix_nraenv_core () = "_nraenv_core.txt"
let suffix_nrasexp () = "_nraenv.sexp"
let suffix_lambda_nrasexp () = "_lambda_nra.sexp"
let suffix_nnrc_core () = "_nnrc_core.txt"
let suffix_nnrc () = "_nnrc.txt"
let suffix_nnrcsexp () = "_nnrc.sexp"
let suffix_dnnrc_dataset () = "_dnnrc.txt"
let suffix_dnnrc_typed_dataset () = "_dnnrc.txt"
let suffix_dnnrcsexp () = "_dnnrc.sexp"
let suffix_nnrcmr () = "_nnrcmr.txt"
let suffix_nnrcmr_spark_rdd () = "_nnrcmr_spark_rdd.txt"
let suffix_nnrcmr_spark_rddsexp () = "_nnrcmr_spark_rdd.sexp"
let suffix_nnrcmr_spark_dataset () = "_nnrcmr_spark_dataset.txt"
let suffix_nnrcmr_spark_datasetsexp () = "_nnrcmr_spark_dataset.sexp"
let suffix_nnrcmr_cldmr () = "_nnrcmr_cldmr.txt"
let suffix_nnrcmr_cldmrsexp () = "_nnrcmr_cldmr.sexp"
let suffix_java () = ".java"
let suffix_javascript () = ".js"
let suffix_spark_rdd () = "_spark_rdd.scala"
let suffix_spark_dataset () = "_spark_dataset.scala"
let suffix_cld_design () = "_cloudant_design.json"
let suffix_stats () = "_stats.json"
let suffix_error () = ".error"

let suffix_sdata () = ".sio"

let suffix_of_language lang =
  match lang with
  | Compiler.L_rule -> suffix_rule ()
  | Compiler.L_camp -> suffix_camp ()
  | Compiler.L_oql -> suffix_oql ()
  | Compiler.L_sql -> suffix_sql ()
  | Compiler.L_lambda_nra -> suffix_lambda_nra ()
  | Compiler.L_nra -> suffix_nra ()
  | Compiler.L_nraenv -> suffix_nraenv ()
  | Compiler.L_nraenv_core -> suffix_nraenv_core ()
  | Compiler.L_nnrc_core -> suffix_nnrc_core ()
  | Compiler.L_nnrc -> suffix_nnrc ()
  | Compiler.L_dnnrc_dataset -> suffix_dnnrc_dataset ()
  | Compiler.L_dnnrc_typed_dataset -> suffix_dnnrc_typed_dataset ()
  | Compiler.L_nnrcmr -> suffix_nnrcmr ()
  | Compiler.L_cldmr -> suffix_nnrcmr_cldmr ()
  | Compiler.L_javascript -> suffix_javascript ()
  | Compiler.L_java -> suffix_java ()
  | Compiler.L_spark_rdd -> suffix_spark_rdd ()
  | Compiler.L_spark_dataset -> suffix_spark_dataset ()
  | Compiler.L_cloudant -> suffix_cld_design ()
  | Compiler.L_error _ -> suffix_error ()

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
  match String.lowercase s with
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
  match String.lowercase s with
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
      comp_pretty_config : PrettyIL.pretty_config;
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
    comp_pretty_config = PrettyIL.default_pretty_config ();
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
