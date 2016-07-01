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
open Compiler.EnhancedCompiler

(* Configuration utils for the Camp evaluator and compiler *)

type serialization_format =
  | META
  | ENHANCED

type source_lang =
  | RULE
  | OQL

type target_lang =
  | ORIG
  | NRAEnv
  | NNRC
  | DNNRC
  | NNRCMR
  | CLDMR
  | Java
  | JS
  | Spark
  | Spark2
  | Cloudant

type lang_config =
    { mutable slang : source_lang;
      mutable tlang : target_lang;
      cld_conf : cld_config }

let default_eval_lang_config () =
  { slang = RULE;
    tlang = ORIG;
    cld_conf = default_cld_config () }
      
let default_comp_lang_config () =
  { slang = RULE;
    tlang = JS;
    cld_conf = default_cld_config () }
      
let get_source_lang conf = conf.slang
let change_source conf s =
  match s with
  | "Rule" -> conf.slang <- RULE
  | "OQL" -> conf.slang <- OQL
  | _ ->
      Printf.fprintf stderr "Unknown source: %s\n" s;
      raise (CACo_Error ("Unknown source: " ^ s))

let get_target_lang conf = conf.tlang
let change_target conf s =
  match s with
  | "Orig" -> conf.tlang <- ORIG
  | "CAMP" -> conf.tlang <- ORIG (* Deprecated *)
  | "NRAEnv" -> conf.tlang <- NRAEnv
  | "NNRC" -> conf.tlang <- NNRC
  | "DNNRC" -> conf.tlang <- DNNRC
  | "NNRCMR" -> conf.tlang <- NNRCMR
  | "CLDMR" -> conf.tlang <- CLDMR
  | "Java" -> conf.tlang <- Java
  | "JS" | "RHINO" -> conf.tlang <- JS
  | "Spark" -> conf.tlang <- Spark
  | "Spark2" -> conf.tlang <- Spark2
  | "Cloudant" -> conf.tlang <- Cloudant
  | _ ->
      Printf.fprintf stderr "Unknown target: %s\n" s;
      raise (CACo_Error ("Unknown target: " ^ s))

let get_cld_config conf = conf.cld_conf

(* Target language *)
let suffix_rule () = "_rule.camp"
let suffix_oql () = "_oql.txt"
let suffix_nra () = "_nraenv.txt"
let suffix_nrasexp () = "_nraenv.sexp"
let suffix_nrc () = "_nnrc.txt"
let suffix_nrcsexp () = "_nnrc.sexp"
let suffix_dnrc () = "_dnnrc.txt"
let suffix_dnrcsexp () = "_dnnrc.sexp"
let suffix_nrcmr () = "_nnrcmr.txt"
let suffix_nrcmr_spark () = "_nnrcmr_spark.txt"
let suffix_nrcmr_sparksexp () = "_nnrcmr_spark.sexp"
let suffix_nrcmr_spark2 () = "_nnrcmr_spark2.txt"
let suffix_nrcmr_spark2sexp () = "_nnrcmr_spark2.sexp"
let suffix_nrcmr_cldmr () = "_nnrcmr_cldmr.txt"
let suffix_nrcmr_cldmrsexp () = "_nnrcmr_cldmr.sexp"
let suffix_java () = ".java"
let suffix_js () = ".js"
let suffix_spark () = "_spark.scala"
let suffix_spark2 () = "_spark2.scala"
let suffix_cld_design () = "_cloudant_design.json"
let suffix_cld_curl () = "_cloudant.sh"
let suffix_stats () = "_stats.json"

let suffix_target conf =
  match conf.tlang with
  | ORIG ->
      begin
	match conf.slang with
	| RULE -> suffix_rule ()
	| OQL -> suffix_oql ()
      end
  | NRAEnv -> suffix_nra ()
  | NNRC -> suffix_nrc ()
  | DNNRC -> suffix_dnrc ()
  | NNRCMR -> suffix_nrcmr ()
  | CLDMR -> suffix_nrcmr_cldmr ()
  | Java -> suffix_java ()
  | JS -> suffix_js ()
  | Spark -> suffix_spark ()
  | Spark2 -> suffix_spark2 ()
  | Cloudant ->
      begin
	match get_cld (get_cld_config conf) with
	| Design -> suffix_cld_design ()
	| Curl -> suffix_cld_curl ()
      end

(* Evaluator Section *)
  
type eval_config =
    { debug : bool ref;
      eval_only : bool ref;
      mutable eval_io : Data.json option;
      mutable format : serialization_format;
      mutable eval_inputs : string list;
      eval_lang_config : lang_config }

let default_eval_config () =
  { debug = ref false;
    eval_only = ref false;
    eval_io = None;
    format = META;
    eval_inputs = [];
    eval_lang_config = default_eval_lang_config () }

let set_eval_io conf io = conf.eval_io <- Some io
let set_input conf f = conf.eval_inputs <- f :: conf.eval_inputs

let set_format conf s =
  match s with
  | "META" -> conf.format <- META
  | "ENHANCED" -> conf.format <- ENHANCED
  | _ -> ()

let get_format conf = conf.format
let get_eval_lang_config conf = conf.eval_lang_config
let get_eval_only conf = conf.eval_only
let get_debug conf = conf.debug
let get_eval_io conf = conf.eval_io
let get_eval_inputs conf = conf.eval_inputs

(* Data Section *)
  
type data_config =
    { mutable in_jsons : Data.json list;
      mutable data_args : string list }

let default_data_config () =
  { in_jsons = [];
    data_args = [] }

let set_json conf json =
  conf.in_jsons <- json :: conf.in_jsons

(* Compiler Section *)
  
type comp_config =
    { mutable comp_io : Data.json option;
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


