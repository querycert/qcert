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
open CompDriver


type language_or_optim =
  | LoO_optim
  | LoO_language of language

type driver_config = {
    comp_qname : char list;
    comp_path : language_or_optim list;
    comp_brand : (char list * char list) list;
    comp_schema : RType.brand_model * RType.camp_type;
    comp_vdbindings : vdbindings;
    comp_java_imports : char list;
  }

let get_path conf = conf.comp_path
let get_brand conf = conf.comp_brand
let get_schema conf = conf.comp_schema

let language_of_name name =
  begin match String.lowercase name with
  | "rule" -> L_rule
  | "camp" -> L_camp
  | "oql" -> L_oql
  | "nraenv" -> L_nraenv
  | "nnrc" -> L_nnrc
  | "nnrcmr" -> L_nnrcmr
  | "cldmr" -> L_cldmr
  | "dnnrc" -> L_dnnrc_dataset
  | "rhino" | "js" -> L_javascript
  | "java" -> L_java
  | "spark" -> L_spark
  | "spark2" -> L_spark2
  | "cloudant" -> L_cloudant
  (* Not supported: *)
  | "nra" -> L_nra
  | "dnnrc_typed" -> L_dnnrc_typed_dataset
  | "error" -> L_error
  | _ -> raise (CACo_Error ("Not a valid language: " ^ name))
  end

let name_of_language lang =
  begin match lang with
  | L_rule -> "rule"
  | L_camp -> "camp"
  | L_oql -> "oql"
  | L_nra -> "nra"
  | L_nraenv -> "nraenv"
  | L_nnrc -> "nnrc"
  | L_nnrcmr -> "nnrcmr"
  | L_cldmr -> "cldmr"
  | L_dnnrc_dataset -> "dnnrc"
  | L_dnnrc_typed_dataset -> "dnnrc_typed"
  | L_javascript -> "javascript"
  | L_java -> "java"
  | L_spark -> "spark"
  | L_spark2 -> "spark2"
  | L_cloudant -> "cloudant"
  | L_error -> "error"
  end

let name_of_driver dv =
  begin match dv with
  | Dv_nra _ -> "nra"
  | Dv_nraenv _ -> "nraenv"
  | Dv_nnrc _ -> "nnrc"
  | Dv_nnrcmr _ -> "nnrcmr"
  | Dv_rule _ -> "rule"
  | Dv_camp _ -> "camp"
  | Dv_oql _ -> "oql"
  | Dv_cldmr _ -> "cldmr"
  | Dv_dnnrc_dataset _ -> "dnnrc_dataset"
  | Dv_dnnrc_typed_dataset _ -> "dnnrc_typed_dataset"
  | Dv_javascript _ -> "javascript"
  | Dv_java _ -> "java"
  | Dv_spark _ -> "spark"
  | Dv_spark2 _ -> "spark2"
  | Dv_cloudant _ -> "cloudant"
  end

let language_or_optim_of_name name =
  begin match String.lowercase name with
  | "optim" -> LoO_optim
  | lang -> LoO_language (language_of_name lang)
  end

let push_optim dv =
  begin match dv with
  | Dv_nra dv -> Dv_nra (Dv_nra_optim dv)
  | Dv_nraenv dv -> Dv_nraenv (Dv_nraenv_optim dv)
  | Dv_nnrc dv -> Dv_nnrc (Dv_nnrc_optim dv)
  | Dv_nnrcmr dv -> Dv_nnrcmr (Dv_nnrcmr_optim dv)
  | Dv_rule _
  | Dv_camp _
  | Dv_oql _
  | Dv_cldmr _
  | Dv_dnnrc_dataset _
  | Dv_dnnrc_typed_dataset _
  | Dv_javascript _
  | Dv_java _
  | Dv_spark _
  | Dv_spark2 _
  | Dv_cloudant _ ->
      raise (CACo_Error ("No optimiation for "^(name_of_driver dv)))
  end

let push_translation config lang dv =
  begin match lang with
  | L_rule ->
      begin match dv with
      | Dv_camp dv -> Dv_rule (Dv_rule_to_camp dv)
      | Dv_nraenv dv -> Dv_rule (Dv_rule_to_nraenv dv)
      | Dv_nra dv -> Dv_rule (Dv_rule_to_nra dv)
      | Dv_rule _
      | Dv_oql _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ ->
          raise (CACo_Error ("No compilation path from "^(name_of_language lang)^" to "^(name_of_driver dv)))
      end
  | L_camp ->
      begin match dv with
      | Dv_nraenv dv -> Dv_camp (Dv_camp_to_nraenv dv)
      | Dv_nra dv -> Dv_camp (Dv_camp_to_nra dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ ->
          raise (CACo_Error ("No compilation path from "^(name_of_language lang)^" to "^(name_of_driver dv)))
      end
  | L_oql ->
      begin match dv with
      | Dv_nraenv dv -> Dv_oql (Dv_oql_to_nraenv dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_nra _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ ->
          raise (CACo_Error ("No compilation path from "^(name_of_language lang)^" to "^(name_of_driver dv)))
      end
  | L_nra ->
      begin match dv with
      | Dv_nnrc dv -> Dv_nra (Dv_nra_to_nnrc dv)
      | Dv_nraenv dv -> Dv_nra (Dv_nra_to_nraenv dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_nra _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ ->
          raise (CACo_Error ("No compilation path from "^(name_of_language lang)^" to "^(name_of_driver dv)))
      end
  | L_nraenv ->
      begin match dv with
      | Dv_nnrc dv -> Dv_nraenv (Dv_nraenv_to_nnrc dv)
      | Dv_nra dv -> Dv_nraenv (Dv_nraenv_to_nra dv)
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_nraenv _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ ->
          raise (CACo_Error ("No compilation path from "^(name_of_language lang)^" to "^(name_of_driver dv)))
      end
  | L_nnrc ->
      begin match dv with
      | Dv_nnrcmr dv -> Dv_nnrc (Dv_nnrc_to_nnrcmr (config.comp_vdbindings, dv))
      | Dv_dnnrc_dataset dv -> Dv_nnrc (Dv_nnrc_to_dnnrc_dataset dv)
      | Dv_javascript dv -> Dv_nnrc (Dv_nnrc_to_javascript dv)
      | Dv_java dv -> Dv_nnrc (Dv_nnrc_to_java (config.comp_qname, config.comp_java_imports, dv))
      | Dv_camp dv -> Dv_nnrc (Dv_nnrc_to_camp (List.map fst config.comp_vdbindings, dv)) (* XXX to check XXX *)
      | Dv_rule _
      | Dv_oql _
      | Dv_nra _
      | Dv_nraenv _
      | Dv_nnrc _
      | Dv_cldmr _
      | Dv_dnnrc_typed_dataset _
      | Dv_spark _
      | Dv_spark2 _
      | Dv_cloudant _ ->
          raise (CACo_Error ("No compilation path from "^(name_of_language lang)^" to "^(name_of_driver dv)))
      end
  | L_nnrcmr ->
      begin match dv with
      | Dv_spark dv -> Dv_nnrcmr (Dv_nnrcmr_to_spark (config.comp_qname, dv))
      | Dv_nnrc dv -> Dv_nnrcmr (Dv_nnrcmr_to_nnrc dv)
      | Dv_dnnrc_dataset dv -> Dv_nnrcmr (Dv_nnrcmr_to_dnnrc_dataset dv)
      | Dv_cldmr dv -> Dv_nnrcmr (Dv_nnrcmr_to_cldmr (config.comp_brand, dv))
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_nra _
      | Dv_nraenv _
      | Dv_nnrcmr _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark2 _
      | Dv_cloudant _ ->
          raise (CACo_Error ("No compilation path from "^(name_of_language lang)^" to "^(name_of_driver dv)))
      end
  | L_cldmr ->
      begin match dv with
      | Dv_cloudant dv -> Dv_cldmr (Dv_cldmr_to_cloudant (config.comp_qname, config.comp_brand, dv))
      | Dv_rule _
      | Dv_camp _
      | Dv_oql _
      | Dv_nra _
      | Dv_nraenv _
      | Dv_nnrc _
      | Dv_nnrcmr _
      | Dv_cldmr _
      | Dv_dnnrc_dataset _
      | Dv_dnnrc_typed_dataset _
      | Dv_javascript _
      | Dv_java _
      | Dv_spark _
      | Dv_spark2 _ ->
          raise (CACo_Error ("No compilation path from "^(name_of_language lang)^" to "^(name_of_driver dv)))
      end
  (* | L_dnnrc_dataset -> *)
  (*     begin match dv with *)
  (*     | Dv_rule dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_camp dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_oql dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_nra dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_nraenv dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_nnrc dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_nnrcmr dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_cldmr dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_dnnrc_dataset dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_dnnrc_typed_dataset dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_javascript dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_java dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_spark dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_spark2 dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     | Dv_cloudant dv -> Dv_dnnrc_dataset (Dv_dnnrc_dataset_to_ dv) *)
  (*     end *)
  (* | L_dnnrc_typed_dataset -> *)
  (*     begin match dv with *)
  (*     | Dv_rule dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_camp dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_oql dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_nra dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_nraenv dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_nnrc dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_nnrcmr dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_cldmr dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_dnnrc_dataset dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_dnnrc_typed_dataset dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_javascript dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_java dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_spark dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_spark2 dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     | Dv_cloudant dv -> Dv_dnnrc_typed_dataset (Dv_dnnrc_typed_dataset_to_ dv) *)
  (*     end *)
  | L_javascript
  | L_java
  | L_spark
  | L_spark2
  | L_cloudant
  | L_error ->
      raise (CACo_Error ("No compilation path from "^(name_of_language lang)^" to "^(name_of_driver dv)))
  end

let rec driver_of_language target rev_path =
  begin match target with
  | LoO_optim ->
      begin match rev_path with
      | [] ->
          raise (CACo_Error "The source language must be specified in the path")
      | LoO_optim :: rev_path ->
          driver_of_language target rev_path
      | LoO_language lang :: _ ->
          push_optim (driver_of_language (LoO_language lang) [])
      end
  | LoO_language L_rule -> Dv_rule Dv_rule_stop
  | LoO_language L_camp -> Dv_camp Dv_camp_stop
  | LoO_language L_oql -> Dv_oql Dv_oql_stop
  | LoO_language L_nra -> Dv_nra Dv_nra_stop
  | LoO_language L_nraenv -> Dv_nraenv Dv_nraenv_stop
  | LoO_language L_nnrc -> Dv_nnrc Dv_nnrc_stop
  | LoO_language L_nnrcmr -> Dv_nnrcmr Dv_nnrcmr_stop
  | LoO_language L_cldmr -> Dv_cldmr Dv_cldmr_stop
  | LoO_language L_dnnrc_dataset -> Dv_dnnrc_dataset Dv_dnnrc_dataset_stop
  | LoO_language L_dnnrc_typed_dataset -> Dv_dnnrc_typed_dataset Dv_dnnrc_typed_dataset_stop
  | LoO_language L_javascript -> Dv_javascript Dv_javascript_stop
  | LoO_language L_java -> Dv_java Dv_java_stop
  | LoO_language L_spark -> Dv_spark Dv_spark_stop
  | LoO_language L_spark2 -> Dv_spark2 Dv_spark2_stop
  | LoO_language L_cloudant -> Dv_cloudant Dv_cloudant_stop
  | LoO_language L_error -> raise (CACo_Error "Cannot optimize an error")
  end

let driver_of_conf : driver_config -> driver =
  let rec build config dv p =
    begin match p with
    | [] -> dv
    | lang :: p ->
        begin match lang with
        | LoO_optim -> build config (push_optim dv) p
        | LoO_language lang -> build config (push_translation config lang dv) p
        end
    end
  in
  fun config ->
    begin match List.rev config.comp_path with
    | [] -> raise (CACo_Error "Empty compilation path")
    | target :: rev_path ->
        build config (driver_of_language target rev_path) rev_path
    end


(* let add_path conf s = conf.path <- conf.path @ [s] *)
(* let get_path conf = conf.path *)

(* let get_brand conf = conf.dv_brand *)

