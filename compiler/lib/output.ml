(*
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

(** This module contains compiler output code *)

open CompLang
open Pretty_query

(** Output languages *)

let output_query pconf q =
  begin match q with
  | Q_camp_rule q -> pretty_query pconf pretty_camp_rule q
  | Q_tech_rule q -> pretty_query pconf pretty_tech_rule q
  | Q_designer_rule q -> pretty_query pconf pretty_designer_rule q
  | Q_camp q -> pretty_query pconf pretty_camp q
  | Q_oql q -> pretty_query pconf pretty_oql q
  | Q_sql q -> pretty_query pconf pretty_sql q
  | Q_sqlpp q -> pretty_query pconf pretty_sqlpp q
  | Q_lambda_nra q -> pretty_query pconf pretty_lambda_nra q
  | Q_nra q -> pretty_query pconf pretty_nra q
  | Q_nraenv_core q -> pretty_query pconf pretty_nraenv_core q
  | Q_nraenv q -> pretty_query pconf pretty_nraenv q
  | Q_nnrc_core q -> pretty_query pconf pretty_nnrc q
  | Q_nnrc q -> pretty_query pconf pretty_nnrc q
  | Q_nnrs q -> pretty_query pconf pretty_nnrs q
  | Q_nnrs_core q -> pretty_query pconf pretty_nnrs_core q
  | Q_nnrs_imp q -> pretty_query pconf pretty_nnrs_imp q
  | Q_imp_data q -> pretty_query pconf pretty_imp_data q
  | Q_imp_ejson q -> pretty_query pconf pretty_imp_ejson q
  | Q_nnrcmr q -> pretty_query pconf pretty_nnrcmr q
  | Q_dnnrc q -> pretty_query pconf pretty_dnnrc q
  | Q_dnnrc_typed q -> pretty_query pconf pretty_dnnrc_typed q
  | Q_js_ast q -> pretty_query pconf pretty_js_ast q
  | Q_javascript q -> pretty_query pconf pretty_javascript q
  | Q_java q -> pretty_query pconf pretty_java q
  | Q_spark_df q -> pretty_query pconf pretty_spark_df q
  | Q_wasm_ast q -> pretty_query pconf pretty_wasm_ast q
  | Q_error q -> pretty_query pconf pretty_error q
  end

