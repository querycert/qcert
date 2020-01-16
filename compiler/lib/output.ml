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

open Pretty_query

(** Output languages *)

let output_query pconf q =
  begin match q with
  | Core.Q_camp_rule q -> pretty_query pconf pretty_camp_rule q
  | Core.Q_tech_rule q -> pretty_query pconf pretty_tech_rule q
  | Core.Q_designer_rule q -> pretty_query pconf pretty_designer_rule q
  | Core.Q_camp q -> pretty_query pconf pretty_camp q
  | Core.Q_oql q -> pretty_query pconf pretty_oql q
  | Core.Q_sql q -> pretty_query pconf pretty_sql q
  | Core.Q_sqlpp q -> pretty_query pconf pretty_sqlpp q
  | Core.Q_lambda_nra q -> pretty_query pconf pretty_lambda_nra q
  | Core.Q_nra q -> pretty_query pconf pretty_nra q
  | Core.Q_nraenv_core q -> pretty_query pconf pretty_nraenv_core q
  | Core.Q_nraenv q -> pretty_query pconf pretty_nraenv q
  | Core.Q_nnrc_core q -> pretty_query pconf pretty_nnrc q
  | Core.Q_nnrc q -> pretty_query pconf pretty_nnrc q
  | Core.Q_nnrs q -> pretty_query pconf pretty_nnrs q
  | Core.Q_nnrs_core q -> pretty_query pconf pretty_nnrs_core q
  | Core.Q_nnrs_imp q -> pretty_query pconf pretty_nnrs_imp q
  | Core.Q_imp_data q -> pretty_query pconf pretty_imp_data q
  | Core.Q_imp_ejson q -> pretty_query pconf pretty_imp_ejson q
  | Core.Q_nnrcmr q -> pretty_query pconf pretty_nnrcmr q
  | Core.Q_dnnrc q -> pretty_query pconf pretty_dnnrc q
  | Core.Q_dnnrc_typed q -> pretty_query pconf pretty_dnnrc_typed q
  | Core.Q_js_ast q -> pretty_query pconf pretty_js_ast q
  | Core.Q_javascript q -> pretty_query pconf pretty_javascript q
  | Core.Q_java q -> pretty_query pconf pretty_java q
  | Core.Q_spark_df q -> pretty_query pconf pretty_spark_df q
  | Core.Q_error q -> pretty_query pconf pretty_error q
  end

