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

(** This module contains compiler output code *)

open PrettyQuery

(** Output languages *)

let output_query pconf q =
  begin match q with
  | QcertCompiler.Q_camp_rule q -> pretty_query pconf pretty_camp_rule q
  | QcertCompiler.Q_tech_rule q -> pretty_query pconf pretty_tech_rule q
  | QcertCompiler.Q_designer_rule q -> pretty_query pconf pretty_designer_rule q
  | QcertCompiler.Q_camp q -> pretty_query pconf pretty_camp q
  | QcertCompiler.Q_oql q -> pretty_query pconf pretty_oql q
  | QcertCompiler.Q_sql q -> pretty_query pconf pretty_sql q
  | QcertCompiler.Q_sqlpp q -> pretty_query pconf pretty_sqlpp q
  | QcertCompiler.Q_lambda_nra q -> pretty_query pconf pretty_lambda_nra q
  | QcertCompiler.Q_nra q -> pretty_query pconf pretty_nra q
  | QcertCompiler.Q_nraenv_core q -> pretty_query pconf pretty_nraenv_core q
  | QcertCompiler.Q_nraenv q -> pretty_query pconf pretty_nraenv q
  | QcertCompiler.Q_nnrc_core q -> pretty_query pconf pretty_nnrc q
  | QcertCompiler.Q_nnrc q -> pretty_query pconf pretty_nnrc q
  | QcertCompiler.Q_nnrs q -> pretty_query pconf pretty_nnrs q
  | QcertCompiler.Q_nnrs_core q -> pretty_query pconf pretty_nnrs_core q
  | QcertCompiler.Q_nnrs_imp q -> pretty_query pconf pretty_nnrs_imp q
  | QcertCompiler.Q_imp_qcert q -> pretty_query pconf pretty_imp_qcert q
  | QcertCompiler.Q_imp_json q -> pretty_query pconf pretty_imp_json q
  | QcertCompiler.Q_nnrcmr q -> pretty_query pconf pretty_nnrcmr q
  | QcertCompiler.Q_dnnrc q -> pretty_query pconf pretty_dnnrc q
  | QcertCompiler.Q_dnnrc_typed q -> pretty_query pconf pretty_dnnrc_typed q
  | QcertCompiler.Q_js_ast q -> pretty_query pconf pretty_js_ast q
  | QcertCompiler.Q_javascript q -> pretty_query pconf pretty_javascript q
  | QcertCompiler.Q_java q -> pretty_query pconf pretty_java q
  | QcertCompiler.Q_spark_rdd q -> pretty_query pconf pretty_spark_rdd q
  | QcertCompiler.Q_spark_df q -> pretty_query pconf pretty_spark_df q
  | QcertCompiler.Q_error q -> pretty_query pconf pretty_error q
  end

