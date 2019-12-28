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

open Pretty_query

(** Output languages *)

let output_query pconf q =
  begin match q with
  | Compiler.Q_camp_rule q -> pretty_query pconf pretty_camp_rule q
  | Compiler.Q_tech_rule q -> pretty_query pconf pretty_tech_rule q
  | Compiler.Q_designer_rule q -> pretty_query pconf pretty_designer_rule q
  | Compiler.Q_camp q -> pretty_query pconf pretty_camp q
  | Compiler.Q_oql q -> pretty_query pconf pretty_oql q
  | Compiler.Q_sql q -> pretty_query pconf pretty_sql q
  | Compiler.Q_sqlpp q -> pretty_query pconf pretty_sqlpp q
  | Compiler.Q_lambda_nra q -> pretty_query pconf pretty_lambda_nra q
  | Compiler.Q_nra q -> pretty_query pconf pretty_nra q
  | Compiler.Q_nraenv_core q -> pretty_query pconf pretty_nraenv_core q
  | Compiler.Q_nraenv q -> pretty_query pconf pretty_nraenv q
  | Compiler.Q_nnrc_core q -> pretty_query pconf pretty_nnrc q
  | Compiler.Q_nnrc q -> pretty_query pconf pretty_nnrc q
  | Compiler.Q_nnrs q -> pretty_query pconf pretty_nnrs q
  | Compiler.Q_nnrs_core q -> pretty_query pconf pretty_nnrs_core q
  | Compiler.Q_nnrs_imp q -> pretty_query pconf pretty_nnrs_imp q
  | Compiler.Q_imp_qcert q -> pretty_query pconf pretty_imp_qcert q
  | Compiler.Q_imp_ejson q -> pretty_query pconf pretty_imp_ejson q
  | Compiler.Q_nnrcmr q -> pretty_query pconf pretty_nnrcmr q
  | Compiler.Q_dnnrc q -> pretty_query pconf pretty_dnnrc q
  | Compiler.Q_dnnrc_typed q -> pretty_query pconf pretty_dnnrc_typed q
  | Compiler.Q_js_ast q -> pretty_query pconf pretty_js_ast q
  | Compiler.Q_javascript q -> pretty_query pconf pretty_javascript q
  | Compiler.Q_java q -> pretty_query pconf pretty_java q
  | Compiler.Q_spark_df q -> pretty_query pconf pretty_spark_df q
  | Compiler.Q_error q -> pretty_query pconf pretty_error q
  end

