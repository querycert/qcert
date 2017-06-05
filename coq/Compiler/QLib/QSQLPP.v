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

Require Import CompilerRuntime.
Require String.
Require QData QOperators.
Require SQLPP.

Module QSQLPP(runtime:CompilerRuntime).

  Module QData := QData.QData runtime.
  Module QOps := QOperators.QOperators runtime.

  Definition sqlpp : Set := SQLPP.sqlpp.
  Definition t : Set := sqlpp.
  Definition column : Set := String.string.
  Definition table : Set := String.string.

  Definition sqlpp_table_spec : Set := SQLPP.sqlpp_table_spec.
  Definition sqlpp_bin_cond : Set := SQLPP.sqlpp_bin_cond.
  Definition sqlpp_un_expr : Set := SQLPP.sqlpp_un_expr.
  Definition sqlpp_bin_expr : Set := SQLPP.sqlpp_bin_expr.
  Definition sqlpp_agg : Set := SQLPP.sqlpp_agg.

  Definition sqlpp_statement : Set := SQLPP.sqlpp_statement.
  Definition sqlpp_query : Set := SQLPP.sqlpp_query.
  Definition sqlpp_select : Set := SQLPP.sqlpp_select.
  Definition sqlpp_from : Set := SQLPP.sqlpp_from.
  Definition sqlpp_condition : Set := SQLPP.sqlpp_condition.
  Definition sqlpp_expr : Set := SQLPP.sqlpp_expr.

  Definition sqlpp_sqlpp_query := SQLPP.SPQuery.
  Definition sqlpp_sqlpp_union := SQLPP.SPUnion.
  Definition sqlpp_sqlpp_intersect := SQLPP.SPIntersect.
  Definition sqlpp_sqlpp_except := SQLPP.SPExcept.
  Definition sqlpp_select_column : column -> sqlpp_select := SQLPP.SPSelectColumn.
  Definition sqlpp_select_column_deref : table -> column -> sqlpp_select := SQLPP.SPSelectColumnDeref.
  Definition sqlpp_select_expr : column -> sqlpp_expr -> sqlpp_select := SQLPP.SPSelectExpr.
  Definition sqlpp_select_star : sqlpp_select := SQLPP.SPSelectStar.

  Definition sqlpp_condition_and : sqlpp_condition -> sqlpp_condition -> sqlpp_condition := SQLPP.SPCondAnd.
  Definition sqlpp_condition_or : sqlpp_condition -> sqlpp_condition -> sqlpp_condition := SQLPP.SPCondOr.
  Definition sqlpp_condition_not : sqlpp_condition -> sqlpp_condition := SQLPP.SPCondNot.

  Definition sqlpp_from_table : table -> sqlpp_from := SQLPP.SPFromTable.
  Definition sqlpp_from_table_alias : table -> table -> sqlpp_from := SQLPP.SPFromTableAlias.
  Definition sqlpp_from_query : sqlpp_table_spec -> sqlpp_query -> sqlpp_from := SQLPP.SPFromQuery.

  Definition sqlpp_cond_and := SQLPP.SPCondAnd.
  Definition sqlpp_cond_or := SQLPP.SPCondOr.
  Definition sqlpp_cond_not := SQLPP.SPCondNot.
  Definition sqlpp_cond_binary := SQLPP.SPCondBinary.
  Definition sqlpp_cond_exists := SQLPP.SPCondExists.
  Definition sqlpp_cond_in := SQLPP.SPCondIn.
  Definition sqlpp_cond_like := SQLPP.SPCondLike.
  Definition sqlpp_cond_between := SQLPP.SPCondBetween.

  Definition sqlpp_expr_const : QData.data -> sqlpp_expr := SQLPP.SPExprConst.
  Definition sqlpp_expr_column : String.string -> sqlpp_expr := SQLPP.SPExprColumn.
  Definition sqlpp_expr_column_deref : String.string -> String.string -> sqlpp_expr := SQLPP.SPExprColumnDeref.
  Definition sqlpp_expr_star : sqlpp_expr := SQLPP.SPExprStar.
  Definition sqlpp_expr_unary : sqlpp_un_expr -> sqlpp_expr -> sqlpp_expr := SQLPP.SPExprUnary.
  Definition sqlpp_expr_binary : sqlpp_bin_expr -> sqlpp_expr -> sqlpp_expr -> sqlpp_expr := SQLPP.SPExprBinary.
  Definition sqlpp_expr_case : sqlpp_condition -> sqlpp_expr -> sqlpp_expr -> sqlpp_expr := SQLPP.SPExprCase.
  Definition sqlpp_expr_agg_expr : sqlpp_agg -> sqlpp_expr -> sqlpp_expr := SQLPP.SPExprAggExpr.
  Definition sqlpp_expr_query : sqlpp_query -> sqlpp_expr := SQLPP.SPExprQuery.

  Definition sqlpp_run_query : sqlpp_query -> sqlpp_statement
    := SQLPP.SPRunQuery.
  Definition sqlpp_create_view : String.string -> sqlpp_query -> sqlpp_statement
    := SQLPP.SPCreateView.
  Definition sqlpp_drop_view : String.string -> sqlpp_statement
    := SQLPP.SPDropView.

End QSQLPP.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
