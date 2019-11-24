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

Require Import CompilerRuntime.
Require String.
Require QData QOperators.
Require SQL.

Module QSQL(runtime:CompilerRuntime).

  Module QData := QData.QData runtime.
  Module QOps := QOperators.QOperators runtime.

  Definition sql : Set := SQL.sql.
  Definition t : Set := sql.
  Definition column : Set := String.string.
  Definition table : Set := String.string.

  Definition sql_table_spec : Set := SQL.sql_table_spec.
  Definition sql_bin_cond : Set := SQL.sql_bin_cond.
  Definition sql_un_expr : Set := SQL.sql_un_expr.
  Definition sql_bin_expr : Set := SQL.sql_bin_expr.
  Definition sql_agg : Set := SQL.sql_agg.

  Definition sql_statement : Set := SQL.sql_statement.
  Definition sql_query : Set := SQL.sql_query.
  Definition sql_select : Set := SQL.sql_select.
  Definition sql_from : Set := SQL.sql_from.
  Definition sql_condition : Set := SQL.sql_condition.
  Definition sql_expr : Set := SQL.sql_expr.

  Definition sql_sql_query := SQL.SQuery.
  Definition sql_sql_union := SQL.SUnion.
  Definition sql_sql_intersect := SQL.SIntersect.
  Definition sql_sql_except := SQL.SExcept.
  Definition sql_select_column : column -> sql_select := SQL.SSelectColumn.
  Definition sql_select_column_deref : table -> column -> sql_select := SQL.SSelectColumnDeref.
  Definition sql_select_expr : column -> sql_expr -> sql_select := SQL.SSelectExpr.
  Definition sql_select_star : sql_select := SQL.SSelectStar.

  Definition sql_condition_and : sql_condition -> sql_condition -> sql_condition := SQL.SCondAnd.
  Definition sql_condition_or : sql_condition -> sql_condition -> sql_condition := SQL.SCondOr.
  Definition sql_condition_not : sql_condition -> sql_condition := SQL.SCondNot.

  Definition sql_from_table : table -> sql_from := SQL.SFromTable.
  Definition sql_from_table_alias : table -> table -> sql_from := SQL.SFromTableAlias.
  Definition sql_from_query : sql_table_spec -> sql_query -> sql_from := SQL.SFromQuery.

  Definition sql_cond_and := SQL.SCondAnd.
  Definition sql_cond_or := SQL.SCondOr.
  Definition sql_cond_not := SQL.SCondNot.
  Definition sql_cond_binary := SQL.SCondBinary.
  Definition sql_cond_exists := SQL.SCondExists.
  Definition sql_cond_in := SQL.SCondIn.
  Definition sql_cond_like := SQL.SCondLike.
  Definition sql_cond_between := SQL.SCondBetween.

  Definition sql_expr_const : QData.qdata -> sql_expr := SQL.SExprConst.
  Definition sql_expr_column : String.string -> sql_expr := SQL.SExprColumn.
  Definition sql_expr_column_deref : String.string -> String.string -> sql_expr := SQL.SExprColumnDeref.
  Definition sql_expr_star : sql_expr := SQL.SExprStar.
  Definition sql_expr_unary : sql_un_expr -> sql_expr -> sql_expr := SQL.SExprUnary.
  Definition sql_expr_binary : sql_bin_expr -> sql_expr -> sql_expr -> sql_expr := SQL.SExprBinary.
  Definition sql_expr_case : sql_condition -> sql_expr -> sql_expr -> sql_expr := SQL.SExprCase.
  Definition sql_expr_agg_expr : sql_agg -> sql_expr -> sql_expr := SQL.SExprAggExpr.
  Definition sql_expr_query : sql_query -> sql_expr := SQL.SExprQuery.

  Definition sql_run_query : sql_query -> sql_statement
    := SQL.SRunQuery.
  Definition sql_create_view : String.string -> sql_query -> sql_statement
    := SQL.SCreateView.
  Definition sql_drop_view : String.string -> sql_statement
    := SQL.SDropView.

End QSQL.

