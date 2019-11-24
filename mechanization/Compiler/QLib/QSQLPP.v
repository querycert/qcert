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
Require Import String.
Require QData.
Require QOperators.
Require SQLPP.

Module QSQLPP(runtime:CompilerRuntime).

  Module QData := QData.QData runtime.
  Module QOps := QOperators.QOperators runtime.

  Definition sqlpp : Set := SQLPP.sqlpp.

  Definition sqlpp_select_statement := SQLPP.sqlpp_select_statement.
  Definition sqlpp_select : Set := SQLPP.sqlpp_select.
  Definition sqlpp_from : Set := SQLPP.sqlpp_from.
  Definition sqlpp_where : Set := SQLPP.sqlpp_where.
  Definition sqlpp_expr : Set := SQLPP.sqlpp_expr.
  Definition sqlpp_select_block : Set := SQLPP.sqlpp_select_block.
  Definition sqlpp_union_element : Set := SQLPP.sqlpp_union_element.
  Definition sqlpp_join_clause : Set := SQLPP.sqlpp_join_clause.
  Definition sqlpp_group_by : Set := SQLPP.sqlpp_group_by.
  Definition sqlpp_order_by : Set := SQLPP.sqlpp_order_by.
  Definition sqlpp_when_then : Set := SQLPP.sqlpp_when_then.
  Definition sqlpp_distinct : Set := SQLPP.sqlpp_distinct.
  Definition sqlpp_project : Set := SQLPP.sqlpp_project.
  Definition sqlpp_join_type : Set := SQLPP.sqlpp_join_type.
  Definition sqlpp_function_name := SQLPP.sqlpp_function_name.
  
  Definition sqlpp_sqlpp_query := SQLPP.SPQuery.
  Definition sqlpp_sqlpp_positive : sqlpp_expr->sqlpp_expr := SQLPP.SPPositive.
  Definition sqlpp_sqlpp_negative : sqlpp_expr->sqlpp_expr := SQLPP.SPNegative.
  Definition sqlpp_sqlpp_exists : sqlpp_expr->sqlpp_expr := SQLPP.SPExists.
  Definition sqlpp_sqlpp_not : sqlpp_expr->sqlpp_expr := SQLPP.SPNot.
  Definition sqlpp_sqlpp_is_null : sqlpp_expr->sqlpp_expr := SQLPP.SPIsNull.
  Definition sqlpp_sqlpp_is_missing : sqlpp_expr->sqlpp_expr := SQLPP.SPIsMissing.
  Definition sqlpp_sqlpp_is_unknown : sqlpp_expr->sqlpp_expr := SQLPP.SPIsUnknown.
  Definition sqlpp_sqlpp_plus : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPPlus.
  Definition sqlpp_sqlpp_minus : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPMinus.
  Definition sqlpp_sqlpp_mult : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPMult.
  Definition sqlpp_sqlpp_div : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPDiv.
  Definition sqlpp_sqlpp_mod : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPMod.
  Definition sqlpp_sqlpp_exp : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPExp.
  Definition sqlpp_sqlpp_concat : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPConcat.
  Definition sqlpp_sqlpp_in : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPIn.
  Definition sqlpp_sqlpp_eq : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPEq.
  Definition sqlpp_sqlpp_fuzzy_eq : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPFuzzyEq.
  Definition sqlpp_sqlpp_neq : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPNeq.
  Definition sqlpp_sqlpp_lt : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPLt.
  Definition sqlpp_sqlpp_gt : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPGt.
  Definition sqlpp_sqlpp_le : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPLe.
  Definition sqlpp_sqlpp_ge : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPGe.
  Definition sqlpp_sqlpp_like : sqlpp_expr->string->sqlpp_expr := SQLPP.SPLike.
  Definition sqlpp_sqlpp_and : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPAnd.
  Definition sqlpp_sqlpp_or : sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPOr.
  Definition sqlpp_sqlpp_between : sqlpp_expr->sqlpp_expr->sqlpp_expr->sqlpp_expr := SQLPP.SPBetween.
  Definition sqlpp_sqlpp_when_then : sqlpp_expr->sqlpp_expr->sqlpp_when_then := SQLPP.SPWhenThen.
  Definition sqlpp_sqlpp_simple_case : sqlpp_expr->list sqlpp_when_then-> option sqlpp_expr->sqlpp_expr := SQLPP.SPSimpleCase.
  Definition sqlpp_sqlpp_searched_case : list sqlpp_when_then->option sqlpp_expr->sqlpp_expr := SQLPP.SPSearchedCase.
  Definition sqlpp_sqlpp_some := SQLPP.SPSome.
  Definition sqlpp_sqlpp_every := SQLPP.SPEvery.
  Definition sqlpp_sqlpp_dot : sqlpp_expr->string->sqlpp_expr := SQLPP.SPDot.
  Definition sqlpp_sqlpp_index := SQLPP.SPIndex.
  Definition sqlpp_sqlpp_index_any := SQLPP.SPIndexAny.
  Definition sqlpp_sqlpp_literal := SQLPP.SPLiteral.
  Definition sqlpp_sqlpp_null := SQLPP.SPNull.
  Definition sqlpp_sqlpp_missing := SQLPP.SPMissing.
  Definition sqlpp_sqlpp_var_ref := SQLPP.SPVarRef.
  Definition sqlpp_sqlpp_function_call := SQLPP.SPFunctionCall.
  Definition sqlpp_sqlpp_array := SQLPP.SPArray.
  Definition sqlpp_sqlpp_bag := SQLPP.SPBag.
  Definition sqlpp_sqlpp_object := SQLPP.SPObject.
  Definition sqlpp_sqlpp_select_stmt := SQLPP.SPSelectStmt.
  Definition sqlpp_sqlpp_select_block := SQLPP.SPSelectBlock.
  Definition sqlpp_sqlpp_block := SQLPP.SPBlock.
  Definition sqlpp_sqlpp_subquery := SQLPP.SPSubquery.
  Definition sqlpp_sqlpp_select_sql := SQLPP.SPSelectSQL.
  Definition sqlpp_sqlpp_select_value := SQLPP.SPSelectValue.
  Definition sqlpp_sqlpp_project := SQLPP.SPProject.
  Definition sqlpp_sqlpp_project_star := SQLPP.SPProjectStar.
  Definition sqlpp_sqlpp_from := SQLPP.SPFrom.
  Definition sqlpp_sqlpp_join := SQLPP.SPJoin.
  Definition sqlpp_sqlpp_unnest := SQLPP.SPUnnest.
  Definition sqlpp_sqlpp_inner := SQLPP.SPInner.
  Definition sqlpp_sqlpp_left_outer := SQLPP.SPLeftOuter.
  Definition sqlpp_sqlpp_where := SQLPP.SPWhere.
  Definition sqlpp_sqlpp_no_where := SQLPP.SPNoWhere.
  Definition sqlpp_sqlpp_group_by := SQLPP.SPGroupBy.
  Definition sqlpp_sqlpp_no_group_by := SQLPP.SPNoGroupBy.
  Definition sqlpp_sqlpp_order_by := SQLPP.SPOrderBy.
  Definition sqlpp_sqlpp_no_order_by := SQLPP.SPNoOrderBy.
  Definition sqlpp_sqlpp_distinct := SQLPP.SPDistinct.
  Definition sqlpp_sqlpp_all := SQLPP.SPAll.

End QSQLPP.

