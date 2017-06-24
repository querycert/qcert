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

  Definition sqlpp_statement := SQLPP.sqlpp_select_statement.
  Definition sqlpp_query : Set := sqlpp_statement.
  Definition sqlpp_select : Set := SQLPP.sqlpp_select.
  Definition sqlpp_from : Set := SQLPP.sqlpp_from.
  Definition sqlpp_where : Set := SQLPP.sqlpp_where.
  Definition sqlpp_expr : Set := SQLPP.sqlpp_expr.
  Definition sqlpp_select_block : Set := SQLPP.sqlpp_select_block.
  Definition sqlpp_union_element : Set := SQLPP.sqlpp_union_element.
  Definition sqlpp_join_clause : Set := SQLPP.sqlpp_join_clause.
  Definition sqlpp_group_by : Set := SQLPP.sqlpp_group_by.
  Definition sqlpp_order_by : Set := SQLPP.sqlpp_order_by.

  Definition sqlpp_sqlpp_query := SQLPP.SPQuery.
  Definition sqlpp_sqlpp_positive := SQLPP.SPPositive.
  Definition sqlpp_sqlpp_negative := SQLPP.SPNegative.
  Definition sqlpp_sqlpp_exists := SQLPP.SPExists.
  Definition sqlpp_sqlpp_not := SQLPP.SPNot.
  Definition sqlpp_sqlpp_is_null := SQLPP.SPIsNull.
  Definition sqlpp_sqlpp_is_missing := SQLPP.SPIsMissing.
  Definition sqlpp_sqlpp_is_unknown := SQLPP.SPIsUnknown.
  Definition sqlpp_sqlpp_plus := SQLPP.SPPlus.
  Definition sqlpp_sqlpp_minus := SQLPP.SPMinus.
  Definition sqlpp_sqlpp_mult := SQLPP.SPMult.
  Definition sqlpp_sqlpp_div := SQLPP.SPDiv.
  Definition sqlpp_sqlpp_mod := SQLPP.SPMod.
  Definition sqlpp_sqlpp_exp := SQLPP.SPExp.
  Definition sqlpp_sqlpp_concat := SQLPP.SPConcat.
  Definition sqlpp_sqlpp_in := SQLPP.SPIn.
  Definition sqlpp_sqlpp_eq := SQLPP.SPEq.
  Definition sqlpp_sqlpp_neq := SQLPP.SPNeq.
  Definition sqlpp_sqlpp_lt := SQLPP.SPLt.
  Definition sqlpp_sqlpp_gt := SQLPP.SPGt.
  Definition sqlpp_sqlpp_le := SQLPP.SPLe.
  Definition sqlpp_sqlpp_ge := SQLPP.SPGe.
  Definition sqlpp_sqlpp_like := SQLPP.SPLike.
  Definition sqlpp_sqlpp_and := SQLPP.SPAnd.
  Definition sqlpp_sqlpp_or := SQLPP.SPOr.
  Definition sqlpp_sqlpp_between := SQLPP.SPBetween.
  Definition sqlpp_sqlpp_case := SQLPP.SPCase.
  Definition sqlpp_sqlpp_some := SQLPP.SPSome.
  Definition sqlpp_sqlpp_every := SQLPP.SPEvery.
  Definition sqlpp_sqlpp_dot := SQLPP.SPDot.
  Definition sqlpp_sqlpp_index := SQLPP.SPIndex.
  Definition sqlpp_sqlpp_literal := SQLPP.SPLiteral.
  Definition sqlpp_sqlpp_null := SQLPP.SPNull.
  Definition sqlpp_sqlpp_var_ref := SQLPP.SPVarRef.
  Definition sqlpp_sqlpp_function_call := SQLPP.SPFunctionCall.
  Definition sqlpp_sqlpp_array := SQLPP.SPArray.
  Definition sqlpp_sqlpp_bag := SQLPP.SPBag.
  Definition sqlpp_sqlpp_object := SQLPP.SPObject.

End QSQLPP.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
