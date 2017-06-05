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

Section SQLPPSize.

  Require Import String.
  Require Import ZArith.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.

  Require Import Utils BasicSystem.

  Require Import SQLPP.
  
  Context {fruntime:foreign_runtime}.

  Section size.
    Fixpoint sqlpp_query_size (q:sqlpp_query) := (* XXX To check XXX *)
      match q with
      | SPUnion _ q1 q2 =>
        (sqlpp_query_size q1) + (sqlpp_query_size q2) + 1 (* XXX to check XXX *)
      | SPIntersect _ q1 q2 =>
        (sqlpp_query_size q1) + (sqlpp_query_size q2) + 1 (* XXX to check XXX *)
      | SPExcept _ q1 q2 =>
        (sqlpp_query_size q1) + (sqlpp_query_size q2) + 1 (* XXX to check XXX *)
      | SPQuery selects froms opt_where opt_group opt_order =>
        List.fold_left (fun acc select => acc + sqlpp_select_size select) selects 0
        + List.fold_left (fun acc from => acc + sqlpp_from_size from) froms 0
        + match opt_where with
          | None => 0
          | Some cond => sqlpp_condition_size cond
          end
        + match opt_group with
          | None => 0
          | Some (_, Some cond) => sqlpp_condition_size cond
          | Some (_, _) => 1
          end
        + match opt_order with
          | None => 0
          | Some cond => 1
          end
      end
        
    with sqlpp_select_size (select: sqlpp_select) :=
      match select with
      | SPSelectColumn _ => 1
      | SPSelectColumnDeref _ _ => 1
      | SPSelectStar => 1
      | SPSelectExpr _ e => sqlpp_expr_size e
      end

    with sqlpp_from_size (from: sqlpp_from) :=
      match from with
      | SPFromTable _ => 1
      | SPFromTableAlias _ _ => 1
      | SPFromQuery _ q => sqlpp_query_size q
      end

    with sqlpp_condition_size (cond: sqlpp_condition) :=
      match cond with
      | SPCondAnd c1 c2
      | SPCondOr c1 c2 =>
        1 + sqlpp_condition_size c1 + sqlpp_condition_size c2
      | SPCondNot c =>
        1 + sqlpp_condition_size c
      | SPCondBinary _ e1 e2 =>
        1 + sqlpp_expr_size e1 + sqlpp_expr_size e2
      | SPCondExists q =>
        1 + sqlpp_query_size q
      | SPCondIn e1 e2 =>
        1 + sqlpp_expr_size e1 + sqlpp_expr_size e2
      | SPCondLike e _ =>
        1 + sqlpp_expr_size e
      | SPCondBetween e1 e2 e3 =>
        1 + sqlpp_expr_size e1 + sqlpp_expr_size e2 + sqlpp_expr_size e3
      end

    with sqlpp_expr_size (expr: sqlpp_expr) :=
      match expr with
      | SPExprConst _ => 1
      | SPExprColumn _ => 1
      | SPExprColumnDeref _ _ => 1
      | SPExprStar => 1
      | SPExprUnary _ e => 1 + sqlpp_expr_size e
      | SPExprBinary _ e1 e2 => 1 + sqlpp_expr_size e1 + sqlpp_expr_size e2
      | SPExprCase c e1 e2 =>
        1 + sqlpp_condition_size c + sqlpp_expr_size e1 + sqlpp_expr_size e2
      | SPExprAggExpr _ e => 1 + sqlpp_expr_size e
      | SPExprQuery q => 1 + sqlpp_query_size q
      end.

    Definition sqlpp_statement_size (st:sqlpp_statement) :=
      match st with
      | SPRunQuery q => sqlpp_query_size q
      | SPCreateView _ q => sqlpp_query_size q
      | SPDropView _ => 1
      end.

    Definition sqlpp_size (q:sqlpp) :=
      List.fold_left (fun acc st => acc + sqlpp_statement_size st) q 0.

  End size.

  Section depth.

    Fixpoint sqlpp_query_depth (q:sqlpp_query) := (* XXX To check XXX *)
      match q with
      | SPUnion _ q1 q2 =>
        1 + (max (sqlpp_query_depth q1) (sqlpp_query_depth q2)) (* XXX To check with Louis XXX *)
      | SPIntersect _ q1 q2 =>
        1 + (max (sqlpp_query_depth q1) (sqlpp_query_depth q2)) (* XXX To check with Louis XXX *)
      | SPExcept _ q1 q2 =>
        1 + (max (sqlpp_query_depth q1) (sqlpp_query_depth q2)) (* XXX To check with Louis XXX *)
      | SPQuery selects froms opt_where opt_group opt_order =>
        max (List.fold_left (fun acc select => max acc (sqlpp_select_depth select)) selects 0)
            (max (List.fold_left (fun acc from => max acc (sqlpp_from_depth from)) froms 0)
                 (max (match opt_where with
                       | None => 0
                       | Some cond => sqlpp_condition_depth cond
                       end)
                      (max (match opt_group with
                            | None => 0
                            | Some (_, Some cond) => sqlpp_condition_depth cond
                            | Some (_, _) => 1
                            end)
                           (match opt_order with
                            | None => 0
                            | Some cond => 1
                            end))))
      end

    with sqlpp_select_depth (select: sqlpp_select) :=
      match select with
      | SPSelectColumn _ => 0
      | SPSelectColumnDeref _ _ => 0
      | SPSelectStar => 0
      | SPSelectExpr _ e => sqlpp_expr_depth e
      end

    with sqlpp_from_depth (from: sqlpp_from) :=
      match from with
      | SPFromTable _ => 0
      | SPFromTableAlias _ _ => 0
      | SPFromQuery _ q => 1 + sqlpp_query_depth q
      end

    with sqlpp_condition_depth (cond: sqlpp_condition) :=
      match cond with
      | SPCondAnd c1 c2
      | SPCondOr c1 c2 =>
        max (sqlpp_condition_depth c1) (sqlpp_condition_depth c2)
      | SPCondNot c =>
        sqlpp_condition_depth c
      | SPCondBinary _ e1 e2 =>
        max (sqlpp_expr_depth e1) (sqlpp_expr_depth e2)
      | SPCondExists q =>
        sqlpp_query_depth q
      | SPCondIn e1 e2 =>
        max (sqlpp_expr_depth e1) (sqlpp_expr_depth e2)
      | SPCondLike e _ =>
        sqlpp_expr_depth e
      | SPCondBetween e1 e2 e3 =>
        max (sqlpp_expr_depth e1) (max (sqlpp_expr_depth e2) (sqlpp_expr_depth e3))
      end

    with sqlpp_expr_depth (expr: sqlpp_expr) :=
      match expr with
      | SPExprConst _ => 0
      | SPExprColumn _ => 0
      | SPExprColumnDeref _ _ => 0
      | SPExprStar => 0
      | SPExprUnary _ e => sqlpp_expr_depth e
      | SPExprBinary _ e1 e2 => max (sqlpp_expr_depth e1) (sqlpp_expr_depth e2)
      | SPExprCase c e1 e2 =>
        max (sqlpp_condition_depth c) (max (sqlpp_expr_depth e1) (sqlpp_expr_depth e2))
      | SPExprAggExpr _ e => sqlpp_expr_depth e
      | SPExprQuery q => sqlpp_query_depth q
      end.

    Definition sqlpp_statement_depth (st:sqlpp_statement) :=
      match st with
      | SPRunQuery q => 1 + sqlpp_query_depth q
      | SPCreateView _ q => sqlpp_query_depth q
      | SPDropView _ => 1
      end.

    Definition sqlpp_depth (q:sqlpp) :=
      List.fold_left (fun acc st => max acc (sqlpp_statement_depth st)) q 0.

  End depth.
  
End SQLPPSize.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
