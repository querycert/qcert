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

Require Import String.
Require Import ZArith.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Utils.
Require Import CommonSystem.
Require Import SQL.
  
Section SQLSize.
  Context {fruntime:foreign_runtime}.

  Section size.
    Fixpoint sql_query_size (q:sql_query) := (* XXX To check XXX *)
      match q with
      | SUnion _ q1 q2 =>
        (sql_query_size q1) + (sql_query_size q2) + 1 (* XXX to check XXX *)
      | SIntersect _ q1 q2 =>
        (sql_query_size q1) + (sql_query_size q2) + 1 (* XXX to check XXX *)
      | SExcept _ q1 q2 =>
        (sql_query_size q1) + (sql_query_size q2) + 1 (* XXX to check XXX *)
      | SQuery selects froms opt_where opt_group opt_order =>
        List.fold_left (fun acc select => acc + sql_select_size select) selects 0
        + List.fold_left (fun acc from => acc + sql_from_size from) froms 0
        + match opt_where with
          | None => 0
          | Some cond => sql_condition_size cond
          end
        + match opt_group with
          | None => 0
          | Some (_, Some cond) => sql_condition_size cond
          | Some (_, _) => 1
          end
        + match opt_order with
          | None => 0
          | Some cond => 1
          end
      end
        
    with sql_select_size (select: sql_select) :=
      match select with
      | SSelectColumn _ => 1
      | SSelectColumnDeref _ _ => 1
      | SSelectStar => 1
      | SSelectExpr _ e => sql_expr_size e
      end

    with sql_from_size (from: sql_from) :=
      match from with
      | SFromTable _ => 1
      | SFromTableAlias _ _ => 1
      | SFromQuery _ q => sql_query_size q
      end

    with sql_condition_size (cond: sql_condition) :=
      match cond with
      | SCondAnd c1 c2
      | SCondOr c1 c2 =>
        1 + sql_condition_size c1 + sql_condition_size c2
      | SCondNot c =>
        1 + sql_condition_size c
      | SCondBinary _ e1 e2 =>
        1 + sql_expr_size e1 + sql_expr_size e2
      | SCondExists q =>
        1 + sql_query_size q
      | SCondIn e1 e2 =>
        1 + sql_expr_size e1 + sql_expr_size e2
      | SCondLike e _ =>
        1 + sql_expr_size e
      | SCondBetween e1 e2 e3 =>
        1 + sql_expr_size e1 + sql_expr_size e2 + sql_expr_size e3
      end

    with sql_expr_size (expr: sql_expr) :=
      match expr with
      | SExprConst _ => 1
      | SExprColumn _ => 1
      | SExprColumnDeref _ _ => 1
      | SExprStar => 1
      | SExprUnary _ e => 1 + sql_expr_size e
      | SExprBinary _ e1 e2 => 1 + sql_expr_size e1 + sql_expr_size e2
      | SExprCase c e1 e2 =>
        1 + sql_condition_size c + sql_expr_size e1 + sql_expr_size e2
      | SExprAggExpr _ e => 1 + sql_expr_size e
      | SExprQuery q => 1 + sql_query_size q
      end.

    Definition sql_statement_size (st:sql_statement) :=
      match st with
      | SRunQuery q => sql_query_size q
      | SCreateView _ q => sql_query_size q
      | SDropView _ => 1
      end.

    Definition sql_size (q:sql) :=
      List.fold_left (fun acc st => acc + sql_statement_size st) q 0.

  End size.

  Section depth.

    Fixpoint sql_query_depth (q:sql_query) := (* XXX To check XXX *)
      match q with
      | SUnion _ q1 q2 =>
        1 + (max (sql_query_depth q1) (sql_query_depth q2)) (* XXX To check with Louis XXX *)
      | SIntersect _ q1 q2 =>
        1 + (max (sql_query_depth q1) (sql_query_depth q2)) (* XXX To check with Louis XXX *)
      | SExcept _ q1 q2 =>
        1 + (max (sql_query_depth q1) (sql_query_depth q2)) (* XXX To check with Louis XXX *)
      | SQuery selects froms opt_where opt_group opt_order =>
        max (List.fold_left (fun acc select => max acc (sql_select_depth select)) selects 0)
            (max (List.fold_left (fun acc from => max acc (sql_from_depth from)) froms 0)
                 (max (match opt_where with
                       | None => 0
                       | Some cond => sql_condition_depth cond
                       end)
                      (max (match opt_group with
                            | None => 0
                            | Some (_, Some cond) => sql_condition_depth cond
                            | Some (_, _) => 1
                            end)
                           (match opt_order with
                            | None => 0
                            | Some cond => 1
                            end))))
      end

    with sql_select_depth (select: sql_select) :=
      match select with
      | SSelectColumn _ => 0
      | SSelectColumnDeref _ _ => 0
      | SSelectStar => 0
      | SSelectExpr _ e => sql_expr_depth e
      end

    with sql_from_depth (from: sql_from) :=
      match from with
      | SFromTable _ => 0
      | SFromTableAlias _ _ => 0
      | SFromQuery _ q => 1 + sql_query_depth q
      end

    with sql_condition_depth (cond: sql_condition) :=
      match cond with
      | SCondAnd c1 c2
      | SCondOr c1 c2 =>
        max (sql_condition_depth c1) (sql_condition_depth c2)
      | SCondNot c =>
        sql_condition_depth c
      | SCondBinary _ e1 e2 =>
        max (sql_expr_depth e1) (sql_expr_depth e2)
      | SCondExists q =>
        sql_query_depth q
      | SCondIn e1 e2 =>
        max (sql_expr_depth e1) (sql_expr_depth e2)
      | SCondLike e _ =>
        sql_expr_depth e
      | SCondBetween e1 e2 e3 =>
        max (sql_expr_depth e1) (max (sql_expr_depth e2) (sql_expr_depth e3))
      end

    with sql_expr_depth (expr: sql_expr) :=
      match expr with
      | SExprConst _ => 0
      | SExprColumn _ => 0
      | SExprColumnDeref _ _ => 0
      | SExprStar => 0
      | SExprUnary _ e => sql_expr_depth e
      | SExprBinary _ e1 e2 => max (sql_expr_depth e1) (sql_expr_depth e2)
      | SExprCase c e1 e2 =>
        max (sql_condition_depth c) (max (sql_expr_depth e1) (sql_expr_depth e2))
      | SExprAggExpr _ e => sql_expr_depth e
      | SExprQuery q => sql_query_depth q
      end.

    Definition sql_statement_depth (st:sql_statement) :=
      match st with
      | SRunQuery q => 1 + sql_query_depth q
      | SCreateView _ q => sql_query_depth q
      | SDropView _ => 1
      end.

    Definition sql_depth (q:sql) :=
      List.fold_left (fun acc st => max acc (sql_statement_depth st)) q 0.

  End depth.
  
End SQLSize.

