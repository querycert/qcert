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

Section SQLtoNRAEnv.

  Require Import String.
  Require Import ZArith.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.

  Require Import Utils BasicSystem.

  Context {fruntime:foreign_runtime}.

  Require Import RDataSort. (* For SortCriterias *)
  Require Import SQL.
  Require Import NRAEnvRuntime.

  Definition sql_order_to_nraenv (acc:nraenv) (opt_order:option sql_order_spec) :=
    match opt_order with
    | None => acc
    | Some sql_order_spec =>
      NRAEnvUnop (AOrderBy sql_order_spec) acc
    end.

  Definition column_of_select (select:sql_select) : (option string * string) :=
    match select with
    | SSelectColumn cname => (None,cname)
    | SSelectColumnDeref tname cname => (Some tname,cname)
    | SSelectStar => (None,""%string) (* XXX Ouch ... do we need full inference because of this? XXX *)
    | SSelectExpr cname _ => (None,cname)
    end.
    
  Definition columns_of_selects (selects:list sql_select) : list (option string * string) :=
    map column_of_select selects.
    
  Fixpoint columns_of_query (q:sql_query) : list (option string * string) :=
    match q with
    | SUnion _ q1 q2 =>
      columns_of_query q1 (* XXX WARNING: This should check that q2 has the same columns -- typing would be nice XXX *)
    | SIntersect _ q1 q2 =>
      columns_of_query q1 (* XXX WARNING: This should check that q2 has the same columns -- typing would be nice XXX *)
    | SExcept _ q1 q2 =>
      columns_of_query q1 (* XXX WARNING: This should check that q2 has the same columns -- typing would be nice XXX *)
    | SQuery selects _ _ _ _ =>
      columns_of_selects selects
    end.
  
  Fixpoint create_renaming
           (out_columns:list string)
           (in_columns:list (option string * string)) :=
    match out_columns,in_columns with
    | nil,_ | _,nil =>  (NRAEnvConst (drec nil))
    | out_cname :: out_columns', (None,in_cname) :: in_columns' =>
      NRAEnvBinop AConcat
                  (NRAEnvUnop (ARec out_cname) (NRAEnvUnop (ADot in_cname) NRAEnvID))
                  (create_renaming out_columns' in_columns')
    | out_cname :: out_columns', (Some in_tname,in_cname) :: in_columns' =>
      NRAEnvBinop AConcat
                  (NRAEnvUnop (ARec out_cname) (NRAEnvUnop (ADot in_cname) (NRAEnvUnop (ADot in_tname) NRAEnvID)))
                  (create_renaming out_columns' in_columns')
    end.

  Definition nraenv_if b expr1 expr2
    :=
      NRAEnvApp
        (NRAEnvEither
           (NRAEnvApp expr1 (NRAEnvUnop (ADot "id"%string) NRAEnvID))
           (NRAEnvApp expr2 (NRAEnvUnop (ADot "id"%string) NRAEnvID)))
        (NRAEnvEitherConcat  
           (NRAEnvApp (NRAEnvEither (NRAEnvConst (dleft (drec nil))) (NRAEnvConst (dright (drec nil))))
                      (NRAEnvUnop ASingleton (NRAEnvSelect NRAEnvID (NRAEnvUnop AColl b))))
           ((NRAEnvUnop (ARec "id"%string) NRAEnvID))).

  (*
    Example example_nraenv_if
      := nraenv_if
           (NRAEnvBinop AEq (NRAEnvConst (dnat 3)) (NRAEnvID))
           (NRAEnvBinop (ABArith ArithPlus) (NRAEnvConst (dnat 10)) NRAEnvID)
           (NRAEnvBinop (ABArith ArithPlus) (NRAEnvConst (dnat 20)) NRAEnvID).

    Eval vm_compute in nraenv_eval nil nil example_nraenv_if (drec nil) (dnat 3).
    Eval vm_compute in nraenv_eval nil nil example_nraenv_if (drec nil) (dnat 4).
   *)

  Section queryvar.
    Context (view_list:list string).

    Definition lookup_table (table_name:string) : nraenv
      := if in_dec string_eqdec table_name view_list
         then NRAEnvUnop (ADot table_name) NRAEnvEnv
         else NRAEnvGetConstant table_name.

    Fixpoint sql_query_to_nraenv (create_table:bool) (q:sql_query) {struct q} : nraenv :=
      let q_is_singleton : bool := is_singleton_sql_query q in
      match q with
      | SUnion SAll q1 q2 =>
        NRAEnvBinop AUnion
                    (sql_query_to_nraenv create_table q1)
                    (sql_query_to_nraenv create_table q2)
      | SUnion SDistinct q1 q2 =>
        NRAEnvUnop ADistinct
                   (NRAEnvBinop AUnion
                                (sql_query_to_nraenv create_table q1)
                                (sql_query_to_nraenv create_table q2))
      | SIntersect SAll q1 q2 =>
        NRAEnvBinop AMin (* XXX Bag minimum -- to double check XXX *)
                    (sql_query_to_nraenv create_table q1)
                    (sql_query_to_nraenv create_table q2)
      | SIntersect SDistinct q1 q2 =>
        NRAEnvUnop ADistinct
                   (NRAEnvBinop AMin (* XXX Bag minimum -- to double check XXX *)
                                (sql_query_to_nraenv create_table q1)
                                (sql_query_to_nraenv create_table q2))
      | SExcept SAll q1 q2 =>
        NRAEnvBinop AMinus (* XXX Bag difference -- to double check XXX *)
                    (sql_query_to_nraenv create_table q1)
                    (sql_query_to_nraenv create_table q2)
      | SExcept SDistinct q1 q2 =>
        NRAEnvUnop ADistinct
                   (NRAEnvBinop AMinus (* XXX Bag minimum -- to double check XXX *)
                                (sql_query_to_nraenv create_table q1)
                                (sql_query_to_nraenv create_table q2))
      | SQuery selects froms opt_where opt_group opt_order =>
        let nraenv_from_clause :=
            fold_left sql_from_to_nraenv froms (NRAEnvUnop AColl NRAEnvID)
        in
        let nraenv_where_clause :=
            match opt_where with
            | None => nraenv_from_clause
            | Some cond => NRAEnvSelect (sql_condition_to_nraenv NRAEnvID cond) nraenv_from_clause
            end
        in
        let nraenv_group_by_clause :=
            match opt_group with
            | None => nraenv_where_clause
            | Some (sl,None) => NRAEnvGroupBy "partition" sl nraenv_where_clause
            | Some (sl,Some cond) =>
              NRAEnvSelect (sql_condition_to_nraenv (NRAEnvUnop (ADot "partition") NRAEnvID) cond)
                           (NRAEnvGroupBy "partition" sl nraenv_where_clause)
            end
        in
        let nraenv_select_clause :=
            if q_is_singleton (* XXX Two different translations here! XXX *)
            then
              match selects with
              | SSelectExpr _ expr :: nil =>
                sql_expr_to_nraenv true nraenv_group_by_clause expr
              | _ => NRAEnvConst dunit (* XXX This should be really a compilation error XXX *)
              end
            else
              if create_table
              then
                NRAEnvMap (fold_left sql_select_to_nraenv selects (NRAEnvConst (drec nil)))
                          nraenv_group_by_clause
              else
                if (is_value_sequence_sql_query q)
                then
                  match selects with
                  | SSelectExpr _ expr :: nil =>
                    NRAEnvMap (sql_expr_to_nraenv false NRAEnvID expr) nraenv_group_by_clause
                  | SSelectColumn cname :: nil =>
                    NRAEnvMap (NRAEnvUnop (ADot cname) NRAEnvID) nraenv_group_by_clause
                  | SSelectColumnDeref tname cname :: nil =>
                    NRAEnvMap (NRAEnvUnop (ADot cname) (NRAEnvUnop (ADot tname) NRAEnvID)) nraenv_group_by_clause
                  | _ => NRAEnvConst dunit (* XXX This should be really a compilation error XXX *)
                  end
                else
                  NRAEnvConst dunit (* XXX This should be really a compilation error XXX *)
        in
        let nraenv_order_by_clause := sql_order_to_nraenv nraenv_select_clause opt_order in
        nraenv_order_by_clause
      end
    with sql_from_to_nraenv (acc:nraenv) (from:sql_from) {struct from} :=
           match from with
           | (SFromTable tname) => NRAEnvProduct (lookup_table tname) acc
           | (SFromTableAlias new_name tname) =>
             NRAEnvProduct (NRAEnvMap (NRAEnvUnop (ARec new_name) NRAEnvID) (lookup_table tname)) acc
           | SFromQuery tspec q =>
             let (tname,opt_columns) := tspec in
             match opt_columns with
             | Some out_columns =>
               let in_columns := columns_of_query q in
               NRAEnvMap (create_renaming out_columns in_columns)
                         (sql_query_to_nraenv true q)
             | None => sql_query_to_nraenv true q
             end
           end
    with sql_select_to_nraenv (acc:nraenv) (select:sql_select) {struct select} :=
           match select with
           | SSelectColumn cname =>
             NRAEnvBinop AConcat
                         (NRAEnvUnop (ARec cname) (NRAEnvUnop (ADot cname) NRAEnvID))
                         acc
           | SSelectColumnDeref tname cname =>
             NRAEnvBinop AConcat
                         (NRAEnvUnop (ARec cname) (NRAEnvUnop (ADot cname) (NRAEnvUnop (ADot tname) NRAEnvID)))
                         acc
           | SSelectStar =>
             NRAEnvBinop AConcat NRAEnvID acc
           | SSelectExpr cname expr =>
             NRAEnvBinop AConcat
                         (NRAEnvUnop (ARec cname) (sql_expr_to_nraenv false (NRAEnvUnop (ADot "partition") NRAEnvID) expr))
                         acc
           end
    with sql_expr_to_nraenv (create_table:bool) (acc:nraenv) (expr:sql_expr) {struct expr} :=
           match expr with
           | SExprConst d => NRAEnvConst d
           | SExprColumn cname => NRAEnvUnop (ADot cname) NRAEnvID
           | SExprColumnDeref tname cname => NRAEnvUnop (ADot cname) (NRAEnvUnop (ADot tname) NRAEnvID)
           | SExprStar => NRAEnvID
           | SExprUnary (SSubstring n1 on2) expr1 =>
             NRAEnvUnop (ASubstring n1 on2)
                        (sql_expr_to_nraenv create_table acc expr1)
           | SExprUnary (SUnaryForeignExpr fu) expr1 =>
             NRAEnvUnop (AForeignUnaryOp fu)
                        (sql_expr_to_nraenv create_table acc expr1)
           | SExprBinary (SBinaryForeignExpr fb) expr1 expr2 =>
             NRAEnvBinop (AForeignBinaryOp fb)
                         (sql_expr_to_nraenv create_table acc expr1)
                         (sql_expr_to_nraenv create_table acc expr2)
           | SExprBinary SPlus expr1 expr2 =>
             NRAEnvBinop (ABArith ArithPlus)
                         (sql_expr_to_nraenv create_table acc expr1)
                         (sql_expr_to_nraenv create_table acc expr2)
           | SExprBinary SSubtract expr1 expr2 =>
             NRAEnvBinop (ABArith ArithMinus)
                         (sql_expr_to_nraenv create_table acc expr1)
                         (sql_expr_to_nraenv create_table acc expr2)
           | SExprUnary SMinus expr1 =>
             NRAEnvBinop (ABArith ArithMinus)
                         (NRAEnvConst (dnat 0))
                         (sql_expr_to_nraenv create_table acc expr1)
           | SExprBinary SMult expr1 expr2 =>
             NRAEnvBinop (ABArith ArithMult)
                         (sql_expr_to_nraenv create_table acc expr1)
                         (sql_expr_to_nraenv create_table acc expr2)
           | SExprBinary SDivide expr1 expr2 =>
             NRAEnvBinop (ABArith ArithDivide)
                         (sql_expr_to_nraenv create_table acc expr1)
                         (sql_expr_to_nraenv create_table acc expr2)
           | SExprBinary SConcat expr1 expr2 =>
             NRAEnvBinop ASConcat
                         (sql_expr_to_nraenv create_table acc expr1)
                         (sql_expr_to_nraenv create_table acc expr2)
           | SExprCase cond expr1 expr2 =>
             nraenv_if
               (sql_condition_to_nraenv acc cond)
               (sql_expr_to_nraenv create_table acc expr1)
               (sql_expr_to_nraenv create_table acc expr2)
           | SExprAggExpr SSum expr1 =>
             NRAEnvUnop ASum (NRAEnvMap (sql_expr_to_nraenv create_table NRAEnvID expr1) acc)
           | SExprAggExpr SAvg expr1 =>
             NRAEnvUnop AArithMean (NRAEnvMap (sql_expr_to_nraenv create_table NRAEnvID expr1) acc)
           | SExprAggExpr SCount expr1 =>
             NRAEnvUnop ACount (NRAEnvMap (sql_expr_to_nraenv create_table NRAEnvID expr1) acc)
           | SExprAggExpr SMin expr1 =>
             NRAEnvUnop ANumMin (NRAEnvMap (sql_expr_to_nraenv create_table NRAEnvID expr1) acc)
           | SExprAggExpr SMax expr1 =>
             NRAEnvUnop ANumMax (NRAEnvMap (sql_expr_to_nraenv create_table NRAEnvID expr1) acc)
           | SExprQuery q =>
             if create_table
             then sql_query_to_nraenv true q
             else sql_query_to_nraenv false q
           end
    with sql_condition_to_nraenv (acc:nraenv) (cond:sql_condition) {struct cond} :=
           match cond with
           | SCondAnd cond1 cond2 =>
             NRAEnvBinop AAnd
                         (sql_condition_to_nraenv acc cond1)
                         (sql_condition_to_nraenv acc cond2)
           | SCondOr cond1 cond2 =>
             NRAEnvBinop AOr
                         (sql_condition_to_nraenv acc cond1)
                         (sql_condition_to_nraenv acc cond2)
           | SCondNot cond1 =>
             NRAEnvUnop ANeg
                        (sql_condition_to_nraenv acc cond1)
           | SCondBinary SEq expr1 expr2 =>
             NRAEnvBinop AEq
                         (sql_expr_to_nraenv true acc expr1)
                         (sql_expr_to_nraenv true acc expr2)
           | SCondBinary SLe expr1 expr2 =>
             NRAEnvBinop ALe
                         (sql_expr_to_nraenv true acc expr1)
                         (sql_expr_to_nraenv true acc expr2)
           | SCondBinary SLt expr1 expr2 =>
             NRAEnvBinop ALt
                         (sql_expr_to_nraenv true acc expr1)
                         (sql_expr_to_nraenv true acc expr2)
           | SCondBinary SGe expr1 expr2 =>
             NRAEnvUnop ANeg (NRAEnvBinop ALt
                                          (sql_expr_to_nraenv true acc expr1)
                                          (sql_expr_to_nraenv true acc expr2))
           | SCondBinary SGt expr1 expr2 =>
             NRAEnvUnop ANeg (NRAEnvBinop ALe
                                          (sql_expr_to_nraenv true acc expr1)
                                          (sql_expr_to_nraenv true acc expr2))
           | SCondBinary SDiff expr1 expr2 =>
             NRAEnvUnop ANeg (NRAEnvBinop AEq
                                          (sql_expr_to_nraenv true acc expr1)
                                          (sql_expr_to_nraenv true acc expr2))
           | SCondBinary (SBinaryForeignCond fb) expr1 expr2 =>
             NRAEnvBinop (AForeignBinaryOp fb)
                         (sql_expr_to_nraenv true acc expr1)
                         (sql_expr_to_nraenv true acc expr2)
           | SCondExists q =>
             NRAEnvUnop ANeg (NRAEnvBinop ALe
                                          (NRAEnvUnop ACount (sql_query_to_nraenv true q))
                                          (NRAEnvConst (dnat 0)))
           | SCondIn expr1 expr2 =>
             NRAEnvBinop AContains
                         (sql_expr_to_nraenv true acc expr1)
                         (sql_expr_to_nraenv false acc expr2)
           | SCondLike expr1 slike =>
             NRAEnvUnop (ALike slike None) (sql_expr_to_nraenv true acc expr1)
           | SCondBetween expr1 expr2 expr3 =>
             NRAEnvBinop AAnd
                         (NRAEnvBinop ALe
                                      (sql_expr_to_nraenv true acc expr2)
                                      (sql_expr_to_nraenv true acc expr1))
                         (NRAEnvBinop ALe
                                      (sql_expr_to_nraenv true acc expr1)
                                      (sql_expr_to_nraenv true acc expr3))
           end.

    Definition sql_query_to_nraenv_top (q:sql_query) : nraenv :=
      NRAEnvApp (sql_query_to_nraenv true q) (NRAEnvConst (drec nil)). (* XXX Always initialize ID to an empty record XXX *)

    End queryvar.

    (* we currently keep only the value of the last select statement *)
  (* the input environment is assumed to be a record with fields "view_list" *)
  Fixpoint sql_statements_to_nraenv
           (view_list:list string) (q:sql) : nraenv
    := match q with
       | nil => NRAEnvID
       | (SRunQuery q)::rest =>
         NRAEnvApp
           (sql_statements_to_nraenv view_list rest)
           (sql_query_to_nraenv_top view_list q)
       | (SCreateView s q)::rest =>
         NRAEnvAppEnv 
           (sql_statements_to_nraenv (s::view_list) rest)
           (NRAEnvBinop AConcat
                        NRAEnvEnv
                        (NRAEnvUnop (ARec s)
                                    (sql_query_to_nraenv_top view_list q)))
       | (SDropView s)::rest =>
         NRAEnvAppEnv
           (sql_statements_to_nraenv (remove_all s view_list) rest)
           (NRAEnvUnop (ARecRemove s) NRAEnvEnv)
       end.

  (* If there is no select statement, we default to dunit *)
  Definition sql_to_nraenv_top (q:sql) : nraenv
    :=
      NRAEnvAppEnv
        (NRAEnvApp (sql_statements_to_nraenv nil q) (NRAEnvConst dunit))
        (NRAEnvConst (drec nil)).

End SQLtoNRAEnv.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
