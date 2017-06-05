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

(****************
 * TEMP SQLPP is a renamed clone of SQL plus some additions.  A substantial refactoring 
 * would be required structure it as it ought to be based on the semantics.
 ****************)

Section SQLPP.

  Require Import String.
  Require Import ZArith.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.

  Require Import Utils BasicSystem.

  Context {fruntime:foreign_runtime}.

  Require Import RDataSort. (* For SortCriterias *)

  Unset Elimination Schemes.

  Definition sqlpp_env := list (string * data). (* For eval -- unused now *)

  Definition sqlpp_table_spec : Set := string * (option (list string)).
  Definition sqlpp_order_spec : Set := SortCriterias.
  Inductive sqlpp_bin_cond : Set :=
  | SPEq | SPLe | SPLt | SPGe | SPGt | SPDiff
  | SPBinaryForeignCond (fb : foreign_binary_op_type) : sqlpp_bin_cond.
  Inductive sqlpp_un_expr : Set :=
  | SPMinus : sqlpp_un_expr
  | SPSubstring : Z -> option Z -> sqlpp_un_expr
  | SPUnaryForeignExpr (fu:foreign_unary_op_type) : sqlpp_un_expr.
  Inductive sqlpp_bin_expr : Set :=
  | SPPlus | SPSubtract | SPMult | SPDivide
  | SPConcat
  | SPBinaryForeignExpr (fb : foreign_binary_op_type) : sqlpp_bin_expr.
  Inductive sqlpp_agg : Set := | SPSum | SPAvg | SPCount | SPMin | SPMax.

  Inductive sqlpp_distinct : Set := SPDistinct | SPAll.
  
  Inductive sqlpp_query : Set :=
  | SPQuery :
      list sqlpp_select ->                                 (* Select Clause *)
      list sqlpp_from ->                                   (* From Clause *)
      option sqlpp_condition ->                            (* Where Clause *)
      option ((list string) * (option sqlpp_condition)) -> (* GroupBy Clause *)
      option sqlpp_order_spec -> sqlpp_query                 (* OrderBy Clause *)
  | SPUnion :
      sqlpp_distinct -> sqlpp_query -> sqlpp_query -> sqlpp_query
  | SPIntersect :
      sqlpp_distinct -> sqlpp_query -> sqlpp_query -> sqlpp_query
  | SPExcept :
      sqlpp_distinct -> sqlpp_query -> sqlpp_query -> sqlpp_query
  with sqlpp_select : Set :=
  | SPSelectColumn : string -> sqlpp_select
  | SPSelectColumnDeref : string -> string -> sqlpp_select
  | SPSelectStar : sqlpp_select
  | SPSelectExpr : string -> sqlpp_expr -> sqlpp_select
  with sqlpp_from : Set :=
  | SPFromTable : string -> sqlpp_from
  | SPFromTableAlias : string -> string -> sqlpp_from
  | SPFromQuery : sqlpp_table_spec -> sqlpp_query -> sqlpp_from
  with sqlpp_condition : Set :=
  | SPCondAnd : sqlpp_condition -> sqlpp_condition -> sqlpp_condition
  | SPCondOr : sqlpp_condition -> sqlpp_condition -> sqlpp_condition
  | SPCondNot : sqlpp_condition -> sqlpp_condition
  | SPCondBinary : sqlpp_bin_cond -> sqlpp_expr -> sqlpp_expr -> sqlpp_condition
  | SPCondExists : sqlpp_query -> sqlpp_condition
  | SPCondIn : sqlpp_expr -> sqlpp_expr -> sqlpp_condition
  | SPCondLike : sqlpp_expr -> string -> sqlpp_condition
  | SPCondBetween : sqlpp_expr -> sqlpp_expr -> sqlpp_expr -> sqlpp_condition
  with sqlpp_expr : Set :=
  | SPExprConst : data -> sqlpp_expr
  | SPExprColumn : string -> sqlpp_expr
  | SPExprColumnDeref : string -> string -> sqlpp_expr
  | SPExprStar : sqlpp_expr
  | SPExprUnary : sqlpp_un_expr -> sqlpp_expr -> sqlpp_expr
  | SPExprBinary : sqlpp_bin_expr -> sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPExprCase : sqlpp_condition -> sqlpp_expr -> sqlpp_expr -> sqlpp_expr
  | SPExprAggExpr : sqlpp_agg -> sqlpp_expr -> sqlpp_expr
  | SPExprQuery : sqlpp_query -> sqlpp_expr (* relatively broad allowance for nesting... *)
  .

  Inductive sqlpp_statement : Set :=
  | SPRunQuery : sqlpp_query -> sqlpp_statement
  | SPCreateView : string -> sqlpp_query -> sqlpp_statement
  | SPDropView : string -> sqlpp_statement
  .

  (* Let's finally give our languages a proper name! *)
  Definition sqlpp : Set := list sqlpp_statement.

  (* Note: Has to be reviewed carefully -- The semantics differs
     widely for the 'singleton' vs 'non-singleton' case *)
  Fixpoint is_singleton_sqlpp_query (q:sqlpp_query) : bool :=
    match q with
    | SPUnion _ _ _ => false
    | SPIntersect _ _ _ => false
    | SPExcept _ _ _ => false
    | SPQuery (SPSelectExpr _ expr :: nil) _ _ None None =>
      is_singleton_sqlpp_expr expr
    | SPQuery _ _ _ _ _ => false
    end
  with is_singleton_sqlpp_expr (expr:sqlpp_expr) : bool :=
    match expr with
    | SPExprConst _ => true
    | SPExprColumn _ => false
    | SPExprColumnDeref _ _ => false
    | SPExprStar => false
    | SPExprUnary _ expr1 =>
      is_singleton_sqlpp_expr expr1
    | SPExprBinary _ expr1 expr2 =>
      is_singleton_sqlpp_expr expr1 && is_singleton_sqlpp_expr expr2
    | SPExprCase _ expr1 expr2 =>
      is_singleton_sqlpp_expr expr1 && is_singleton_sqlpp_expr expr2
    | SPExprAggExpr _ _ => true
    | SPExprQuery q => is_singleton_sqlpp_query q
    end.
  
  (* Note: Has to be reviewed carefully -- similar predicate but
     checking that the result is a single column (used in 'in'
     predicate for unboxing) *)
  
  Fixpoint is_value_sequence_sqlpp_query (q:sqlpp_query) : bool :=
    match q with
    | SPUnion _ q1 q2 =>
      if is_value_sequence_sqlpp_query q1
      then is_value_sequence_sqlpp_query q2
      else false
    | SPIntersect _ q1 q2 =>
      if is_value_sequence_sqlpp_query q1
      then is_value_sequence_sqlpp_query q2
      else false
    | SPExcept _ q1 q2 =>
      if is_value_sequence_sqlpp_query q1
      then is_value_sequence_sqlpp_query q2
      else false
    | SPQuery (SPSelectExpr _ expr :: nil) _ _ _ _ =>
      if (is_singleton_sqlpp_expr expr) then false else true
    | SPQuery (SPSelectColumn _ :: nil) _ _ _ _ => true
    | SPQuery (SPSelectColumnDeref _ _ :: nil) _ _ _ _ => true
    | SPQuery _ _ _ _ _ => false
    end.

  Section FreeVars.

    Fixpoint sqlpp_query_free_variables (q:sqlpp_query) : list string :=
      match q with
      | SPQuery q_select_clause q_from_clause (Some q_where_cond) (Some (ls,Some q_groupby_cond)) _ =>
        (concat (map sqlpp_select_free_variables q_select_clause))
          ++ (concat (map sqlpp_from_free_variables q_from_clause))
          ++ (sqlpp_condition_free_variables q_where_cond)
          ++ (sqlpp_condition_free_variables q_groupby_cond)
      | SPQuery q_select_clause q_from_clause None (Some (ls,Some q_groupby_cond)) _ =>
        (concat (map sqlpp_select_free_variables q_select_clause))
          ++ (concat (map sqlpp_from_free_variables q_from_clause))
          ++ (sqlpp_condition_free_variables q_groupby_cond)
      | SPQuery q_select_clause q_from_clause (Some q_where_cond) _ _ =>
        (concat (map sqlpp_select_free_variables q_select_clause))
          ++ (concat (map sqlpp_from_free_variables q_from_clause))
          ++ (sqlpp_condition_free_variables q_where_cond)
      | SPQuery q_select_clause q_from_clause None _ _ =>
        (concat (map sqlpp_select_free_variables q_select_clause))
          ++ (concat (map sqlpp_from_free_variables q_from_clause))
      | SPUnion _ q1 q2 =>
        sqlpp_query_free_variables q1 ++ sqlpp_query_free_variables q2
      | SPIntersect _ q1 q2 =>
        sqlpp_query_free_variables q1 ++ sqlpp_query_free_variables q2
      | SPExcept _ q1 q2 =>
        sqlpp_query_free_variables q1 ++ sqlpp_query_free_variables q2
      end
    with sqlpp_expr_free_variables (q_expr:sqlpp_expr) : list string :=
      match q_expr with
      | SPExprConst d => nil
      | SPExprColumn s => nil
      | SPExprColumnDeref s1 s2 => nil
      | SPExprStar => nil
      | SPExprUnary un q_expr1 =>
        sqlpp_expr_free_variables q_expr1
      | SPExprBinary bin q_expr1 q_expr2 =>
        sqlpp_expr_free_variables q_expr1 ++ sqlpp_expr_free_variables q_expr2
      | SPExprCase q_cond q_expr1 q_expr2 =>
        sqlpp_condition_free_variables q_cond ++
        sqlpp_expr_free_variables q_expr1 ++ sqlpp_expr_free_variables q_expr2
      | SPExprAggExpr agg q_expr1 =>
        sqlpp_expr_free_variables q_expr1
      | SPExprQuery q =>
        sqlpp_query_free_variables q
      end
    with sqlpp_select_free_variables (q_select:sqlpp_select) : list string :=
      match q_select with
      | SPSelectColumn s => nil
      | SPSelectColumnDeref s1 s2 => nil
      | SPSelectStar => nil
      | SPSelectExpr s q_expr => sqlpp_expr_free_variables q_expr
      end
    with sqlpp_from_free_variables (q_from:sqlpp_from) : list string :=
      match q_from with
      | SPFromTable tablename => tablename :: nil (* The important case: table access *)
      | SPFromTableAlias aliasname tablename => tablename :: nil
      | SPFromQuery ts q => sqlpp_query_free_variables q
      end
    with sqlpp_condition_free_variables (q_cond:sqlpp_condition) : list string :=
      match q_cond with
      | SPCondAnd q_cond1 q_cond2 =>
        sqlpp_condition_free_variables q_cond1 ++ sqlpp_condition_free_variables q_cond2
      | SPCondOr q_cond1 q_cond2 =>
        sqlpp_condition_free_variables q_cond1 ++ sqlpp_condition_free_variables q_cond2
      | SPCondNot q_cond1 =>
        sqlpp_condition_free_variables q_cond1
      | SPCondBinary bin q_expr1 q_expr2 =>
        sqlpp_expr_free_variables q_expr1 ++ sqlpp_expr_free_variables q_expr2
      | SPCondExists q_query =>
        sqlpp_query_free_variables q_query
      | SPCondIn q_expr1 q_expr2 =>
        sqlpp_expr_free_variables q_expr1 ++ sqlpp_expr_free_variables q_expr2
      | SPCondLike q_expr1 s =>
        sqlpp_expr_free_variables q_expr1
      | SPCondBetween q_expr1 q_expr2 q_expr3 =>
        sqlpp_expr_free_variables q_expr1 ++ sqlpp_expr_free_variables q_expr2
                                 ++ sqlpp_expr_free_variables q_expr3
      end.
    
    Definition sqlpp_statement_free_variables (q:sqlpp_statement) : list string :=
      match q with
      | SPRunQuery q => sqlpp_query_free_variables q
      | SPCreateView s q => sqlpp_query_free_variables q
      | SPDropView s => nil
      end.
    
    Definition sqlpp_free_vars (q:sqlpp) : list string :=
      bdistinct (concat (map sqlpp_statement_free_variables q)).
    
  End FreeVars.
End SQLPP.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
