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

(****************
 * SQL mini-BNF *
 ****************

// From inspecting the TPC-H queries

Query ::= "select" SelectExpr ("," SelectExpr)*
          "from" FromExpr ("," FromExpr)*
          ( "where" Cond )?
	  ( "group by" GroupExpr ("," GroupExpr)*
	    ( "having" Cond )? )?                          // having only allowed for group by
	  ( "order by" SortCriteria ("," SortCriteria)* )?
	  
SelectExpr ::= Column | * | Expr "as" Column

Agg ::= "sum" | "avg" | "count"

FromExpr ::= TableName | "(" Query ")" "as" TableSpec

Condition ::= Condition ("and" | "or") Condition
      |  "not" Condition
      |  Expr ("=" | "<=" | "<" | ">" | ">=" | "<>") Expr
      |  "exists" "(" Query ")"
      |  Expr "in" Expr
      |  Expr "not" "in" Expr
      |  Expr "like" Expr
      |  Expr "between" Expr "and" Expr

GroupExpr ::= Column

SortCriteria ::= Column ("asc" | "desc")?

Expr ::= Constant
      |  Column
      |  "*"
      |  Expr ("-" | "+" | "*" | "/") Expr
      |  Agg "(" Expr ")"

Constant ::= INT | FLOAT | STRING | "date" STRING
          |  "(" Constant ("," Constant)* ")"

TableSpec ::= TableName ( "(" Column ("," Column)* ")" )?
Column ::= IDENT
TableName ::= IDENT

Note: Do we want to support 'case' (q12) -- seems relatively big an extension
Note: Do we want to support 'substring' (q22) -- seems just meh...
Note: Do we want to support 'create view' (q15) -- seems relatively trivial through environments

*)

Section SQL.

  Require Import String.
  Require Import ZArith.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.

  Require Import Utils BasicSystem.

  Context {fruntime:foreign_runtime}.

  Require Import RDataSort. (* For SortCriterias *)

  Unset Elimination Schemes.

  Definition sql_env := list (string * data). (* For eval -- unused now *)

  Definition sql_table_spec : Set := string * (option (list string)).
  Definition sql_order_spec : Set := SortCriterias.
  Inductive sql_bin_cond : Set :=
  | SEq | SLe | SLt | SGe | SGt | SDiff
  | SBinaryForeignCond (fb : foreign_binary_op_type) : sql_bin_cond.
  Inductive sql_un_expr : Set :=
  | SMinus : sql_un_expr
  | SSubstring : Z -> option Z -> sql_un_expr
  | SUnaryForeignExpr (fu:foreign_unary_op_type) : sql_un_expr.
  Inductive sql_bin_expr : Set :=
  | SPlus | SSubtract | SMult | SDivide
  | SConcat
  | SBinaryForeignExpr (fb : foreign_binary_op_type) : sql_bin_expr.
  Inductive sql_agg : Set := | SSum | SAvg | SCount | SMin | SMax.

  Inductive sql_distinct : Set := SDistinct | SAll.
  
  Inductive sql_query : Set :=
  | SQuery :
      list sql_select ->                                 (* Select Clause *)
      list sql_from ->                                   (* From Clause *)
      option sql_condition ->                            (* Where Clause *)
      option ((list string) * (option sql_condition)) -> (* GroupBy Clause *)
      option sql_order_spec -> sql_query                 (* OrderBy Clause *)
  | SUnion :
      sql_distinct -> sql_query -> sql_query -> sql_query
  | SIntersect :
      sql_distinct -> sql_query -> sql_query -> sql_query
  | SExcept :
      sql_distinct -> sql_query -> sql_query -> sql_query
  with sql_select : Set :=
  | SSelectColumn : string -> sql_select
  | SSelectColumnDeref : string -> string -> sql_select
  | SSelectStar : sql_select
  | SSelectExpr : string -> sql_expr -> sql_select
  with sql_from : Set :=
  | SFromTable : string -> sql_from
  | SFromTableAlias : string -> string -> sql_from
  | SFromQuery : sql_table_spec -> sql_query -> sql_from
  with sql_condition : Set :=
  | SCondAnd : sql_condition -> sql_condition -> sql_condition
  | SCondOr : sql_condition -> sql_condition -> sql_condition
  | SCondNot : sql_condition -> sql_condition
  | SCondBinary : sql_bin_cond -> sql_expr -> sql_expr -> sql_condition
  | SCondExists : sql_query -> sql_condition
  | SCondIn : sql_expr -> sql_expr -> sql_condition
  | SCondLike : sql_expr -> string -> sql_condition
  | SCondBetween : sql_expr -> sql_expr -> sql_expr -> sql_condition
  with sql_expr : Set :=
  | SExprConst : data -> sql_expr
  | SExprColumn : string -> sql_expr
  | SExprColumnDeref : string -> string -> sql_expr
  | SExprStar : sql_expr
  | SExprUnary : sql_un_expr -> sql_expr -> sql_expr
  | SExprBinary : sql_bin_expr -> sql_expr -> sql_expr -> sql_expr
  | SExprCase : sql_condition -> sql_expr -> sql_expr -> sql_expr
  | SExprAggExpr : sql_agg -> sql_expr -> sql_expr
  | SExprQuery : sql_query -> sql_expr (* relatively broad allowance for nesting... *)
  .

  Inductive sql_statement : Set :=
  | SRunQuery : sql_query -> sql_statement
  | SCreateView : string -> sql_query -> sql_statement
  | SDropView : string -> sql_statement
  .

  (* Let's finally give our languages a proper name! *)
  Definition sql : Set := list sql_statement.

  (* Note: Has to be reviewed carefully -- The semantics differs
     widely for the 'singleton' vs 'non-singleton' case *)
  Fixpoint is_singleton_sql_query (q:sql_query) : bool :=
    match q with
    | SUnion _ _ _ => false
    | SIntersect _ _ _ => false
    | SExcept _ _ _ => false
    | SQuery (SSelectExpr _ expr :: nil) _ _ None None =>
      is_singleton_sql_expr expr
    | SQuery _ _ _ _ _ => false
    end
  with is_singleton_sql_expr (expr:sql_expr) : bool :=
    match expr with
    | SExprConst _ => true
    | SExprColumn _ => false
    | SExprColumnDeref _ _ => false
    | SExprStar => false
    | SExprUnary _ expr1 =>
      is_singleton_sql_expr expr1
    | SExprBinary _ expr1 expr2 =>
      is_singleton_sql_expr expr1 && is_singleton_sql_expr expr2
    | SExprCase _ expr1 expr2 =>
      is_singleton_sql_expr expr1 && is_singleton_sql_expr expr2
    | SExprAggExpr _ _ => true
    | SExprQuery q => is_singleton_sql_query q
    end.
  
  (* Note: Has to be reviewed carefully -- similar predicate but
     checking that the result is a single column (used in 'in'
     predicate for unboxing) *)
  
  Fixpoint is_value_sequence_sql_query (q:sql_query) : bool :=
    match q with
    | SUnion _ q1 q2 =>
      if is_value_sequence_sql_query q1
      then is_value_sequence_sql_query q2
      else false
    | SIntersect _ q1 q2 =>
      if is_value_sequence_sql_query q1
      then is_value_sequence_sql_query q2
      else false
    | SExcept _ q1 q2 =>
      if is_value_sequence_sql_query q1
      then is_value_sequence_sql_query q2
      else false
    | SQuery (SSelectExpr _ expr :: nil) _ _ _ _ =>
      if (is_singleton_sql_expr expr) then false else true
    | SQuery (SSelectColumn _ :: nil) _ _ _ _ => true
    | SQuery (SSelectColumnDeref _ _ :: nil) _ _ _ _ => true
    | SQuery _ _ _ _ _ => false
    end.
  
End SQL.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
