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
  | SSubstring : Z -> option Z -> sql_un_expr
  | SUnaryForeignExpr (fu:foreign_unary_op_type) : sql_un_expr.
  Inductive sql_bin_expr : Set :=
  | SPlus | SMinus | SMult | SDivide
  | SBinaryForeignExpr (fb : foreign_binary_op_type) : sql_bin_expr.
  Inductive sql_agg : Set := | SSum | SAvg | SCount | SMin | SMax.

  Inductive sql_query : Set :=
  | SQuery :
      list sql_select ->                                 (* Select Clause *)
      list sql_from ->                                   (* From Clause *)
      option sql_condition ->                            (* Where Clause *)
      option ((list string) * (option sql_condition)) -> (* GroupBy Clause *)
      option sql_order_spec -> sql_query                 (* OrderBy Clause *)
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
  | SExprAggExpr : sql_agg -> sql_expr -> sql_expr
  | SExprQuery : sql_query -> sql_expr (* relatively broad allowance for nesting... *)
  .

  Definition sql : Set := sql_query. (* Let's finally give our languages a proper name! *)

  (* Note: Has to be reviewed carefully -- The semantics differs
     widely for the 'singleton' vs 'non-singleton' case *)
  Fixpoint is_singleton_sql_query (q:sql) : bool :=
    match q with
    | SQuery (SSelectExpr _ expr :: nil) _ _ None None =>
      is_singleton_sql_expr expr
    | _ => false
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
    | SExprAggExpr _ _ => true
    | SExprQuery q => is_singleton_sql_query q
    end.
  
  (* Note: Has to be reviewed carefully -- similar predicate but
     checking that the result is a single column (used in 'in'
     predicate for unboxing) *)
  
  Fixpoint is_value_sequence_sql_query (q:sql) : bool :=
    match q with
    | SQuery (SSelectExpr _ expr :: nil) _ _ _ _ =>
      if (is_singleton_sql_expr expr) then false else true
    | SQuery (SSelectColumn _ :: nil) _ _ _ _ => true
    | SQuery (SSelectColumnDeref _ _ :: nil) _ _ _ _ => true
    | _ => false
    end.
  
  Section Translation.
    Require Import NRAEnvRuntime.

    Require Import RAlgEnvExt.
    
    Definition sql_order_to_nraenv (acc:algenv) (opt_order:option sql_order_spec) :=
      match opt_order with
      | None => acc
      | Some sql_order_spec =>
        ANUnop (AOrderBy sql_order_spec) acc
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
    
    Definition columns_of_query (q:sql) : list (option string * string) :=
      match q with
      | SQuery selects _ _ _ _ =>
        columns_of_selects selects
      end.

    Fixpoint create_renaming
             (out_columns:list string)
             (in_columns:list (option string * string)) :=
      match out_columns,in_columns with
      | nil,_ | _,nil =>  (ANConst (drec nil))
      | out_cname :: out_columns', (None,in_cname) :: in_columns' =>
        ANBinop AConcat
                (ANUnop (ARec out_cname) (ANUnop (ADot in_cname) ANID))
                (create_renaming out_columns' in_columns')
      | out_cname :: out_columns', (Some in_tname,in_cname) :: in_columns' =>
        ANBinop AConcat
                (ANUnop (ARec out_cname) (ANUnop (ADot in_cname) (ANUnop (ADot in_tname) ANID)))
                (create_renaming out_columns' in_columns')
      end.
    
    Fixpoint sql_query_to_nraenv (create_table:bool) (q:sql) {struct q} : algenv :=
      let q_is_singleton : bool := is_singleton_sql_query q in
      match q with
      | SQuery selects froms opt_where opt_group opt_order =>
        let nraenv_from_clause :=
            fold_left sql_from_to_nraenv froms (ANUnop AColl ANID)
        in
        let nraenv_where_clause :=
            match opt_where with
            | None => nraenv_from_clause
            | Some cond => ANSelect (sql_condition_to_nraenv ANID cond) nraenv_from_clause
            end
        in
        let nraenv_group_by_clause :=
            match opt_group with
            | None => nraenv_where_clause
            | Some (sl,None) => group_full "partition" sl nraenv_where_clause
            | Some (sl,Some cond) =>
              ANSelect (sql_condition_to_nraenv (ANUnop (ADot "partition") ANID) cond)
                       (group_full "partition" sl nraenv_where_clause)
            end
        in
        let nraenv_select_clause :=
            if q_is_singleton (* XXX Two different translations here! XXX *)
            then
              match selects with
              | SSelectExpr _ expr :: nil =>
                sql_expr_to_nraenv true nraenv_group_by_clause expr
              | _ => ANConst dunit (* XXX This should be really a compilation error XXX *)
              end
            else
              if create_table
              then
                ANMap (fold_left sql_select_to_nraenv selects (ANConst (drec nil)))
                      nraenv_group_by_clause
              else
                if (is_value_sequence_sql_query q)
                then
                  match selects with
                  | SSelectExpr _ expr :: nil =>
                    ANMap (sql_expr_to_nraenv false ANID expr) nraenv_group_by_clause
                  | SSelectColumn cname :: nil =>
                    ANMap (ANUnop (ADot cname) ANID) nraenv_group_by_clause
                  | SSelectColumnDeref tname cname :: nil =>
                    ANMap (ANUnop (ADot cname) (ANUnop (ADot tname) ANID)) nraenv_group_by_clause
                  | _ => ANConst dunit (* XXX This should be really a compilation error XXX *)
                  end
                else
                  ANConst dunit (* XXX This should be really a compilation error XXX *)
        in
        let nraenv_order_by_clause := sql_order_to_nraenv nraenv_select_clause opt_order in
        nraenv_order_by_clause
      end
    with sql_from_to_nraenv (acc:algenv) (from:sql_from) {struct from} :=
      match from with
      | (SFromTable tname) => ANProduct (ANGetConstant tname) acc
      | (SFromTableAlias new_name tname) =>
        ANProduct (ANMap (ANUnop (ARec new_name) ANID) (ANGetConstant tname)) acc
      | SFromQuery tspec q =>
        let (tname,opt_columns) := tspec in
        match opt_columns with
        | Some out_columns =>
          let in_columns := columns_of_query q in
          ANMap (create_renaming out_columns in_columns)
                (sql_query_to_nraenv true q)
        | None => sql_query_to_nraenv true q
        end
      end
    with sql_select_to_nraenv (acc:algenv) (select:sql_select) {struct select} :=
      match select with
      | SSelectColumn cname =>
        ANBinop AConcat
                (ANUnop (ARec cname) (ANUnop (ADot cname) ANID))
                acc
      | SSelectColumnDeref tname cname =>
        ANBinop AConcat
                (ANUnop (ARec cname) (ANUnop (ADot cname) (ANUnop (ADot tname) ANID)))
                acc
      | SSelectStar =>
        ANBinop AConcat ANID acc
      | SSelectExpr cname expr =>
        ANBinop AConcat
                (ANUnop (ARec cname) (sql_expr_to_nraenv false (ANUnop (ADot "partition") ANID) expr))
                acc
      end
    with sql_expr_to_nraenv (create_table:bool) (acc:algenv) (expr:sql_expr) {struct expr} :=
      match expr with
      | SExprConst d => ANConst d
      | SExprColumn cname => ANUnop (ADot cname) ANID
      | SExprColumnDeref tname cname => ANUnop (ADot cname) (ANUnop (ADot tname) ANID)
      | SExprStar => ANID
      | SExprUnary (SSubstring n1 on2) expr1 =>
        ANUnop (ASubstring n1 on2)
                (sql_expr_to_nraenv create_table acc expr1)
      | SExprUnary (SUnaryForeignExpr fu) expr1 =>
        ANUnop (AForeignUnaryOp fu)
                (sql_expr_to_nraenv create_table acc expr1)
      | SExprBinary (SBinaryForeignExpr fb) expr1 expr2 =>
        ANBinop (AForeignBinaryOp fb)
                (sql_expr_to_nraenv create_table acc expr1)
                (sql_expr_to_nraenv create_table acc expr2)
      | SExprBinary SPlus expr1 expr2 =>
        ANBinop (ABArith ArithPlus)
                (sql_expr_to_nraenv create_table acc expr1)
                (sql_expr_to_nraenv create_table acc expr2)
      | SExprBinary SMinus expr1 expr2 =>
        ANBinop (ABArith ArithMinus)
                (sql_expr_to_nraenv create_table acc expr1)
                (sql_expr_to_nraenv create_table acc expr2)
      | SExprBinary SMult expr1 expr2 =>
        ANBinop (ABArith ArithMult)
                (sql_expr_to_nraenv create_table acc expr1)
                (sql_expr_to_nraenv create_table acc expr2)
      | SExprBinary SDivide expr1 expr2 =>
        ANBinop (ABArith ArithDivide)
                (sql_expr_to_nraenv create_table acc expr1)
                (sql_expr_to_nraenv create_table acc expr2)
      | SExprAggExpr SSum expr1 =>
        ANUnop ASum (ANMap (sql_expr_to_nraenv create_table ANID expr1) acc)
      | SExprAggExpr SAvg expr1 =>
        ANUnop AArithMean (ANMap (sql_expr_to_nraenv create_table ANID expr1) acc)
      | SExprAggExpr SCount expr1 =>
        ANUnop ACount (ANMap (sql_expr_to_nraenv create_table ANID expr1) acc)
      | SExprAggExpr SMin expr1 =>
        ANUnop ANumMin (ANMap (sql_expr_to_nraenv create_table ANID expr1) acc)
      | SExprAggExpr SMax expr1 =>
        ANUnop ANumMax (ANMap (sql_expr_to_nraenv create_table ANID expr1) acc)
      | SExprQuery q =>
        if create_table
        then sql_query_to_nraenv true q
        else sql_query_to_nraenv false q
      end
    with sql_condition_to_nraenv (acc:algenv) (cond:sql_condition) {struct cond} :=
      match cond with
      | SCondAnd cond1 cond2 =>
        ANBinop AAnd
                (sql_condition_to_nraenv acc cond1)
                (sql_condition_to_nraenv acc cond2)
      | SCondOr cond1 cond2 =>
        ANBinop AOr
                (sql_condition_to_nraenv acc cond1)
                (sql_condition_to_nraenv acc cond2)
      | SCondNot cond1 =>
        ANUnop ANeg
                (sql_condition_to_nraenv acc cond1)
      | SCondBinary SEq expr1 expr2 =>
        ANBinop AEq
               (sql_expr_to_nraenv true acc expr1)
               (sql_expr_to_nraenv true acc expr2)
      | SCondBinary SLe expr1 expr2 =>
        ANBinop ALe
               (sql_expr_to_nraenv true acc expr1)
               (sql_expr_to_nraenv true acc expr2)
      | SCondBinary SLt expr1 expr2 =>
        ANBinop ALt
               (sql_expr_to_nraenv true acc expr1)
               (sql_expr_to_nraenv true acc expr2)
      | SCondBinary SGe expr1 expr2 =>
        ANUnop ANeg (ANBinop ALt
                             (sql_expr_to_nraenv true acc expr1)
                             (sql_expr_to_nraenv true acc expr2))
      | SCondBinary SGt expr1 expr2 =>
        ANUnop ANeg (ANBinop ALe
                             (sql_expr_to_nraenv true acc expr1)
                             (sql_expr_to_nraenv true acc expr2))
      | SCondBinary SDiff expr1 expr2 =>
        ANUnop ANeg (ANBinop AEq
                             (sql_expr_to_nraenv true acc expr1)
                             (sql_expr_to_nraenv true acc expr2))
      | SCondBinary (SBinaryForeignCond fb) expr1 expr2 =>
        ANBinop (AForeignBinaryOp fb)
                (sql_expr_to_nraenv true acc expr1)
                (sql_expr_to_nraenv true acc expr2)
      | SCondExists q =>
        ANUnop ANeg (ANBinop ALe
                             (ANUnop ACount (sql_query_to_nraenv true q))
                             (ANConst (dnat 0)))
      | SCondIn expr1 expr2 =>
        ANBinop AContains
                (sql_expr_to_nraenv true acc expr1)
                (sql_expr_to_nraenv false acc expr2)
      | SCondLike expr1 slike =>
        ANUnop (ALike slike None) (sql_expr_to_nraenv true acc expr1)
      | SCondBetween expr1 expr2 expr3 =>
        ANBinop AAnd
                (ANBinop ALe
                         (sql_expr_to_nraenv true acc expr2)
                         (sql_expr_to_nraenv true acc expr1))
                (ANBinop ALe
                         (sql_expr_to_nraenv true acc expr1)
                         (sql_expr_to_nraenv true acc expr3))
      end.

    Definition sql_to_nraenv (q:sql) : algenv :=
      ANApp (sql_query_to_nraenv true q) (ANConst (drec nil)). (* XXX Always initialize ID to an empty record XXX *)
    
  End Translation.

  Section SQLEval.
    (* For now: SQL evaluation through translation *)
    Definition nraenv_eval (op:algenv) (constants:list (string*data))
      := fun_of_algenv nil constants op (drec nil) (drec nil).
    Definition sql_eval (q:sql) (constants:list (string*data))
      := fun_of_algenv nil constants (sql_to_nraenv q) (drec nil) (drec nil).
  End SQLEval.

  Section SQLSize.
    (* For now: SQL size is size of query plan *)
    Require Import RAlgEnvSize.
    Definition sql_size (q:sql) := algenv_size (sql_to_nraenv q).
  End SQLSize.
  
End SQL.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
