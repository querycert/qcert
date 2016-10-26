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

    Definition nraenv_if b expr1 expr2
      :=
        ANApp
        (ANEither
          (ANApp expr1 (ANUnop (ADot "id"%string) ANID))
          (ANApp expr2 (ANUnop (ADot "id"%string) ANID)))
        (ANEitherConcat  
           (ANApp (ANEither (ANConst (dleft (drec nil))) (ANConst (dright (drec nil))))
                  (ANUnop ASingleton (ANSelect ANID (ANUnop AColl b))))
           ((ANUnop (ARec "id"%string) ANID))).

(*
    Example example_nraenv_if
      := nraenv_if
           (ANBinop AEq (ANConst (dnat 3)) (ANID))
           (ANBinop (ABArith ArithPlus) (ANConst (dnat 10)) ANID)
           (ANBinop (ABArith ArithPlus) (ANConst (dnat 20)) ANID).

    Eval vm_compute in fun_of_algenv nil nil example_nraenv_if (drec nil) (dnat 3).
    Eval vm_compute in fun_of_algenv nil nil example_nraenv_if (drec nil) (dnat 4).
*)

    Section queryvar.
      Context (view_list:list string).

      Definition lookup_table (table_name:string) : algenv
        := if in_dec string_eqdec table_name view_list
           then ANUnop (ADot table_name) ANEnv
           else ANGetConstant table_name.

    Fixpoint sql_query_to_nraenv (create_table:bool) (q:sql_query) {struct q} : algenv :=
      let q_is_singleton : bool := is_singleton_sql_query q in
      match q with
      | SUnion SAll q1 q2 =>
        ANBinop AUnion
                (sql_query_to_nraenv create_table q1)
                (sql_query_to_nraenv create_table q2)
      | SUnion SDistinct q1 q2 =>
        ANUnop ADistinct
          (ANBinop AUnion
                   (sql_query_to_nraenv create_table q1)
                   (sql_query_to_nraenv create_table q2))
      | SIntersect SAll q1 q2 =>
        ANBinop AMin (* XXX Bag minimum -- to double check XXX *)
                (sql_query_to_nraenv create_table q1)
                (sql_query_to_nraenv create_table q2)
      | SIntersect SDistinct q1 q2 =>
        ANUnop ADistinct
               (ANBinop AMin (* XXX Bag minimum -- to double check XXX *)
                        (sql_query_to_nraenv create_table q1)
                        (sql_query_to_nraenv create_table q2))
      | SExcept SAll q1 q2 =>
        ANBinop AMinus (* XXX Bag difference -- to double check XXX *)
                (sql_query_to_nraenv create_table q1)
                (sql_query_to_nraenv create_table q2)
      | SExcept SDistinct q1 q2 =>
        ANUnop ADistinct
               (ANBinop AMinus (* XXX Bag minimum -- to double check XXX *)
                        (sql_query_to_nraenv create_table q1)
                        (sql_query_to_nraenv create_table q2))
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
      | (SFromTable tname) => ANProduct (lookup_table tname) acc
      | (SFromTableAlias new_name tname) =>
        ANProduct (ANMap (ANUnop (ARec new_name) ANID) (lookup_table tname)) acc
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
      | SExprBinary SSubtract expr1 expr2 =>
        ANBinop (ABArith ArithMinus)
                (sql_expr_to_nraenv create_table acc expr1)
                (sql_expr_to_nraenv create_table acc expr2)
      | SExprUnary SMinus expr1 =>
        ANBinop (ABArith ArithMinus)
                (ANConst (dnat 0))
                (sql_expr_to_nraenv create_table acc expr1)
      | SExprBinary SMult expr1 expr2 =>
        ANBinop (ABArith ArithMult)
                (sql_expr_to_nraenv create_table acc expr1)
                (sql_expr_to_nraenv create_table acc expr2)
      | SExprBinary SDivide expr1 expr2 =>
        ANBinop (ABArith ArithDivide)
                (sql_expr_to_nraenv create_table acc expr1)
                (sql_expr_to_nraenv create_table acc expr2)
      | SExprBinary SConcat expr1 expr2 =>
        ANBinop ASConcat
                (sql_expr_to_nraenv create_table acc expr1)
                (sql_expr_to_nraenv create_table acc expr2)
      | SExprCase cond expr1 expr2 =>
        nraenv_if
                 (sql_condition_to_nraenv acc cond)
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

    Definition sql_query_to_nraenv_top (q:sql_query) : algenv :=
      ANApp (sql_query_to_nraenv true q) (ANConst (drec nil)). (* XXX Always initialize ID to an empty record XXX *)

    End queryvar.

    (* we currently keep only the value of the last select statement *)
    (* the input environment is assumed to be a record with fields "view_list" *)
    Fixpoint sql_statements_to_nraenv
               (view_list:list string) (q:sql) : algenv
      := match q with
         | nil => ANID
         | (SRunQuery q)::rest =>
           ANApp
             (sql_statements_to_nraenv view_list rest)
             (sql_query_to_nraenv_top view_list q)
         | (SCreateView s q)::rest =>
            ANAppEnv 
              (sql_statements_to_nraenv (s::view_list) rest)
              (ANBinop AConcat
                      ANEnv
                      (ANUnop (ARec s)
                              (sql_query_to_nraenv_top view_list q)))
         | (SDropView s)::rest =>
           ANAppEnv
             (sql_statements_to_nraenv (remove_all s view_list) rest)
             (ANUnop (ARecRemove s) ANEnv)
         end
    .

  (* If there is no select statement, we default to dunit *)
  Definition sql_to_nraenv (q:sql) : algenv
    :=
      ANAppEnv
        (ANApp (sql_statements_to_nraenv nil q) (ANConst dunit))
        (ANConst (drec nil)).

  End Translation.

  Section SQLEval.
    (* For now: SQL evaluation through translation *)
    Definition nraenv_eval (op:algenv) (constants:list (string*data))
      := fun_of_algenv nil constants op (drec nil) (drec nil).
    Definition sql_eval (q:sql) (constants:list (string*data))
      := fun_of_algenv nil constants (sql_to_nraenv q) (drec nil) (drec nil).
  End SQLEval.

  Section SQLSize.

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

  End SQLSize.

  Section SQLDepth.

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
      | SSelectColumn _ => 1
      | SSelectColumnDeref _ _ => 1
      | SSelectStar => 1
      | SSelectExpr _ e => sql_expr_depth e
      end

    with sql_from_depth (from: sql_from) :=
      match from with
      | SFromTable _ => 1
      | SFromTableAlias _ _ => 1
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
      | SRunQuery q => sql_query_depth q
      | SCreateView _ q => sql_query_depth q
      | SDropView _ => 1
      end.

    Definition sql_depth (q:sql) :=
      List.fold_left (fun acc st => max acc (sql_statement_depth st)) q 0.

  End SQLDepth.
  
End SQL.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
