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
	    ( "having" Cond )? )?                          /* having only allowed for group by */
	  ( "order by" SortCriteria ("," SortCriteria)* )?
	  
SelectExpr ::= Column | Expr "as" Column | Agg ( Expr )

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
  Inductive sql_bin_cond : Set := | SEq | SLe | SLt | SGe | SGt | SDiff.
  Inductive sql_bin_expr : Set := | SPlus | SMinus | SMult | SDivide.
  Inductive sql_agg : Set := | SSum | SAvg | SCount.

  Inductive sql_query : Set :=
  | SQuery :
      list sql_select ->                                 (* Select Clause *)
      list sql_from ->                                   (* From Clause *)
      option sql_condition ->                            (* Where Clause *)
      option ((list string) * (option sql_condition)) -> (* GroupBy Clause *)
      option sql_order_spec -> sql_query                 (* OrderBy Clause *)
  with sql_select : Set :=
  | SSelectColumn : string -> sql_select
  | SSelectExpr : string -> sql_expr -> sql_select
  with sql_from : Set :=
  | SFromTable : string -> sql_from
  | SFromQuery : sql_table_spec -> sql_query -> sql_from
  with sql_condition : Set :=
  | SCondAnd : sql_condition -> sql_condition -> sql_condition
  | SCondOr : sql_condition -> sql_condition -> sql_condition
  | SCondNot : sql_condition -> sql_condition
  | SCondBinary : sql_bin_cond -> sql_expr -> sql_expr -> sql_condition
  | SCondExists : sql_query -> sql_condition
  | SCondIn : sql_expr -> sql_expr -> sql_condition
  | SCondLike : sql_expr -> sql_expr -> sql_condition
  | SCondBetween : sql_expr -> sql_expr -> sql_expr -> sql_condition
  with sql_expr : Set :=
  | SExprConst : data -> sql_expr
  | SExprColumn : string -> sql_expr
  | SExprStar : sql_expr
  | SExprBinary : sql_bin_expr -> sql_expr -> sql_expr -> sql_expr
  | SExprAggExpr : sql_agg -> sql_expr -> sql_expr
  .

  Definition sql : Set := sql_query. (* Let's finally give our languages a proper name! *)

  Section Translation.
    Require Import NRAEnvRuntime.

    Definition sql_order_to_nraenv (acc:algenv) (opt_order:option sql_order_spec) :=
      match opt_order with
      | None => acc
      | Some sql_order_spec =>
        ANUnop (AOrderBy sql_order_spec) acc
      end.

    Fixpoint sql_to_nraenv (q:sql) {struct q} : algenv :=
      match q with
      | SQuery selects froms opt_where opt_group opt_order =>
        let nraenv_from_clause :=
            fold_left sql_from_to_nraenv froms (ANUnop AColl ANID)
        in
        let nraenv_where_clause := nraenv_from_clause in
        let nraenv_group_by_clause := nraenv_where_clause in
        let nraenv_order_by_clause := sql_order_to_nraenv nraenv_group_by_clause opt_order in
        ANMap (fold_left sql_select_to_nraenv selects (ANConst (drec nil)))
              nraenv_order_by_clause
      end
    with sql_from_to_nraenv (acc:algenv) (from:sql_from) {struct from} :=
      match from with
      | (SFromTable tname) => ANProduct (ANGetConstant tname) acc
      | _ => acc
      end
    with sql_select_to_nraenv (acc:algenv) (select:sql_select) {struct select} :=
      match select with
      | SSelectColumn cname =>
        ANBinop AConcat
                (ANUnop (ARec cname) (ANUnop (ADot cname) ANID))
                acc
      | SSelectExpr cname expr =>
        ANBinop AConcat
                (ANUnop (ARec cname) (ANUnop (ADot cname) (sql_expr_to_nraenv expr)))
                acc
      end
    with sql_expr_to_nraenv (expr:sql_expr) {struct expr} :=
      match expr with
      | SExprConst d => ANConst d
      | SExprColumn cname => ANUnop (ADot cname) ANID
      | SExprStar => ANID
      | SExprBinary SPlus expr1 expr2 =>
        ANBinop (ABArith ArithPlus)
                (sql_expr_to_nraenv expr1)
                (sql_expr_to_nraenv expr2)
      | SExprBinary SMinus expr1 expr2 =>
        ANBinop (ABArith ArithMinus)
                (sql_expr_to_nraenv expr1)
                (sql_expr_to_nraenv expr2)
      | SExprBinary SMult expr1 expr2 =>
        ANBinop (ABArith ArithMult)
                (sql_expr_to_nraenv expr1)
                (sql_expr_to_nraenv expr2)
      | SExprBinary SDivide expr1 expr2 =>
        ANBinop (ABArith ArithDivide)
                (sql_expr_to_nraenv expr1)
                (sql_expr_to_nraenv expr2)
      | SExprAggExpr _ _ => ANConst dunit
      end.

    Section SQLExamples.
      (* Example *)

      Require Import ZArith.
      Definition mkperson (name:string) (age:Z) (zip:Z) (company:string) :=
        drec (("name", dstring name)
                :: ("age", dnat age)
                :: ("zip", dnat zip)
                :: ("company", dstring company)
                :: nil)%string.
      Definition mkpersons_aux l :=
        map (fun x =>
               match x with (name, age, zip, company) => mkperson name age zip company
               end) l.
      Definition mkpersons l :=
        dcoll (mkpersons_aux l).

      Open Scope Z_scope.
      Definition persons :=
        mkpersons
          (("John",25,1008,"IBM")
             :: ("Jane",12,1009,"AIG")
             :: ("Jill",30,1010,"IBM")
             :: ("Jack",56,1010,"CMU")
             :: nil)%string.

      Definition tables := (("Persons", persons)::nil)%string.

      Definition sql1 :=
        SQuery (SSelectColumn "name"::nil) (SFromTable "Persons"::nil) None None None.
      Definition nraenv1 :=
        sql_to_nraenv sql1.

      Definition nraenv_eval (op:algenv) (constants:list (string*data))
        := fun_of_algenv nil constants op (drec nil) (drec nil).
      Definition sql_eval (q:sql) (constants:list (string*data))
        := fun_of_algenv nil constants (sql_to_nraenv q) (drec nil) (drec nil).
      
      (* Eval vm_compute in nraenv1. *)
      (* Eval vm_compute in (nraenv_eval nraenv1 tables). *)

      Definition sql2 :=
        SQuery (SSelectColumn "name"::SSelectColumn "age"::nil)
               (SFromTable "Persons"::nil) None None (Some (("age"%string,Ascending)::nil)).

      (* Eval vm_compute in (sql_eval sql2 tables). *)

      Definition sql3 :=
        SQuery (SSelectColumn "name"::nil)
               (SFromTable "Persons"::nil) None None (Some (("age"%string,Ascending)::nil)).

      (* Eval vm_compute in (sql_eval sql3 tables). *)

    End SQLExamples.
  
  End Translation.
End SQL.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
