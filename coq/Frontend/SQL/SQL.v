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
  | SSelectStar : sql_select
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
  | SExprQuery : sql_query -> sql_expr (* relatively broad allowance for nesting... *)
  .

  Definition sql : Set := sql_query. (* Let's finally give our languages a proper name! *)

  (* Note: Has to be reviewed carefully -- The semantics differs
     widely for the 'singleton' vs 'non-singleton' case *)
  Fixpoint is_singleton_sql_query (q:sql) : bool :=
    match q with
    | SQuery (SSelectExpr _ expr :: nil) _ _ None _ =>
      is_singleton_sql_expr expr
    | _ => false
    end
  with is_singleton_sql_expr (expr:sql_expr) : bool :=
    match expr with
    | SExprConst _ => true
    | SExprColumn _ => false
    | SExprStar => false
    | SExprBinary _ expr1 expr2 =>
      is_singleton_sql_expr expr1 && is_singleton_sql_expr expr2
    | SExprAggExpr _ _ => true
    | SExprQuery q => is_singleton_sql_query q
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

    Fixpoint sql_to_nraenv (q:sql) {struct q} : algenv :=
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
        let nraenv_order_by_clause := sql_order_to_nraenv nraenv_group_by_clause opt_order in
        if q_is_singleton (* XXX Two different translations here! XXX *)
        then
          match selects with
          | SSelectExpr _ expr :: nil =>
            sql_expr_to_nraenv nraenv_order_by_clause expr
          | _ => ANConst dunit (* XXX This should be really a compilation error XXX *)
          end
        else
          ANMap (fold_left sql_select_to_nraenv selects (ANConst (drec nil)))
                nraenv_order_by_clause
      end
    with sql_from_to_nraenv (acc:algenv) (from:sql_from) {struct from} :=
      match from with
      | (SFromTable tname) => ANProduct (ANGetConstant tname) acc
      | SFromQuery tspec q =>
        let (tname,opt_columns) := tspec in
        match opt_columns with
        | Some columns => sql_to_nraenv q (* XXX Must add renaming in this case XXX *)
        | None => sql_to_nraenv q
        end
      end
    with sql_select_to_nraenv (acc:algenv) (select:sql_select) {struct select} :=
      match select with
      | SSelectColumn cname =>
        ANBinop AConcat
                (ANUnop (ARec cname) (ANUnop (ADot cname) ANID))
                acc
      | SSelectStar =>
        ANBinop AConcat ANID acc
      | SSelectExpr cname expr =>
        ANBinop AConcat
                (ANUnop (ARec cname) (sql_expr_to_nraenv (ANUnop (ADot "partition") ANID) expr))
                acc
      end
    with sql_expr_to_nraenv (acc:algenv) (expr:sql_expr) {struct expr} :=
      match expr with
      | SExprConst d => ANConst d
      | SExprColumn cname => ANUnop (ADot cname) ANID
      | SExprStar => ANID
      | SExprBinary SPlus expr1 expr2 =>
        ANBinop (ABArith ArithPlus)
                (sql_expr_to_nraenv acc expr1)
                (sql_expr_to_nraenv acc expr2)
      | SExprBinary SMinus expr1 expr2 =>
        ANBinop (ABArith ArithMinus)
                (sql_expr_to_nraenv acc expr1)
                (sql_expr_to_nraenv acc expr2)
      | SExprBinary SMult expr1 expr2 =>
        ANBinop (ABArith ArithMult)
                (sql_expr_to_nraenv acc expr1)
                (sql_expr_to_nraenv acc expr2)
      | SExprBinary SDivide expr1 expr2 =>
        ANBinop (ABArith ArithDivide)
                (sql_expr_to_nraenv acc expr1)
                (sql_expr_to_nraenv acc expr2)
      | SExprAggExpr SSum expr1 =>
        ANUnop ASum (ANMap (sql_expr_to_nraenv ANID expr1) acc)
      | SExprAggExpr SAvg expr1 =>
        ANUnop AArithMean (ANMap (sql_expr_to_nraenv ANID expr1) acc)
      | SExprAggExpr SCount expr1 =>
        ANUnop ACount (ANMap (sql_expr_to_nraenv ANID expr1) acc)
      | SExprQuery q => sql_to_nraenv q
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
               (sql_expr_to_nraenv acc expr1)
               (sql_expr_to_nraenv acc expr2)
      | SCondBinary SLe expr1 expr2 =>
        ANBinop ALe
               (sql_expr_to_nraenv acc expr1)
               (sql_expr_to_nraenv acc expr2)
      | SCondBinary SLt expr1 expr2 =>
        ANBinop ALt
               (sql_expr_to_nraenv acc expr1)
               (sql_expr_to_nraenv acc expr2)
      | SCondBinary SGe expr1 expr2 =>
        ANUnop ANeg (ANBinop ALt
                             (sql_expr_to_nraenv acc expr1)
                             (sql_expr_to_nraenv acc expr2))
      | SCondBinary SGt expr1 expr2 =>
        ANUnop ANeg (ANBinop ALe
                             (sql_expr_to_nraenv acc expr1)
                             (sql_expr_to_nraenv acc expr2))
      | SCondBinary SDiff expr1 expr2 =>
        ANUnop ANeg (ANBinop AEq
                             (sql_expr_to_nraenv acc expr1)
                             (sql_expr_to_nraenv acc expr2))
      | _ => ANConst (dbool true)
      end.

  End Translation.

  Section SQLEval.
    (* For now: SQL evaluation through translation *)
    Definition nraenv_eval (op:algenv) (constants:list (string*data))
      := fun_of_algenv nil constants op (drec nil) (drec nil).
    Definition sql_eval (q:sql) (constants:list (string*data))
      := fun_of_algenv nil constants (sql_to_nraenv q) (drec nil) (drec nil).
  End SQLEval.

  Section SQLExamples.
    (* Some Working Examples *)

    Require Import ZArith.
    Open Scope Z_scope.

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

    Definition persons :=
      mkpersons
        (("John",30,1008,"IBM")
           :: ("Jane",12,1009,"AIG")
           :: ("Joan",30,1008,"AIG")
           :: ("Jade",30,1008,"AIG")
           :: ("Jacques",30,1008,"AIG")
           :: ("Jill",25,1010,"IBM")
           :: ("Joo",25,1010,"IBM")
           :: ("Just",12,1010,"IBM")
           :: ("Jack",56,1010,"CMU")
           :: ("Jerome",56,1010,"CMU")
           :: nil)%string.

    Definition tables := (("Persons", persons)::nil)%string.

    (* sql1:
        select name
        from Persons *)
    Definition sql1 :=
      SQuery (SSelectColumn "name"::nil) (SFromTable "Persons"::nil) None None None.
    Definition nraenv1 :=
      sql_to_nraenv sql1.

    (* Eval vm_compute in nraenv1. *)
    (* Eval vm_compute in (nraenv_eval nraenv1 tables). *)

    (* sql2:
         select name,
                age
         from Persons
         order by age *)
    Definition sql2 :=
      SQuery (SSelectColumn "name"::SSelectColumn "age"::nil)
             (SFromTable "Persons"::nil) None None (Some (("age"%string,Ascending)::nil)).

    (* Eval vm_compute in (sql_eval sql2 tables). *)

    (* sql3:
         select name
         from Persons
         order by age *)
    Definition sql3 :=
      SQuery (SSelectColumn "name"::nil)
             (SFromTable "Persons"::nil) None None (Some (("age"%string,Ascending)::nil)).

    (* Eval vm_compute in (sql_eval sql3 tables). *)

    (* sql4:
         select name
         from Persons
         where company = 'IBM'
         order by age *)
    Definition sql4 :=
      SQuery (SSelectColumn "name"::nil)
             (SFromTable "Persons"::nil)
             (Some (SCondBinary SEq (SExprColumn "company")
                                (SExprConst (dstring "IBM"))))
             None (Some (("age"%string,Ascending)::nil)).

    (* Eval vm_compute in (sql_eval sql4 tables). *)

    (* sql5:
         select sum(age)
         from Persons *)
    Definition sql5 :=
      SQuery (SSelectExpr ""
                          (SExprAggExpr SSum (SExprColumn "age"))::nil)
             (SFromTable "Persons"::nil) None None None.

    (* Eval vm_compute in (sql_eval sql5 tables). *)

    (* sql6:
         select count( * )
         from Persons *)
    Definition sql6 :=
      SQuery (SSelectExpr ""
                          (SExprAggExpr SCount SExprStar)::nil)
             (SFromTable "Persons"::nil) None None None.

    (* Eval vm_compute in (sql_eval sql6 tables). *)

    (* sql7:
         select count( * )
           from
              ( select name
                from Persons
                where company = 'IBM'
                order by age ) as IBMers
     *)
    Definition sql7 :=
      SQuery (SSelectExpr ""
                          (SExprAggExpr SCount SExprStar)::nil)
             (SFromQuery ("IBMers"%string,None) sql4 :: nil) None None None.

    (* Eval vm_compute in (sql_eval sql7 tables). *)

    (* sql8:
        select *
        from Persons
        group by age *)
    Definition sql8 :=
      SQuery (SSelectExpr "res" SExprStar::nil)
             (SFromTable "Persons"::nil) None (Some (("age"%string::nil),None)) None.

    (* Eval vm_compute in (sql_eval sql8 tables). *)

    (* sql9:
        select age, count( * ) as nb
        from Persons
        group by age *)
    Definition sql9 :=
      SQuery (SSelectColumn "age" :: SSelectExpr "nb"
                            (SExprAggExpr SCount SExprStar)::nil)
             (SFromTable "Persons"::nil) None (Some (("age"%string::nil),None)) None.

    (* Eval vm_compute in (sql_eval sql9 tables). *)

    (* sql10:
        select age, count( * ) as nb
        from Persons
        group by age
        order by age *)
    Definition sql10 :=
      SQuery (SSelectColumn "age" :: SSelectExpr "nb"
                            (SExprAggExpr SCount SExprStar)::nil)
             (SFromTable "Persons"::nil) None
             (Some (("age"%string::nil),None)) (Some (("age"%string,Ascending)::nil)).

    (* Eval vm_compute in (sql_eval sql10 tables). *)

    (* sql11:
        select age, count( * ) as nb
        from Persons
        group by age
        having count( * ) > 1
        order by age
   *)
    Definition sql11 :=
      SQuery (SSelectColumn "age" :: SSelectExpr "nb"
                            (SExprAggExpr SCount SExprStar)::nil)
             (SFromTable "Persons"::nil)
             None (Some (("age"%string::nil),
                         Some (SCondBinary SGt (SExprAggExpr SCount SExprStar)
                                           (SExprConst (dnat 1)))))
             (Some (("age"%string,Ascending)::nil)).

    (* sql12:
        select age, company, count( * ) as nb
        from Persons
        group by age, company
        // order by age  -- BUG IN ORDERBY REMOVING DUPLICATES
     *)
    Definition sql12 :=
      SQuery (SSelectColumn "age" :: SSelectColumn "company" :: SSelectExpr "nb"
                            (SExprAggExpr SCount SExprStar)::nil)
             (SFromTable "Persons"::nil)
             None
             (Some (("age"%string::"company"%string::nil),None)) None.

    (* Eval vm_compute in (sql_eval sql12 tables). *)

  End SQLExamples.
  
End SQL.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
