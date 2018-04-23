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

(* Notations *)

Require Import List.
Require Import Utils.
Require Import CommonRuntime.

Import ListNotations.

Delimit Scope data_scope with data.

Notation "⊥" := (dunit) : data_scope. (* null value *)

Notation "[||]" := (drec nil) : data_scope. (* records *)
Notation "[| x1 ; .. ; xn |]" := (drec (cons x1 .. (cons xn nil) ..)) : data_scope.

Notation "{||}" := (dcoll nil) : data_scope. (* collections *)
Notation "{| x1 ; .. ; xn |}" := (dcoll (cons x1 .. (cons xn nil) ..)) : data_scope.

Require Import String.
Require Import ZArith.
Require Import SQL.
Require Import SQLtoNRAEnv.
Require Import EnhancedModel.
Require Import CompEval.
  
Section SQLTest.
  Open Scope Z_scope.

  Local Open Scope string_scope.
  Local Open Scope data_scope.

  (*****************
   * Preliminaries *
   *****************)

  (* Some useful functions *)

  Fixpoint natcoll_aux (n n0:nat) : list data :=
    match n with
      | O => nil
      | S n' => (dnat (Z_of_nat (n0 - n))) :: (natcoll_aux n' n0)
    end.

  Definition natcoll (n:nat) : data :=
    (dcoll (natcoll_aux n (n+1))).

  (* Notation examples *)

  (* Eval compute in ⊥.   (* Null value *) *)

  Example ex1 := [||].   (* Records *)
  (* Eval compute in ex1. *)
  (* Eval compute in [| ("a", dnat 3) |]. *)

  (* Eval compute in (natcoll 10).  (* Collections *) *)
  (* Eval compute in (natcoll 0). *)
  (* Eval compute in {| dstring "John"; dstring "Jane" |}. *)
  (* Eval compute in {| dbool true; dbool false |}. *)


  (**************
   * Input data *
   **************)

  (* Numbers from one to ten *)

  Definition one_to_ten := (natcoll 10).

  (* Input derivation inheritance *)

  Definition h := (@nil (string*string)).
  
  (* Person table *)

  Definition mkperson (name:string) (age:Z) (zip:Z) (company:string) (position:string) :=
    [| ("name", dstring name);
       ("age", dnat age);
       ("zip", dnat zip);
       ("company", dstring company);
       ("position", dstring position) |].

  Definition mkpersons_aux l :=
    map (fun x =>
           match x with (name, age, zip, company, position) => mkperson name age zip company position
           end) l.

  Definition p1 := mkperson "John" 23 1008 "IBM" "CEO".
  Definition p2 := mkperson "Jane" 24 1009 "AIG" "CFO".

  Definition mkpersons l :=
    dcoll (mkpersons_aux l).

  Definition persons :=
    mkpersons
      (("John",30,1008,"IBM", "CEO")
         :: ("Jane",12,1009,"AIG", "CFO")
         :: ("Joan",30,1008,"AIG", "CEO")
         :: ("Jade",30,1008,"AIG", "VP Sales")
         :: ("Jacques",30,1008,"AIG", "VP Compliance")
         :: ("Jill",25,1010,"IBM", "CFO")
         :: ("Joo",24,1010,"IBM", "VP Engineering")
         :: ("Just",12,1010,"IBM", "VP M&A")
         :: ("Jack",56,1010,"Apricot", "CEO")
         :: ("Jerome",56,1010,"Apricot", "Dean")
         :: nil).
  
  (* Eval compute in persons. *)

  (* Company table *)

  Definition companies : data :=
    {| [|("cname", dstring "IBM"); ("stock", dnat 200); ("ticker", dstring "IBM") |];
       [|("cname", dstring "AIG"); ("stock", dnat 20);  ("ticker", dstring "AIG") |];
       [|("cname", dstring "AMD"); ("stock", dnat 25);  ("ticker", dstring "AMD") |];
       [|("cname", dstring "Apricot"); ("stock", dnat 135);  ("ticker", dstring "APR") |] |}.

  (* Eval compute in companies. *)

  (* The whole input *)

  Definition tables : list (string*data) :=
    (("persons",persons) :: ("companies",companies) :: nil).

  (***********
   * Queries *
   ***********)

  Definition sql_just_query_to_nraenv (q:sql_query)
    := sql_to_nraenv_top (SRunQuery q::nil).

  Definition sql_just_query_eval (q:sql_query)
    := @eval_nraenv _ nil (sql_to_nraenv_top (SRunQuery q::nil)).

  (* sql1:
       select name
       from persons *)
  Definition sql1 :=
    SQuery (SSelectColumn "name"::nil) (SFromTable "persons"::nil) None None None.
  Definition nraenv1 :=
    sql_just_query_to_nraenv sql1.

  Definition sql1_vars := sql_query_free_variables sql1.
  
  (* Eval vm_compute in nraenv1. *)
  (* Eval vm_compute in (sql_just_query_eval  sql1 tables). *)
  (* Eval vm_compute in sql1_vars. *)
  
  (* sql2:
       select name,
              age
       from persons
       order by age *)
  Definition sql2 :=
    SQuery (SSelectColumn "name"::SSelectColumn "age"::nil)
           (SFromTable "persons"::nil) None None (Some (("age",Ascending)::nil)).

  Definition sql2_vars := sql_query_free_variables sql2.
  
  (* Eval vm_compute in (sql_just_query_eval  sql2 tables). *)
  (* Eval vm_compute in sql2_vars. *)
  
  (* sql3:
       select name
       from persons
       order by age *)
  Definition sql3 :=
    SQuery (SSelectColumn "name"::nil)
           (SFromTable "persons"::nil) None None (Some (("age",Ascending)::nil)).

  Definition sql3_vars := sql_query_free_variables sql3.
  
  (* Eval vm_compute in (sql_just_query_eval  sql3 tables). *)
  (* Eval vm_compute in sql3_vars. *)

  (* sql4:
       select name
       from persons
       where company = 'IBM'
       order by age *)
  Definition sql4 :=
    SQuery (SSelectColumn "name"::nil)
           (SFromTable "persons"::nil)
           (Some (SCondBinary SEq (SExprColumn "company")
                              (SExprConst (dstring "IBM"))))
           None (Some (("age",Ascending)::nil)).

  Definition sql4_vars := sql_query_free_variables sql4.
  
  (* Eval vm_compute in (sql_just_query_eval  sql4 tables). *)
  (* Eval vm_compute in sql4_vars. *)
  
  (* sql5:
       select sum(age)
       from persons *)
  Definition sql5 :=
    [SRunQuery (SQuery (SSelectExpr ""
                        (SExprAggExpr SSum (SExprColumn "age"))::nil)
           (SFromTable "persons"::nil) None None None)].

  Definition sql5_vars := sql_free_vars sql5.
  
  (* Eval vm_compute in (sql_just_query_eval  sql5 tables). *)
  (* Eval vm_compute in sql5_vars. *)

  (* sql6:
       select count( * )
       from persons *)
  Definition sql6 :=
    SQuery (SSelectExpr ""
                        (SExprAggExpr SCount SExprStar)::nil)
           (SFromTable "persons"::nil) None None None.

  Definition sql6_vars := sql_query_free_variables sql6.
  
  (* Eval vm_compute in (sql_just_query_eval  sql6 tables). *)
  (* Eval vm_compute in sql6_vars. *)

  (* sql7:
       select count( * )
         from
            ( select name
              from persons
              where company = 'IBM'
              order by age ) as IBMers
   *)
  Definition sql7 :=
    SQuery (SSelectExpr ""
                        (SExprAggExpr SCount SExprStar)::nil)
           (SFromQuery ("IBMers",None) sql4 :: nil) None None None.

  Definition sql7_vars := sql_query_free_variables sql7.
  
  (* Eval vm_compute in (sql_just_query_eval  sql7 tables). *)
  (* Eval vm_compute in sql7_vars. *)

  (* sql8:
       select *
       from persons
       group by age *)
  Definition sql8 :=
    SQuery (SSelectExpr "res" SExprStar::nil)
           (SFromTable "persons"::nil) None (Some (("age"::nil),None)) None.

  Definition sql8_vars := sql_query_free_variables sql8.
  
  (* Eval vm_compute in (sql_just_query_eval  sql8 tables). *)
  (* Eval vm_compute in sql8_vars. *)
  
  (* sql9:
       select age, count( * ) as nb
       from persons
       group by age *)
  Definition sql9 :=
    SQuery (SSelectColumn "age" :: SSelectExpr "nb"
                          (SExprAggExpr SCount SExprStar)::nil)
           (SFromTable "persons"::nil) None (Some (("age"::nil),None)) None.

  Definition sql9_vars := sql_query_free_variables sql9.
  
  (* Eval vm_compute in (sql_just_query_eval  sql9 tables). *)
  (* Eval vm_compute in sql9_vars. *)
  
  (* sql10:
       select age, count( * ) as nb
       from persons
       group by age
       order by age *)
  Definition sql10 :=
    SQuery (SSelectColumn "age" :: SSelectExpr "nb"
                          (SExprAggExpr SCount SExprStar)::nil)
           (SFromTable "persons"::nil) None
           (Some (("age"::nil),None)) (Some (("age",Ascending)::nil)).

  Definition sql10_vars := sql_query_free_variables sql10.
  
  (* Eval vm_compute in (sql_just_query_eval  sql10 tables). *)
  (* Eval vm_compute in sql10_vars. *)

  (* sql11:
       select age, count( * ) as nb
       from persons
       group by age
       having count( * ) > 1
       order by age
   *)
  Definition sql11 :=
    SQuery (SSelectColumn "age" :: SSelectExpr "nb"
                          (SExprAggExpr SCount SExprStar)::nil)
           (SFromTable "persons"::nil)
           None (Some (("age"::nil),
                       Some (SCondBinary SGt (SExprAggExpr SCount SExprStar)
                                         (SExprConst (dnat 1)))))
           (Some (("age",Ascending)::nil)).

  Definition sql11_vars := sql_query_free_variables sql11.
  
  (* Eval vm_compute in (sql_just_query_eval  sql11 tables). *)
  (* Eval vm_compute in sql11_vars. *)

  (* sql12:
       select age, company, count( * ) as nb
       from persons
       group by age, company
       // order by age  -- BUG IN ORDERBY REMOVING DUPLICATES
   *)
  Definition sql12 :=
    SQuery (SSelectColumn "age" :: SSelectColumn "company" :: SSelectExpr "nb"
                          (SExprAggExpr SCount SExprStar)::nil)
           (SFromTable "persons"::nil)
           None
           (Some (("age"::"company"::nil),None)) None.

  Definition sql12_vars := sql_query_free_variables sql12.
  
  (* Eval vm_compute in (sql_just_query_eval  sql12 tables). *)
  (* Eval vm_compute in sql12_vars. *)

  (* sql13:
       select name
       from persons
       where company = 'IBM'
       order by age *)
  Definition sql13 :=
    SQuery (SSelectColumn "name"::SSelectColumn "age"::nil)
           (SFromTable "persons"::nil)
           (Some (SCondBinary SEq (SExprColumn "company")
                              (SExprConst (dstring "IBM"))))
           None (Some (("age",Ascending)::nil)).

  Definition sql13_vars := sql_query_free_variables sql13.
  
  (* Eval vm_compute in (sql_just_query_eval  sql13 tables). *)
  (* Eval vm_compute in sql13_vars. *)

  (* sql14:
         select nom
           from
              ( select name,age
                from persons
                where company = 'IBM'
                order by age ) as (nom,age)
   *)
  Definition sql14 :=
    SQuery (SSelectColumn "nom"::nil)
           (SFromQuery ("IBMers",Some ("nom"::"age"::nil)) sql13 :: nil)
           None None None.

  Definition sql14_vars := sql_query_free_variables sql14.
  
  (* Eval vm_compute in (sql_just_query_eval  sql14 tables).  *)
  (* Eval vm_compute in sql14_vars. *)

  (* sql15:
       select cname, stock, count( * ) as nb_employees
       from persons, companies
       where cname = company
       group by cname, stock
       having stock > 50
       order by stock *)
  Definition sql15 :=
    SQuery ((SSelectColumn "cname")
              :: (SSelectColumn "stock")
              :: SSelectExpr "nb_employees" (SExprAggExpr SCount SExprStar)::nil)  (* Select Clause *)
           (SFromTable "persons"::SFromTable "companies"::nil)                     (* From Clause *)
           (Some (SCondBinary SEq (SExprColumn "cname") (SExprColumn "company")))  (* Where Clause *)
           (Some (("cname"::"stock"::nil),                                         (* Group By Clause *)
                  Some (SCondBinary SGt                                            (* Having Clause *)
                                    (SExprColumn "stock")
                                    (SExprConst (dnat 50)))))
           (Some (("stock"%string,Ascending)::nil)).                               (* Order By Clause *)

  Definition sql15_vars := sql_query_free_variables sql15.
  
  (* Eval vm_compute in (sql_just_query_eval  sql15 tables). *)
  (* Size of the plan: *)
  (* Eval vm_compute in (sql_size sql15).*)
  (* Eval vm_compute in sql15_vars. *)

  (* sql16:
       select name, company
       from persons
       where company in (
          select cname
          from companies
          where stock > 50
       ) *)

  Definition sql16 :=
    SQuery ((SSelectColumn "name")
              :: (SSelectColumn "company")
              ::nil)
           (SFromTable "persons"::nil)
           (Some (SCondIn (SExprColumn "company")
                          (SExprQuery
                             (SQuery ((SSelectColumn "cname")::nil)
                                     (SFromTable "companies"::nil)
                                     (Some (SCondBinary SGt
                                                        (SExprColumn "stock")
                                                        (SExprConst (dnat 50))))
                                     None None))))
           None
           None.

  Definition sql16_vars := sql_query_free_variables sql16.
  
  (* Eval vm_compute in (sql_just_query_eval  sql16 tables). *)
  (* Eval vm_compute in sql16_vars. *)

  (* sql17:
       select p1.age,
              p1.company,
              p1.name as emp1,
              p2.name as emp2
       from persons p1, persons p2
       where p1.age = p2.age
         and p1.company = p2.company
         and p1.name <> p2.name *)
  Definition sql17 :=
    [SRunQuery
       (SQuery ((SSelectColumnDeref "p1" "age")
                  :: (SSelectColumnDeref "p1" "company")
                  :: (SSelectExpr "emp1" (SExprColumnDeref "p1" "name"))
                  :: (SSelectExpr "emp2" (SExprColumnDeref "p2" "name"))
                  :: nil)
               (SFromTableAlias "p1" "persons"::SFromTableAlias "p2" "persons"::nil)
               (Some (SCondAnd
                        (SCondAnd
                           (SCondBinary SEq (SExprColumnDeref "p1" "age")
                                        (SExprColumnDeref "p2" "age"))
                           (SCondBinary SEq (SExprColumnDeref "p1" "company")
                                        (SExprColumnDeref "p2" "company")))
                        (SCondBinary SDiff (SExprColumnDeref "p1" "name")
                                     (SExprColumnDeref "p2" "name"))))
               None
               None)].

  Definition sql17_vars := sql_free_vars sql17.
  
  (* Eval vm_compute in (sql_just_query_eval  sql17 tables). *)
  (* Eval vm_compute in sql17_vars. *)

End SQLTest.

