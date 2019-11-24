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

Delimit Scope data_scope with data.

Notation "⊥" := (dunit) : data_scope. (* null value *)

Notation "[||]" := (drec nil) : data_scope. (* records *)
Notation "[| x1 ; .. ; xn |]" := (drec (cons x1 .. (cons xn nil) ..)) : data_scope.

Notation "{||}" := (dcoll nil) : data_scope. (* collections *)
Notation "{| x1 ; .. ; xn |}" := (dcoll (cons x1 .. (cons xn nil) ..)) : data_scope.

Require Import String.
Require Import ZArith.
Require Import OQL.
Require Import OQLSugar.
Require Import TrivialModel.

Section OQLTest.
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
  
  (* Employee table *)

  Definition mkemployee (name:string) (age:Z) (zip:Z) (company:string) :=
    dbrand ("Employee"::nil)
           [| ("name", dstring name);
              ("age", dnat age);
              ("zip", dnat zip);
              ("company", dstring company) |].

  Definition mkemployees_aux l :=
    map (fun x =>
           match x with (name, age, zip, company) => mkemployee name age zip company
           end) l.

  Definition p1 := mkemployee "John" 23 1008 "IBM".
  Definition p2 := mkemployee "Jane" 24 1009 "AIG".

  Definition myc x1 x2 :=
  match x1,x2 with
    | drec d1, drec d2 => Some (rec_concat_sort d1 d2)
    | _,_ => None
  end.

  (* Eval compute in (myc p1 p2). *)

  Definition mkemployees l :=
    dcoll (mkemployees_aux l).

  Definition employees :=
    mkemployees
      (("John",23,1008,"IBM")
         :: ("Jane",24,1009,"AIG")
         :: ("Jill",25,1010,"IBM")
         :: ("Jack",27,1010,"CMU")
         :: nil).
  
  (* Eval compute in employees. *)

  (* Company table *)

  Definition companies : data :=
    {| dbrand ("Company"::nil) [|("cname", dstring "IBM"); ("stock", dnat 200); ("ticker", dstring "IBM");
                                 ("departments", dcoll ((dstring "Cloud") :: (dstring "Cognitive") :: nil)) |];
       dbrand ("Company"::nil) [|("cname", dstring "AIG"); ("stock", dnat 20);  ("ticker", dstring "AIG");
                                 ("departments", dcoll ((dstring "Insurance") :: (dstring "Derivatives") :: nil)) |];
       dbrand ("Company"::nil) [|("cname", dstring "AMD"); ("stock", dnat 25);  ("ticker", dstring "AMD");
                                 ("departments", dcoll nil) |] |}.

  Definition CPRModel :=
    ("Company","Entity")::("Employee","Entity")::nil.

  (* Eval compute in companies. *)

  (* The whole input *)

  Definition tables : oql_env :=
    (("Employees",employees) :: ("Companies",companies) :: nil).

  Definition init_env : oql_env := nil.
  
  (***********
   * Queries *
   ***********)

  Open Scope oql_scope.
  
  (* Simple count over a table *)

  Definition q0 : oql_expr := OUnop OpCount (OTable "Companies").
  Definition q0_eval : option data := oql_expr_interp CPRModel tables q0 init_env.

(*  Eval vm_compute in q0_eval. *)

  (* Simple selection+projection over Employees *)
  
  (* select e.age
     from Employees e
     where e.name = "John" *)

  Definition q1 : oql_expr :=
    OSFW
      (OSelect (OUnop (OpDot "age") (OUnop OpUnbrand (OVar "e"))))
      ((OIn "e"  (OTable "Employees"))::nil)
      (OWhere (OBinop OpEqual (OUnop (OpDot "name") (OUnop OpUnbrand (OVar "e"))) (OConst (dstring "John"))))
      ONoOrder.
  
  Definition q1_eval : option data := oql_expr_interp CPRModel tables q1 init_env.

(*  Eval vm_compute in q1_eval. *)
  
  (* Join between Employees and Companies *)
  
  (* select struct(employee: e.name, worksfor: c.cname)
     from Employees e,
          Companies c
     where e.company = c.cname *)
  
  Definition q2 : oql_expr :=
    OSFW
      (OSelect (OBinop OpRecConcat
                       (OUnop (OpRec "employee") (OUnop (OpDot "name") (OUnop OpUnbrand (OVar "e"))))
                       (OUnop (OpRec "worksfor") (OUnop (OpDot "cname") (OUnop OpUnbrand (OVar "c"))))))
      ((OIn "e"  (OTable "Employees"))::(OIn "c" (OTable "Companies"))::nil)
      (OWhere (OBinop OpEqual
                      (OUnop (OpDot "company") (OUnop OpUnbrand (OVar "e")))
                      (OUnop (OpDot "cname") (OUnop OpUnbrand (OVar "c")))))
      ONoOrder.

  Definition q2_eval : option data := oql_expr_interp CPRModel tables q2 init_env.

(*  Eval vm_compute in q2_eval. *)

  (* Same, written with OStruct sugar *)
  
  Definition q2' : oql_expr :=
    OSFW
      (OSelect (OStruct (("employee", (OUnop (OpDot "name") (OUnop OpUnbrand (OVar "e"))))
                           :: ("worksfor", (OUnop (OpDot "cname") (OUnop OpUnbrand (OVar "c"))))
                           :: nil)))
      ((OIn "e"  (OTable "Employees"))::(OIn "c" (OTable "Companies"))::nil)
      (OWhere (OBinop OpEqual
                      (OUnop (OpDot "company") (OUnop OpUnbrand (OVar "e")))
                      (OUnop (OpDot "cname") (OUnop OpUnbrand (OVar "c")))))
      ONoOrder.

  Definition q2'_eval : option data := oql_expr_interp CPRModel tables q2' init_env.

(*  Eval vm_compute in q2'_eval. *)
(*  Eval vm_compute in q2'. *)
  
  (* select struct(company: c.cname, dept: d)
     from Companies c,
          c.departments d *)
  
  Definition q3 : oql_expr :=
    OSFW
      (OSelect (OBinop OpRecConcat
                       (OUnop (OpRec "company") (OUnop (OpDot "cname") (OUnop OpUnbrand (OVar "c"))))
                       (OUnop (OpRec "dept") (OVar "d"))))
      ((OIn "c"  (OTable "Companies"))::(OIn "d" (OUnop (OpDot "departments") (OUnop OpUnbrand (OVar "c"))))::nil)
      OTrue
      ONoOrder.

  Definition q3_eval : option data := oql_expr_interp CPRModel tables q3 init_env.

(*  Eval vm_compute in q3_eval. *)
  (* Note that AMD doesn't appear since it does not have departments *)
  (* Note that the scope of c are the following clauses and you cannot
  reverse the order in the from clause because of that. The following
  is indeed an error. *)

  (* select struct(company: c.cname, dept: d)
     from c.departments d,
          Companies c *)
  
  Definition q3wrong : oql_expr :=
    OSFW
      (OSelect (OBinop OpRecConcat
                       (OUnop (OpRec "company") (OUnop (OpDot "cname") (OUnop OpUnbrand (OVar "c"))))
                       (OUnop (OpRec "dept") (OVar "d"))))
      ((OIn "d" (OUnop (OpDot "departments") (OUnop OpUnbrand (OVar "c"))))::(OIn "c"  (OTable "Companies"))::nil)
      OTrue
      ONoOrder.

  Definition q3wrong_eval : option data := oql_expr_interp CPRModel tables q3wrong init_env.

(*  Eval vm_compute in q3wrong_eval. *)

End OQLTest.

