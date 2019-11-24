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

Require Import String ZArith.
Require Import NRARuntime.
Require Import TrivialModel.
  
Section NRATest.
  Open Scope Z_scope.

  Local Open Scope string_scope.
  Local Open Scope nraext_scope.
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

  Definition mkperson (name:string) (age:Z) (zip:Z) (company:string) :=
    [| ("name", dstring name);
       ("age", dnat age);
       ("zip", dnat zip);
       ("company", dstring company) |].

  Definition mkpersons_aux l :=
    map (fun x =>
           match x with (name, age, zip, company) => mkperson name age zip company
           end) l.

  Definition p1 := mkperson "John" 23 1008 "IBM".
  Definition p2 := mkperson "Jane" 24 1009 "AIG".

  Definition myc x1 x2 :=
  match x1,x2 with
    | drec d1, drec d2 => Some (rec_concat_sort d1 d2)
    | _,_ => None
  end.

  (* Eval compute in (myc p1 p2). *)

  Definition mkpersons l :=
    dcoll (mkpersons_aux l).

  Definition persons :=
    mkpersons
      (("John",23,1008,"IBM")
         :: ("Jane",24,1009,"AIG")
         :: ("Jill",25,1010,"IBM")
         :: ("Jack",27,1010,"CMU")
         :: nil).
  
  (* Eval compute in persons. *)

  (* Company table *)

  Definition companies : data :=
    {| [|("cname", dstring "IBM"); ("stock", dnat 200); ("ticker", dstring "IBM") |];
       [|("cname", dstring "AIG"); ("stock", dnat 20);  ("ticker", dstring "AIG") |];
       [|("cname", dstring "AMD"); ("stock", dnat 25);  ("ticker", dstring "AMD") |] |}.

  (* Eval compute in companies. *)

  (* The whole input *)

  Definition tables : data :=
    [| ("persons",persons); ("companies",companies) |].

  (* Eval compute in tables. *)

  Definition qtpersons := ID·"persons".
  (* Eval compute in qtpersons@tables. *)

  Definition qtcompanies := ID·"companies".
  (* Eval compute in qtcompanies@tables. *)

  Definition nothing : data := dunit.

  Definition qpersons := (xNRAConst (persons)).
  (* Eval compute in qpersons@nothing. *)

  Definition qcompanies := (xNRAConst (companies)).
  (* Eval compute in qcompanies@nothing. *)

  (***********
   * Queries *
   ***********)

  (* Eval compute in ID@persons. *)

  (* count *)

  Definition q0 := ♯count(ID).

  (* Eval compute in (q0@one_to_ten). *)
  
  (* simple maps *)

  Definition q0' := ‵one_to_ten⌈"n"⌋.

  (* Eval compute in (q0'@nothing). *)

  Definition q1 := χ⟨ ID ⟩(qpersons).

  (* Eval compute in q1@nothing. *)

  Definition q2 := χ⟨ ID·"age" ⟩(qpersons).

  (* Eval compute in q2@nothing. *)

  Definition q2' := χ⌈"n"⌋⟨ ID·"age" ⟩(qpersons).

  (* Eval compute in q2'@nothing. *)

  (* simple selections *)

  Definition q3 := (σ⟨ ‵‵true ⟩(qpersons)).

  (* Eval compute in q3@nothing. *)

  Definition q4 := (σ⟨ ID·"age" ≐ ‵‵23 ⟩(qpersons)).

  (* Eval compute in q4@nothing. *)

  (* simple cartesian product *)
 
  Definition q5 := (qpersons × qcompanies).

  (* Eval compute in q5@nothing. *)

  (* simple join *)

  (* Eval compute in qcompanies. *)

  Definition q6 := σ⟨ ID·"company" ≐ ID·"cname" ⟩(qpersons × qcompanies).
  
  (* Eval compute in q6@nothing. *)

  Definition q6' := ⋈⟨ ID·"company" ≐ ID·"cname" ⟩(qpersons, qcompanies).

  (* Eval compute in q6'@nothing. *)

  (* semi join *)

  Definition q61 := ⋉⟨ ID·"company" ≐ ID·"cname" ⟩(qpersons, qcompanies).

  (* Eval compute in q61@nothing. *)

  (* anti join *)

  Definition q62 := ▷⟨ ID·"company" ≐ ID·"cname" ⟩(qpersons, qcompanies).

  (* Eval compute in q62@nothing. *)

  (* simple group-by, employees per company (or counts them) *)

  Definition q7 := ⋈ᵈ⟨ ‵{|‵[| ("emps", σ⟨ ID·"company" ≐ ID·"cname" ⟩(qpersons × ‵{|ID|})) |]|} ⟩( qcompanies ).

  (* Eval compute in q7@nothing. *)

  Definition q8 := ⋈ᵈ⟨ ‵{|‵[| ("emp_count",♯count(σ⟨ ID·"company" ≐ ID·"cname" ⟩(qpersons × ‵{|ID|}))) |]|} ⟩( qcompanies ).

  (* Eval compute in q8@nothing. *)

  (* Projection *)

  Definition q9 := Π[](qpersons).

  (* Eval compute in q9@nothing. *)

  Definition q10 := Π["name"](qpersons).

  (* Eval compute in q10@nothing. *)

  Definition q11 := Π["name","company"](qpersons).

  (* Eval compute in q11@nothing. *)
 
  Definition q12 := Π["name","company","cname"](q6').

  (* Eval compute in q12@nothing. *)

  Definition q13 := Π["name","company","cname","stock"](q6').

  (* Eval compute in q13@nothing. *)

  (* Out-Projection *)

  Definition q14 := ¬Π["name"](q6').

  (* Eval compute in q14@nothing. *)

  (* Renaming *)

  Definition q15 := ρ[ "name" ↦ "nom" ](q6').

  (* Eval compute in q15@nothing. *)

  (* Unnest *)

  Definition q16 := μ["emps"](q7).

  (* Eval compute in q16@nothing. *)

  Definition q7' := Π["cname","zips"](χ⌈"zips"⌋⟨χ⟨ ID·"zip" ⟩(ID·"emps")⟩(q7)).

  (* Eval compute in q7'@nothing. *)

  Definition q17 := μ["zips"]["zip"](q7').

  (* Eval compute in q17@nothing. *)

  (* Grouping *)

  (* Eval compute in q6'@nothing. *)

  Definition q18 := Γ["g"]["cname"](q6').

  (* Eval compute in q18@nothing. *)

  (* Eval compute in (h ⊢ qpersons @ₓ dunit). *)

End NRATest.

