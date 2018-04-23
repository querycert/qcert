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

(** * Examples manually translated from arl (JRules) *)

Require Import ZArith.
Require Import String.
Require Import List.
Require Import Utils.
Require Import CommonSystem.
Require Import CAMPRuntime.
Require Import CAMPRuleRuntime.
Require Import TrivialModel.
Require Import CompEnv.
  
Local Open Scope Z_scope.
Local Open Scope string.
Import ListNotations.

(* This module encodes the examples in sample-rules.txt *)
Section CAMPTest.
  Local Open Scope camp_scope.
  
  (* This was copy/pastes from sample-rules (with [] added in at the top level *)
  Example exampleWM : list data 
    := [ dbrand (singleton "Customer") (drec [("cid",dnat 123); ("name",dstring "John Doe"); ("age",dnat 32)]);
         dbrand (singleton "Customer") (drec [("cid",dnat 124); ("name",dstring "Jane Doe"); ("age",dnat 32)]);
         dbrand (singleton "Customer") (drec [("cid",dnat 125); ("name",dstring "Jim Does"); ("age",dnat 34)]);
         dbrand (singleton "Customer") (drec [("cid",dnat 126); ("name",dstring "Jill Does"); ("age",dnat 32)]);
         dbrand (singleton "Customer") (drec [("cid",dnat 127); ("name",dstring "Joan Doe"); ("age",dnat 34)]);
         dbrand (singleton "Customer") (drec [("cid",dnat 128); ("name",dstring "James Do"); ("age",dnat 35)]);
         dbrand (singleton "Purchase") (drec [("pid",dnat 1); ("cid",dnat 123); ("name",dstring "Tomatoe"); ("quantity",dnat 3)]);
         dbrand (singleton "Purchase") (drec [("pid",dnat 2); ("cid",dnat 123); ("name",dstring "Potatoe"); ("quantity",dnat 1)]);
         dbrand (singleton "Purchase") (drec [("pid",dnat 3); ("cid",dnat 125); ("name",dstring "Stiletto"); ("quantity",dnat 64)]);
         dbrand (singleton "Purchase") (drec [("pid",dnat 4); ("cid",dnat 126); ("name",dstring "Libretto"); ("quantity",dnat 62)]);
         dbrand (singleton "Purchase") (drec [("pid",dnat 5); ("cid",dnat 128); ("name",dstring "Dough"); ("quantity",dnat 4)]);
         dbrand (singleton "Purchase") (drec [("pid",dnat 6); ("cid",dnat 128); ("name",dstring "Croissant"); ("quantity",dnat 2)]) ].

  (* R1: customers with age 32 *)
  (*
      rule R1 {
               when {
               c:Customer(age == 32);
               }
               then {
                 System.out.println("Customer =" + c);
               }
             }
   *)

  Definition CPRModel :=
    ("Customer","Entity")::("Purchase","Entity")::nil.

  Definition CPRModel_relation : brand_relation
    := mkBrand_relation CPRModel (eq_refl _) (eq_refl _).
  
  Example R1 := 
        rule_when ("c" INSTANCEOF (singleton "Customer") WHERE ("age" !#-> #_ ≐ ‵32))
     ;; rule_return (‵"Customer =" +s+ withVar "c" ("name" !#-> #_)).

  Example R1_result := eval_camp_rule CPRModel R1 exampleWM.

  Example R1_expected :=
    map dconst
        ["Customer =Jill Does";
          "Customer =Jane Doe";
          "Customer =John Doe"].

  (* Eval vm_compute in R1_result. *)
  Example R1_verify : validate_success R1_result R1_expected = true.
  Proof. fast_refl. Qed.

  (* R2: Pairs of customers with the same age *)

  (*
      rule R2 {
              when {
              c1:Customer();
              c2:Customer(age == c1.age);
              }
              then {
                System.out.println("Customer: " + c1 + " and: " + c2 + " have the same age: " + c1.age);
              }
            }
 *)

  Example R2 := 
       rule_when ("c1" INSTANCEOF (singleton "Customer") 
                     WHERE paccept)
    ;; rule_when ("c2" INSTANCEOF (singleton "Customer") 
                      WHERE ("age"!#-> #_ #= withVar "c1" ("age" !#-> …)))
    ;;  rule_return (‵"Customer: " +s+ withVar "c1" ("name" !#-> …)
                 +s+ #`" and: "
                 +s+ withVar "c2" ("name" !#-> …)
                 +s+ ‵" have the same age: "
                 +s+ withVar "c1" (toString ("age" !#-> …))
       ).

  Example R2_result := eval_camp_rule CPRModel R2 exampleWM.
  Example R2_expected := map dconst 
    ["Customer: James Do and: James Do have the same age: 35";
     "Customer: Jim Does and: Joan Doe have the same age: 34";
     "Customer: Joan Doe and: Joan Doe have the same age: 34";
     "Customer: Joan Doe and: Jim Does have the same age: 34";
     "Customer: John Doe and: Jill Does have the same age: 32";
     "Customer: Jane Doe and: Jill Does have the same age: 32";
     "Customer: Jill Does and: Jill Does have the same age: 32";
     "Customer: Jill Does and: John Doe have the same age: 32";
     "Customer: Jill Does and: Jane Doe have the same age: 32";
     "Customer: Jim Does and: Jim Does have the same age: 34";
     "Customer: John Doe and: Jane Doe have the same age: 32";
     "Customer: Jane Doe and: Jane Doe have the same age: 32";
     "Customer: Jane Doe and: John Doe have the same age: 32";
     "Customer: John Doe and: John Doe have the same age: 32"].

  Example R2_verify : validate_success R2_result R2_expected = true.
  Proof. fast_refl. Qed.

(* R3: Customers with their purchases *)

(*    rule R3 {
        when {
          c:Customer();
          p:Purchase(getCId() == c.id);
        }
        then {
          System.out.println("Customer: " + c + " made purchase:" + p );  
        }
      }
*)

  Example R3 := 
       rule_when ("c" INSTANCEOF (singleton "Customer") 
                    WHERE paccept)
    ;; rule_when ("p" INSTANCEOF (singleton "Purchase") 
                     WHERE ("cid" !#-> … ≐ withBrandedVar "c" ("cid"↓…)))
    ;;  rule_return (‵"Customer: " +s+ withBrandedVar "c" ("name"↓…)
                 +s+ ‵" made purchase:"
                 +s+ withBrandedVar "p" ("name"↓…)).

  Example R3_result := eval_camp_rule CPRModel R3 exampleWM.

  Example R3_expected := map dconst
    ["Customer: James Do made purchase:Croissant";
     "Customer: James Do made purchase:Dough";
     "Customer: Jill Does made purchase:Libretto";
     "Customer: Jim Does made purchase:Stiletto";
     "Customer: John Doe made purchase:Potatoe";
     "Customer: John Doe made purchase:Tomatoe"].

  Example R3_verify : validate_success R3_result R3_expected = true.
  Proof. fast_refl. Qed.

(* R4: Customers that didn't make a purchase *)
(* (Note: variable p is not in scope in the then clause).

    rule R4 {
        when {
          c:Customer();
          not p:Purchase(getCId() == c.id);
        }
        then {
          System.out.println("Customer: " + c + " didn't make a purchase");  
        }
      }
*)
  
  Example R4 :=  
      rule_when ("c" INSTANCEOF (singleton "Customer") 
                    WHERE paccept)
    ;; rule_not ("p" INSTANCEOF (singleton "Purchase") 
                    WHERE ("cid" !#-> … ≐ withBrandedVar "c" ("cid"↓…)))
    ;; rule_return (‵"Customer: " +s+ withBrandedVar "c" ("name"↓…)
                 +s+ ‵" didn't make a purchase").
      
  Example R4_result := eval_camp_rule CPRModel R4 exampleWM.

  Example R4_expected := map dconst
    ["Customer: Joan Doe didn't make a purchase";
     "Customer: Jane Doe didn't make a purchase"].

  Example R4_verify : validate_success R4_result R4_expected = true.
  Proof. fast_refl. Qed.

  
(* R5: Aggregate, counts customers with age 32 *)

   (*
    rule R5 {
        when {
          cs: aggregate {
            c:Customer( age == 32 );
          }
          do { count {c.name}; }
        }
        then {
          System.out.println("Customers with age 32: " + cs);  
        }
      }

 *)

  Example R5 := 
        rule_global
       ("cs" IS AGGREGATE
             (rule_when ("c" INSTANCEOF (singleton "Customer") WHERE ("age" !#-> … ≐ ‵32)))
             DO OpCount
             OVER (withBrandedVar "c" ("name"↓…))
       FLATTEN 0)
      ;; rule_return (‵"Customers with age 32: "
                 +s+ toString (lookup "cs")).

  Example R5_result := eval_camp_rule CPRModel R5 exampleWM.
  Example R5_expected := map dconst
                             ["Customers with age 32: 3"].

  Example R5_verify : validate_success R5_result R5_expected = true.
  Proof. fast_refl. Qed.

  (* R6: Count purchases made by John Doe *)

  (*
    rule R6 {
        when {
          ps: aggregate {
            c:Customer( name == "John Doe" );
            p:Purchase( getCId() == c.id );
          }
          do { count {p}; }
        }
        then {
          System.out.println("Nb of John Doe's purchases: " + ps);  
        }
      }

   *)
  
  Example R6 := 
    rule_global 
       ("ps" IS AGGREGATE
             (rule_when ("c" INSTANCEOF (singleton "Customer") 
                             WHERE ("name" !#-> … ≐ ‵"John Doe"))
              ;;; rule_when ("p" INSTANCEOF (singleton "Purchase") 
                              WHERE  ("cid" !#-> … ≐ withBrandedVar "c" ("cid"↓…))))
             DO OpCount
             OVER (withBrandedVar "p" ("name"↓…))
             FLATTEN 0)
     ;; rule_return (‵"Nb of John Doe's purchases: " +s+ 
                 (toString (lookup "ps"))).


  Example R6_result := eval_camp_rule CPRModel R6 exampleWM.

  Example R6_expected := map dconst
    ["Nb of John Doe's purchases: 2"].

  Example R6_verify : validate_success R6_result R6_expected = true.
  Proof. fast_refl. Qed.

  Example R7 := 
       rule_when ("c" INSTANCEOF (singleton "Customer") WHERE paccept)
    ;; rule_global
        ("cs" IS AGGREGATE
              (rule_when ("c2" INSTANCEOF (singleton "Customer") WHERE ("age" !#-> … ≐ (withBrandedVar "c" ("age"↓…)))))
              DO OpCount
              OVER (lookup "c2")
              FLATTEN 0)
     ;; rule_return (‵"Customer: "  +s+ (withBrandedVar "c" ("name"↓…)) 
                 +s+ ‵" has the same age ("
                 +s+ toString (withBrandedVar "c" ("age"↓…))
                 +s+ ‵") as "
                 +s+ toString (lookup "cs")
                 +s+ ‵" other Customers").

  Example R7_result := eval_camp_rule CPRModel R7 exampleWM.

  Example R7_expected := map dconst
    ["Customer: James Do has the same age (35) as 1 other Customers";
     "Customer: Joan Doe has the same age (34) as 2 other Customers";
     "Customer: Jill Does has the same age (32) as 3 other Customers";
     "Customer: Jim Does has the same age (34) as 2 other Customers";
     "Customer: Jane Doe has the same age (32) as 3 other Customers";
     "Customer: John Doe has the same age (32) as 3 other Customers"].

  Example R7_verify : validate_success R7_result R7_expected = true.
  Proof. fast_refl. Qed.

  Example R8 := 
       rule_when ("c" INSTANCEOF (singleton "Customer") WHERE paccept)
    ;; rule_global
        ("cs" IS AGGREGATE
              (rule_when ("c2" INSTANCEOF (singleton "Customer") WHERE ("age" !#-> … ≐ (withBrandedVar "c" ("age"↓…)))))
              DO OpCount
              OVER (withVar "c2" …)
              FLATTEN 0)
      ;; rule_not ((lookup "cs") ≐ ‵1)
      ;; rule_return (‵"Customer: "  +s+ (withBrandedVar "c" ("name"↓…)) 
                 +s+ ‵" has the same age ("
                 +s+ toString (withBrandedVar "c" ("age"↓…))
                 +s+ ‵") as "
                 +s+ toString (lookup "cs")
                 +s+ ‵" other Customers").

  Example R8_result := eval_camp_rule CPRModel R8 exampleWM.

  Example R8_expected := map dconst
    ["Customer: Jim Does has the same age (34) as 2 other Customers";
     "Customer: Joan Doe has the same age (34) as 2 other Customers";
     "Customer: Jill Does has the same age (32) as 3 other Customers";
     "Customer: John Doe has the same age (32) as 3 other Customers";
     "Customer: Jane Doe has the same age (32) as 3 other Customers"].

  Example R8_verify : validate_success R8_result R8_expected = true.
  Proof. fast_refl. Qed.

  (* R9: Group purchases per customer *)

  (*
  rule R9 {
        when {
          c:Customer();
          pu: aggregate {
            p:Purchase(getCId() == c.id);
          }
          do { ArrayList<String> { p.product }; }
        }
        then {
          System.out.println("Customer : " + c + " purchased: " + pu);
        }
      }
  *)

  Example R9 := 
       rule_when ("c" INSTANCEOF (singleton "Customer") WHERE paccept)
    ;; rule_global
        ("pu" IS AGGREGATE
              (rule_when ("p" INSTANCEOF (singleton "Purchase") 
                              WHERE ("cid" !#-> … ≐ withBrandedVar "c" ("cid"↓…))))
              DO OpIdentity
              OVER (withBrandedVar "p" ("name"↓…))
              FLATTEN 0)
      ;; rule_return (‵"Customer : "  +s+ (withBrandedVar "c" ("name"↓…)) 
                 +s+ ‵" purchased: "
                 +s+ toString (lookup "pu")).

  Example R9_result := eval_camp_rule CPRModel R9 exampleWM.

  Example R9_expected := map dconst
    ["Customer : James Do purchased: [Croissant, Dough]";
     "Customer : Joan Doe purchased: []";
     "Customer : Jill Does purchased: [Libretto]";
     "Customer : Jim Does purchased: [Stiletto]";
     "Customer : Jane Doe purchased: []";
     "Customer : John Doe purchased: [Potatoe, Tomatoe]"].

  Example R9_verify : validate_success R9_result R9_expected = true.
  Proof. fast_refl. Qed.
  
 (* R10: From the result of R9, compute the total number of purchases for
all customers. *)

  (*
    rule R10 {
        when {
          total:aggregate {
            c:Customer();
            pu: aggregate {
              p:Purchase(getCId() == c.id);
            }
            do { ArrayList<String> { p.product }; }
          }
          do { count { pu }; }
        }
        then {
          System.out.println("Total purchases are : " + total);
        }
      }
  *)

  Example R10 :=
      rule_global
        ("total" IS AGGREGATE
                 (   rule_when ("c" INSTANCEOF (singleton "Customer") WHERE paccept)
                  ;;; rule_global ("pu" IS AGGREGATE 
                                     (rule_when ("p" INSTANCEOF (singleton "Purchase") 
                              WHERE ("cid" !#-> … ≐ withBrandedVar "c" ("cid"↓…))))
                                     DO OpIdentity
                                     OVER (withBrandedVar "p" ("name"↓…))
                                     FLATTEN 0))
         DO OpCount
         OVER (withVar "pu" …)
         FLATTEN 0)
      ;; rule_return (‵"Total purchases are : " 
                 +s+ toString (lookup "total")).

  Example R10_result := eval_camp_rule CPRModel R10 exampleWM.

  Example R10_expected := map dconst
    [ "Total purchases are : 6"].

  Example R10_verify : validate_success R10_result R10_expected = true.
  Proof. fast_refl. Qed.

  (* R11: Compute the average nb of purchases for customers below 34. *)

  (*
    rule R11 {
        when {
          avg:aggregate {
            c:Customer(age <= 34);
            pu: aggregate {
              p:Purchase(getCId() == c.id);
            }
            do { count { p }; }
          }
          do { mean { new Double(pu) }; }
        }
        then {
          System.out.println("Average nb purchases for customers below 34 is : " + avg);
        }
      }
  *)

  Example R11 :=
       rule_global
        ("total" IS AGGREGATE
                 (   rule_when ("c" INSTANCEOF (singleton "Customer") 
                                 WHERE (passert 
                                          (pbinop OpLe ("age"↓…) ‵34))) 
                  ;;; rule_global ("pu" IS AGGREGATE 
                                     (rule_when ("p" INSTANCEOF (singleton "Purchase") 
                              WHERE ("cid" !#-> … ≐ withBrandedVar "c" ("cid"↓…))))
                                     DO OpCount
                                     OVER (withBrandedVar "p" …)
                                     FLATTEN 0))
         DO OpIdentity
         OVER (withVar "pu" …)
         FLATTEN 0)
      ;; rule_return (‵"Average nb purchases for customers below 34 is : " 
                 +s+ toString (punop OpNatSum (lookup "total"))
                 +s+ ‵" / " 
                 +s+ toString (punop OpCount (lookup "total")))
                .


  Example R11_result := eval_camp_rule CPRModel R11 exampleWM.
(*  Eval vm_compute in R11_result. *)

  Example R11_expected := map dconst
    [ "Average nb purchases for customers below 34 is : 0.8 "].

(*  Example R11_verify : validate_success R11_result R11_expected = true.
  Proof. fast_refl. Qed.
*)

End CAMPTest.

