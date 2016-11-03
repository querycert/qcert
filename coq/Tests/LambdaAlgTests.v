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

Require Import String.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.

Require Import Utils BasicRuntime.

Require Import LambdaAlg LambdaAlgEq LambdaAlgtoNRAEnv.
Require Import TrivialCompiler.
Import TrivialCompiler.

(* Examples from [CZ96] Figure 2. 'as is' *)
Section LambdaNRATests.

  (* Prep *)
  Definition h : brand_relation_t := nil.
  
  Definition db1 :=
    (dcoll ((drec (("addr",(drec (("city", dstring "NYC")::nil)))::nil))::nil))%string.

  Definition child1 :=
    (dcoll ((drec (("name",dstring "Jane")::("age",dnat 2)::nil))
              :: (drec (("name",dstring "Joan")::("age",dnat 99)::nil))
              :: nil))%string.
  
  Definition child2 :=
    (dcoll ((drec (("name",dstring "Jules")::("age",dnat 24)::nil))
              :: (drec (("name",dstring "Jim")::("age",dnat 26)::nil))
              :: nil))%string.
  
  Definition db2 :=
    (dcoll ((drec (("name",dstring "John")::("age",dnat 24)::("child",child1)::nil))
              :: (drec (("name",dstring "Jack")::("age",dnat 40)::("child",child2)::nil))
              :: nil))%string.

  (* T1 : map(λ(a) a.city)(map(λ(p) p.addr)(P)) == map(λ(p) p.addr.city)(P) *)
  (** The original version of T1 *)
  Definition T1l P :=
    LAMap (LALambda "a" (LAUnop (ADot "city") (LAVar "a")))
          (LAMap (LALambda "p" (LAUnop (ADot "addr") (LAVar "p"))) P).

  (** The simplified version of T1 *)
  Definition T1r P :=
    LAMap (LALambda "p" (LAUnop (ADot "city") (LAUnop (ADot "addr") (LAVar "p")))) P.


  Lemma T1lr_equiv P : lalg_eq (T1l P) (T1r P).
  Proof.
    unfold lalg_eq, T1l, T1r.
    intros.
    autorewrite with lalg.
    simpl.
    unfold olift.
    destruct (fun_of_lalg h0 cenv env P); trivial.
    unfold lift_oncoll.
    destruct d; trivial.
    induction l; simpl; trivial.
    autorewrite with lalg.
    case_eq (@fun_of_lalg TrivialModel.trivial_foreign_runtime h0 cenv
             (@app
                (prod string
                   (@data (@foreign_runtime_data TrivialModel.trivial_foreign_runtime))) env
                (@cons
                   (prod string
                      (@data (@foreign_runtime_data TrivialModel.trivial_foreign_runtime)))
                   (@pair string
                      (@data (@foreign_runtime_data TrivialModel.trivial_foreign_runtime))
                      (String (Ascii.Ascii false false false false true true true false)
                         EmptyString) a)
                   (@nil
                      (prod string
                         (@data (@foreign_runtime_data TrivialModel.trivial_foreign_runtime))))))
             (@LAUnop TrivialModel.trivial_foreign_runtime
                (@ADot TrivialModel.trivial_foreign_data
                   (@TrivialModel.trivial_foreign_unary_op TrivialModel.trivial_foreign_data)
                   (String (Ascii.Ascii true false false false false true true false)
                      (String (Ascii.Ascii false false true false false true true false)
                         (String (Ascii.Ascii false false true false false true true false)
                            (String
                               (Ascii.Ascii false true false false true true true false)
                               EmptyString)))))
                (@LAVar TrivialModel.trivial_foreign_runtime
                   (String (Ascii.Ascii false false false false true true true false)
                           EmptyString)))); simpl; intros.
    - unfold fun_of_lalg in H |- *.
      rewrite H; clear H.
      rewrite olift_some.
      match_case_in IHl; intros; rewrite H in IHl.
      + apply some_lift in H.
        destruct H as [? ? ?]; subst.
        apply lift_injective in IHl; [ | inversion 1; trivial].
        rewrite <- IHl; clear IHl.
        rewrite e.
        simpl.
        destruct ((@rmap (@data TrivialModel.trivial_foreign_data)
                 (@data TrivialModel.trivial_foreign_data)
                 (@fun_of_lalg_lambda TrivialModel.trivial_foreign_runtime h0 cenv env
                    (@LALambda TrivialModel.trivial_foreign_runtime
                       (String (Ascii.Ascii true false false false false true true false)
                          EmptyString)
                       (@LAUnop TrivialModel.trivial_foreign_runtime
                          (@ADot TrivialModel.trivial_foreign_data
                             (@TrivialModel.trivial_foreign_unary_op
                                TrivialModel.trivial_foreign_data)
                             (String
                                (Ascii.Ascii true true false false false true true false)
                                (String
                                   (Ascii.Ascii true false false true false true true false)
                                   (String
                                      (Ascii.Ascii false false true false true true true
                                         false)
                                      (String
                                         (Ascii.Ascii true false false true true true true
                                            false) EmptyString)))))
                          (@LAVar TrivialModel.trivial_foreign_runtime
                             (String
                                (Ascii.Ascii true false false false false true true false)
                                EmptyString))))) x)); simpl.
        * autorewrite with lalg.
          unfold fun_of_lalg.
          simpl.
          unfold edot.
          rewrite @assoc_lookupr_app.
          simpl.
          trivial.
        * repeat match_destr.
      + symmetry in IHl.
        apply none_lift in IHl.
        apply none_lift in H.
        rewrite H, IHl.
        simpl.
        destruct d; simpl; trivial.
        match_destr.
    - match_case; intros.
      unfold fun_of_lalg in H, H0.
      rewrite H in H0.
      simpl in H0.
      discriminate.
  Qed.

  
(*  Eval vm_compute in (eval_q h T1l db1). *)
(*  Eval vm_compute in (eval_q h T1r db1). *)
(*  Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda T1l)) db1). *)
(*  Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda T1r)) db1). *)

  (* T2 : map(λ(x) x.age)(sel(λ(p) p.age > 25)(P)) == sel(λ(a) a > 25)(map(λ(p) p.age)(P)) *)
  Definition T2l P :=
    LAMap (LALambda "x" (LAUnop (ADot "age") (LAVar "x")))
          (LASelect (LALambda "p" (LABinop ALt
                                           (LAConst (dnat 25))
                                           (LAUnop (ADot "age") (LAVar "p")))) P).

  Definition T2r P :=
    LASelect (LALambda "a" (LABinop ALt
                                    (LAConst (dnat 25))
                                    (LAVar "a")))
             (LAMap (LALambda "p" (LAUnop (ADot "age") (LAVar "p"))) P).

  
(*  Eval vm_compute in (eval_q h T2l db2). *)
  (* Eval vm_compute in (eval_q h T2r db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda T2l)) db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda T2r)) db2). *)

  (* A3 : map(λ(p) [ person: p, kids: sel(λ(c) c.age > 25)(p.child) ])(P) *)

  Definition A3 P :=
    LAMap
      (LALambda "p"
                (LABinop AConcat (LAUnop (ARec "person") (LAVar "p"))
                         (LAUnop (ARec "kids")
                                 (LASelect
                                    (LALambda "c"
                                              (LABinop ALt
                                                       (LAConst (dnat 25))
                                                       (LAUnop (ADot "age") (LAVar "c"))))
                                    (LAUnop (ADot "child") (LAVar "p")))))) P.

  (* Eval vm_compute in (eval_q h A3 db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda A3)) db2). *)
  
  (* A4 : map(λ(p) [ person: p, kids: sel(λ(c) p.age > 25)(p.child) ])(P) *)

  Definition A4 P :=
    LAMap
      (LALambda "p"
                (LABinop AConcat (LAUnop (ARec "person") (LAVar "p"))
                         (LAUnop (ARec "kids")
                                 (LASelect
                                    (LALambda "c"
                                              (LABinop ALt
                                                       (LAConst (dnat 25))
                                                       (LAUnop (ADot "age") (LAVar "p"))))
                                    (LAUnop (ADot "child") (LAVar "p")))))) P.

  (* Eval vm_compute in (eval_q h A4 db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda A4)) db2). *)

End LambdaNRATests.


(* Now let's see if we can optimize *)

Require Import NRAEnvOptimFunc.
Require Import OptimizerLogger.
Require Import NRAEnv.
Context {l:optimizer_logger string nraenv}.

Definition T1env : nraenv := (nraenv_of_lalg_lambda (q_to_lambda T1l)).
(* Eval vm_compute in T1env. *)
Definition T1env_opt := toptim_nraenv T1env.
(* Eval vm_compute in T1env_opt. *)
Definition T1nnrc_opt :=
  TrivialCompiler.QDriver.nraenv_optim_to_nnrc_optim T1env_opt.
(* Eval vm_compute in T1nnrc_opt. *)

Definition T2env := (nraenv_of_lalg_lambda (q_to_lambda T2l)).
(* Eval vm_compute in T2env. *)
Definition T2env_opt := toptim_nraenv T2env.
(* Eval vm_compute in T2env_opt. *)
(* Note: this optimizes perfectly the access to environment, but does not yield T2r --- I believe
   this is the right plan in most cases since you would more often want to
   push the select inside the map, rather than the other way around. *)
Definition T2nnrc_opt := TrivialCompiler.QDriver.nraenv_optim_to_nnrc_optim T2env_opt.
(* Eval vm_compute in T2nnrc_opt. *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "QCert")) ***
*** End: ***
*)
