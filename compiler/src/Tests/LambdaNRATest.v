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

Require Import Utils.
Require Import CommonRuntime.
Require Import LambdaNRA.
Require Import LambdaNRAEq.
Require Import LambdaNRAtoNRAEnv.
Require Import TrivialCompiler.

Import TrivialCompiler.

(* Examples from [CZ96] Figure 2. 'as is' *)
Section LambdaNRATest.

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

  (* T1 : P.map{p => p.addr}.map{a => a.city} == P.map{p => p.addr.city} *)
  (** The original version of T1 *)
  Definition T1l P :=
    LNRAMap (LNRALambda "a" (LNRAUnop (OpDot "city") (LNRAVar "a")))
            (LNRAMap (LNRALambda "p" (LNRAUnop (OpDot "addr") (LNRAVar "p"))) P).

  (** The simplified version of T1 *)
  Definition T1r P :=
    LNRAMap (LNRALambda "p" (LNRAUnop (OpDot "city") (LNRAUnop (OpDot "addr") (LNRAVar "p")))) P.


Hint Rewrite @lnra_lambda_eval_lambda_eq : lambda_nra'.
Hint Rewrite @lambda_nra_eval_map_eq : lambda_nra'.
Hint Rewrite @lambda_nra_eval_map_concat_eq : lambda_nra'.
Hint Rewrite @lambda_nra_eval_product_eq : lambda_nra'.
Hint Rewrite @lambda_nra_eval_filter_eq : lambda_nra'.

  Lemma T1lr_equiv P : lambda_nra_eq (T1l P) (T1r P).
  Proof.
    unfold lambda_nra_eq, T1l, T1r.
    intros.
    autorewrite with lambda_nra'.
    simpl.
    unfold olift.
    destruct (lambda_nra_eval h0 cenv env P); trivial.
    unfold lift_oncoll.
    destruct d; trivial.
    induction l; simpl; trivial.
    autorewrite with lambda_nra'.
    case_eq (@lambda_nra_eval TrivialModel.trivial_foreign_runtime h0 cenv
            (@rec_sort string ODT_string
               (@data (@foreign_runtime_data TrivialModel.trivial_foreign_runtime))
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
                           (@data (@foreign_runtime_data TrivialModel.trivial_foreign_runtime)))))))
            (@LNRAUnop TrivialModel.trivial_foreign_runtime
               (@OpDot TrivialModel.trivial_foreign_data
                  (@TrivialModel.trivial_foreign_unary_op)
                  (String (Ascii.Ascii true false false false false true true false)
                     (String (Ascii.Ascii false false true false false true true false)
                        (String (Ascii.Ascii false false true false false true true false)
                           (String (Ascii.Ascii false true false false true true true false)
                              EmptyString)))))
               (@LNRAVar TrivialModel.trivial_foreign_runtime
                  (String (Ascii.Ascii false false false false true true true false)
                     EmptyString)))); simpl; intros.
    - unfold lambda_nra_eval in H |- *.
      rewrite H; clear H.
      rewrite olift_some.
      match_case_in IHl; intros; rewrite H in IHl.
      + apply some_lift in H.
        destruct H as [? ? ?]; subst.
        apply lift_injective in IHl; [ | inversion 1; trivial].
        rewrite <- IHl; clear IHl.
        rewrite e.
        simpl.
        destruct ((@lift_map (@data TrivialModel.trivial_foreign_data)
                 (@data TrivialModel.trivial_foreign_data)
                 (@lnra_lambda_eval TrivialModel.trivial_foreign_runtime h0 cenv env
                    (@LNRALambda TrivialModel.trivial_foreign_runtime
                       (String (Ascii.Ascii true false false false false true true false)
                          EmptyString)
                       (@LNRAUnop TrivialModel.trivial_foreign_runtime
                          (@OpDot TrivialModel.trivial_foreign_data
                             (@TrivialModel.trivial_foreign_unary_op)
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
                          (@LNRAVar TrivialModel.trivial_foreign_runtime
                             (String
                                (Ascii.Ascii true false false false false true true false)
                                EmptyString))))) x)); simpl.
        * autorewrite with lambda_nra'.
          unfold lambda_nra_eval.
          simpl.
          unfold edot.
          simpl.
          rewrite (@assoc_lookupr_drec_sort string ODT_string).
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
      unfold lambda_nra_eval in H, H0.
      rewrite H in H0.
      simpl in H0.
      discriminate.
  Qed.

  
(*  Eval vm_compute in (eval_q h T1l db1). *)
(*  Eval vm_compute in (eval_q h T1r db1). *)
(*  Eval vm_compute in (eval_nraenv_q h (cnraenv_of_lnra_lambda (q_to_lambda T1l)) db1). *)
(*  Eval vm_compute in (eval_nraenv_q h (cnraenv_of_lnra_lambda (q_to_lambda T1r)) db1). *)

  (* T2 : P.filter{p => p.age > 25}.map{x => x.age} == P.map{p => p.age}.filter{a => a > 25} *)
  Definition T2l P :=
    LNRAMap (LNRALambda "x" (LNRAUnop (OpDot "age") (LNRAVar "x")))
            (LNRAFilter (LNRALambda "p" (LNRABinop OpLt
                                                   (LNRAConst (dnat 25))
                                                   (LNRAUnop (OpDot "age") (LNRAVar "p")))) P).
  
  Definition T2r P :=
    LNRAFilter (LNRALambda "a" (LNRABinop OpLt
                                          (LNRAConst (dnat 25))
                                          (LNRAVar "a")))
               (LNRAMap (LNRALambda "p" (LNRAUnop (OpDot "age") (LNRAVar "p"))) P).

  
(*  Eval vm_compute in (eval_q h T2l db2). *)
  (* Eval vm_compute in (eval_q h T2r db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (cnraenv_of_lnra_lambda (q_to_lambda T2l)) db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (cnraenv_of_lnra_lambda (q_to_lambda T2r)) db2). *)

  (* A3 : P.map{p => [ person: p, kids: p.child.filter{c => c.age > 25} ]} *)

  Definition A3 P :=
    LNRAMap
      (LNRALambda "p"
                  (LNRABinop OpRecConcat (LNRAUnop (OpRec "person") (LNRAVar "p"))
                             (LNRAUnop (OpRec "kids")
                                       (LNRAFilter
                                          (LNRALambda "c"
                                                      (LNRABinop OpLt
                                                                 (LNRAConst (dnat 25))
                                                                 (LNRAUnop (OpDot "age") (LNRAVar "c"))))
                                          (LNRAUnop (OpDot "child") (LNRAVar "p")))))) P.

  (* Eval vm_compute in (eval_q h A3 db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (cnraenv_of_lnra_lambda (q_to_lambda A3)) db2). *)
  
  (* A4 : P.map{p => [ person: p, kids: p.child.filter{c => p.age > 25} ]} *)

  Definition A4 P :=
    LNRAMap
      (LNRALambda "p"
                  (LNRABinop OpRecConcat (LNRAUnop (OpRec "person") (LNRAVar "p"))
                             (LNRAUnop (OpRec "kids")
                                       (LNRAFilter
                                          (LNRALambda "c"
                                                      (LNRABinop OpLt
                                                                 (LNRAConst (dnat 25))
                                                                 (LNRAUnop (OpDot "age") (LNRAVar "p"))))
                                          (LNRAUnop (OpDot "child") (LNRAVar "p")))))) P.

  (* Eval vm_compute in (eval_q h A4 db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (cnraenv_of_lnra_lambda (q_to_lambda A4)) db2). *)

End LambdaNRATest.

Section LambdaNRALinq.

  Definition linq_example Persons
    := LNRAMap
         (LNRALambda "p"
                     (LNRAUnop (OpDot "name") (LNRAVar "p")))
         (LNRAFilter 
            (LNRALambda "p"
                        (LNRABinop OpLt
                                   (LNRAUnop (OpDot "name") (LNRAVar "p"))
                                   (LNRAConst (dnat 30))))
            Persons).
               
  Definition demo_example :=
    LNRAFilter
         (LNRALambda "p"
                     (LNRABinop OpLt
                                (LNRAUnop (OpDot "age") (LNRAVar "p"))
                                (LNRAConst (dnat 30))))
         (LNRABinop OpBagUnion (LNRATable "Persons1")
                    (LNRATable "Persons2")).

End LambdaNRALinq.

(* Now let's see if we can optimize *)

Require Import OptimizerLogger.
Require Import NRAEnv.
Require Import NRAEnvOptimizer.
Require Import CompDriver.

Definition silent_optim := silent_optimizer_logger string nraenv.
Existing Instance silent_optim.

Definition T1env : nraenv := (nraenv_of_lnra_lambda (q_to_lambda T1l)).
(* Eval vm_compute in T1env. *)
Definition T1env_opt := nraenv_optim_default T1env.
(* Eval vm_compute in T1env_opt. *)
Definition T1nnrc_opt :=
  TrivialCompiler.QDriver.nraenv_optim_to_nnrc_optim T1env_opt.
(* Eval vm_compute in T1nnrc_opt. *)

Definition T2env := (nraenv_of_lnra_lambda (q_to_lambda T2l)).
(* Eval vm_compute in T2env. *)
Definition T2env_opt := nraenv_optim_default T2env.
(* Eval vm_compute in T2env_opt. *)
(* Note: this optimizes perfectly the access to environment, but does not yield T2r --- I believe
   this is the right plan in most cases since you would more often want to
   push the map inside the filter, rather than the other way around. *)
Definition T2nnrc_opt := TrivialCompiler.QDriver.nraenv_optim_to_nnrc_optim T2env_opt.
(* Eval vm_compute in T2nnrc_opt. *)

