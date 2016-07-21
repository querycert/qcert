Require Import String.
Require Import List.
Require Import Arith.
Require Import EquivDec.
Require Import Morphisms.

Require Import Utils BasicRuntime.

Require Import LambdaAlg LambdaAlgtoNRAEnv.
Require Import TrivialCompiler.
Import TrivialCompiler.

(* Examples from [CZ96] Figure 2. 'as is' *)
Section LambdaNRAExamples.

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

  (* T1 : map(λ(a) a.city)(map(λ(p) p.addr)(Q)) == map(λ(p) p.addr.city)(Q) *)
  Definition T1l Q :=
    LAMap (LALambda "a" (LAUnop (ADot "city") (LAVar "a")))
          (LAMap (LALambda "p" (LAUnop (ADot "addr") (LAVar "p"))) Q).

  Definition T1r Q :=
    LAMap (LALambda "p" (LAUnop (ADot "city") (LAUnop (ADot "addr") (LAVar "p")))) Q.

(*  Eval vm_compute in (eval_q h T1l db1). *)
(*  Eval vm_compute in (eval_q h T1r db1). *)
(*  Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda T1l)) db1). *)
(*  Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda T1r)) db1). *)

  (* T2 : map(λ(x) x.age)(sel(λ(p) p.age > 25)(Q)) == sel(λ(a) a > 25)(map(λ(p) p.age)(Q)) *)
  Definition T2l Q :=
    LAMap (LALambda "x" (LAUnop (ADot "age") (LAVar "x")))
          (LASelect (LALambda "p" (LABinop ALt
                                           (LAConst (dnat 25))
                                           (LAUnop (ADot "age") (LAVar "p")))) Q).

  Definition T2r Q :=
    LASelect (LALambda "a" (LABinop ALt
                                    (LAConst (dnat 25))
                                    (LAVar "a")))
             (LAMap (LALambda "p" (LAUnop (ADot "age") (LAVar "p"))) Q).

(*  Eval vm_compute in (eval_q h T2l db2). *)
  (* Eval vm_compute in (eval_q h T2r db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda T2l)) db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda T2r)) db2). *)

  (* A1 : map(λ(p) [ person: p, kids: sel(λ(c) c.age > 25)(p.child) ])(Q) *)

  Definition A1 Q :=
    LAMap
      (LALambda "p"
                (LABinop AConcat (LAUnop (ARec "person") (LAVar "p"))
                         (LAUnop (ARec "kids")
                                 (LASelect
                                    (LALambda "c"
                                              (LABinop ALt
                                                       (LAConst (dnat 25))
                                                       (LAUnop (ADot "age") (LAVar "c"))))
                                    (LAUnop (ADot "child") (LAVar "p")))))) Q.

  (* Eval vm_compute in (eval_q h A1 db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda A1)) db2). *)
  
  (* A2 : map(λ(p) [ person: p, kids: sel(λ(c) p.age > 25)(p.child) ])(Q) *)

  Definition A2 Q :=
    LAMap
      (LALambda "p"
                (LABinop AConcat (LAUnop (ARec "person") (LAVar "p"))
                         (LAUnop (ARec "kids")
                                 (LASelect
                                    (LALambda "c"
                                              (LABinop ALt
                                                       (LAConst (dnat 25))
                                                       (LAUnop (ADot "age") (LAVar "p"))))
                                    (LAUnop (ADot "child") (LAVar "p")))))) Q.

  (* Eval vm_compute in (eval_q h A2 db2). *)
  (* Eval vm_compute in (eval_nraenv_q h (algenv_of_lalg_lambda (q_to_lambda A2)) db2). *)

End LambdaNRAExamples.


(* Now let's see if we can optimize *)

Require Import TOptimEnvFunc.
Require Import OptimizerLogger.
Require Import RAlgEnv.
Context {l:optimizer_logger string algenv}.

Definition T1env := (algenv_of_lalg_lambda (q_to_lambda T1l)).
(* Eval vm_compute in T1env. *)
Definition T1env_opt := toptim T1env.
(* Eval vm_compute in T1env_opt. *)
Definition T1nnrc_opt := TrivialCompiler.CompCore.tcompile_nraenv_to_nnrc_typed_opt T1env_opt.
(* Eval vm_compute in T1nnrc_opt. *)

Definition T2env := (algenv_of_lalg_lambda (q_to_lambda T2l)).
(* Eval vm_compute in T2env. *)
Definition T2env_opt := toptim T2env.
(* Eval vm_compute in T2env_opt. *)
(* Note: this optimizes perfectly the access to environment, but does not yield T2r --- I believe
   this is the right plan in most cases since you would more often want to
   push the select inside the map, rather than the other way around. *)
Definition T2nnrc_opt := TrivialCompiler.CompCore.tcompile_nraenv_to_nnrc_typed_opt T2env_opt.
(* Eval vm_compute in T2nnrc_opt. *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
