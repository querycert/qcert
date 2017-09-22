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

(** NRAEnv is nested relational algebra, extended with operations to
  facilitate encoding of environment manipulation. It serves as the
  main intermediate language for optimization. *)

(** NRAEnv is a thin layer over the core language cNRAEnv. As cNRAEnv,
  NRAEnv is combinators-based, i.e., it is evaluated with only a
  static global environment, but no notion of local
  variables. *)

(** Additional operators in NRAEnv can be easily expressed in terms of
  the core cNRAEnv, but are useful for optimization purposes. Those
  operators notably include joins and group-by. *)

(** NRAEnv builds on a large body of work from the database
community. For a complete treatment on nested relational algebras, we
refer to Guido Moerkotte's "Building Query Compilers", Chapter 7.

   http://pi3.informatik.uni-mannheim.de/~moer/querycompiler.pdf *)

(** Summary:

- Language: NRAEnv (Nested Relational Algebra with Environments)
- Based on: "Handling Environments in a Nested Relational Algebra with
  Combinators and an Implementation in a Verified Query Compiler"
  Joshua Auerbach, Martin Hirzel, Louis Mandel, Avraham Shinnar, and
  Jérôme Siméon. SIGMOD'2017.
- translating to NRAEnv: LambdaNRA, SQL, OQL, CAMP, cNRAEnv
- translating from NRAEnv: NNRC, cNRAEnv *)

Section NRAEnv.
  Require Import String.
  Require Import List.
  Require Import Compare_dec.
  Require Import EquivDec.
  Require Import Utils.
  Require Import CommonRuntime.
  Require Import cNRAEnv.
  Require Import cNRAEnvEq.

(** * Abstract Syntax *)

  Context (h:list(string*string)).
  Context {fruntime:foreign_runtime}.

(** As much as possible, notations are aligned with those of S. Cluet
   and G. Moerkotte. Nested queries in object bases. In Proc. Int.
   Workshop on Database Programming Languages , pages 226-242,
   1993. *)

  Inductive nraenv : Set :=
  | NRAEnvID : nraenv                                         (**r Current value *)
  | NRAEnvConst : data -> nraenv                              (**r Constant value *)
  | NRAEnvBinop : binary_op -> nraenv -> nraenv -> nraenv         (**r Binary operator *)
  | NRAEnvUnop : unary_op -> nraenv -> nraenv                  (**r Unary operator *)
  | NRAEnvMap : nraenv -> nraenv -> nraenv                    (**r Map [χ] *)
  | NRAEnvMapProduct : nraenv -> nraenv -> nraenv              (**r Dependent cartesian product [⋈ᵈ] *)
  | NRAEnvProduct : nraenv -> nraenv -> nraenv                (**r Cartesian product [×] *)
  | NRAEnvSelect : nraenv -> nraenv -> nraenv                 (**r Relational selection [σ] *) 
  | NRAEnvDefault : nraenv -> nraenv -> nraenv                (**r Default for empty collection [∥] *)
  | NRAEnvEither : nraenv -> nraenv -> nraenv                 (**r Choice *)
  | NRAEnvEitherConcat : nraenv -> nraenv -> nraenv           (**r Choice with concatenation *)
  | NRAEnvApp : nraenv -> nraenv -> nraenv                    (**r Composition *)
  | NRAEnvGetConstant : string -> nraenv                      (**r Accesses a global constant *)
  | NRAEnvEnv : nraenv                                        (**r Current environment *)
  | NRAEnvAppEnv : nraenv -> nraenv -> nraenv                 (**r Composition over the environment *)
  | NRAEnvMapEnv : nraenv -> nraenv                           (**r Map over the environment *)
  | NRAEnvFlatMap : nraenv -> nraenv -> nraenv                (**r Flat map *)
  | NRAEnvJoin : nraenv -> nraenv -> nraenv -> nraenv         (**r Join [⋈] *)
  | NRAEnvProject : list string -> nraenv -> nraenv           (**r Projection [Π] *)
  | NRAEnvGroupBy : string -> list string -> nraenv -> nraenv (**r GroupBy [Γ] *)
  | NRAEnvUnnest : string -> string -> nraenv -> nraenv       (**r Unnesting [μ] *)
  .

  (** Equality between two NRAEnv expressions is decidable. *)
  
  Global Instance nraenv_eqdec : EqDec nraenv eq.
  Proof.
    change (forall x y : nraenv,  {x = y} + {x <> y}).
    decide equality;
      try solve [apply binary_op_eqdec | apply unary_op_eqdec | apply data_eqdec | apply string_eqdec | apply list_eqdec; apply string_eqdec].
  Defined.

  (** * Macros *)

  (** All the additional operators are defined in terms of the core cNRAEnv. *)
  
  (** ** Join operations *)

  Definition join (op1 op2 op3 : nraenv_core) : nraenv_core :=
    (cNRAEnvSelect op1 (cNRAEnvProduct op2 op3)).

  Definition semi_join (op1 op2 op3 : nraenv_core) : nraenv_core :=
    cNRAEnvSelect (cNRAEnvUnop OpNeg (cNRAEnvBinop OpEqual (cNRAEnvSelect op1 (cNRAEnvProduct ((cNRAEnvUnop OpBag) cNRAEnvID) op3)) (cNRAEnvConst (dcoll nil)))) op2.

  Definition anti_join (op1 op2 op3 : nraenv_core) : nraenv_core :=
    cNRAEnvSelect (cNRAEnvBinop OpEqual (cNRAEnvSelect op1 (cNRAEnvProduct ((cNRAEnvUnop OpBag) cNRAEnvID) op3)) (cNRAEnvConst (dcoll nil))) op2.

  (** ** Map operations *)

  Definition map_add_rec (s:string) (op1 op2 : nraenv_core) : nraenv_core :=
    cNRAEnvMap ((cNRAEnvBinop OpRecConcat) cNRAEnvID ((cNRAEnvUnop (OpRec s)) op1)) op2.
  Definition map_to_rec (s:string) (op : nraenv_core) : nraenv_core :=
    cNRAEnvMap (cNRAEnvUnop (OpRec s) cNRAEnvID) op.

  Definition flat_map (op1 op2 : nraenv_core) : nraenv_core :=
    cNRAEnvUnop OpFlatten (cNRAEnvMap op1 op2).
  
  (** ** Projection *)
  Definition project (fields:list string) (op:nraenv_core) : nraenv_core
    := cNRAEnvMap (cNRAEnvUnop (OpRecProject fields) cNRAEnvID) op.

  Definition project_remove (s:string) (op:nraenv_core) : nraenv_core :=
    cNRAEnvMap ((cNRAEnvUnop (OpRecRemove s)) cNRAEnvID) op.

  (** ** Renaming *)
  (* renames field s1 to s2 *)
  Definition map_rename_rec (s1 s2:string) (op:nraenv_core) : nraenv_core :=
    cNRAEnvMap ((cNRAEnvBinop OpRecConcat) ((cNRAEnvUnop (OpRec s2)) ((cNRAEnvUnop (OpDot s1)) cNRAEnvID))
                  ((cNRAEnvUnop (OpRecRemove s1)) cNRAEnvID)) op.

  (** ** Grouping *)

  (** Defining group-by in terms of the core is more tricky, but is
     possible. You need to do two passes, and compare elements with
     the same set of attribute names which means you need to
     encapsulate each branch with distinct record names. *)

  Import ListNotations.
  (* g: partition name ; sl: list of grouping attributes *)
  (* Γ[g][sl](op) ==
     χ⟨
         ID.t1.t2
         ⊗
         [ g : χ⟨ ID.t3 ⟩
               (σ⟨ π[sl](ID.t1) = π[sl](ID.t3) ⟩
                 ({ ID.t2 } × ID.t4)) ]
       ⟩
      ({ [ t4 : χ⟨[t3]⟩(op) ] } × (χ⟨[t2:ID]⟩(χ⟨[t1:ID]⟩(♯distinct(Π[sl](op)))))) *)
  
  Definition group_by_no_env (g:string) (sl:list string) (op : nraenv_core) : nraenv_core :=
    cNRAEnvMap
      (cNRAEnvBinop OpRecConcat
               (cNRAEnvUnop (OpDot "1") (cNRAEnvUnop (OpDot "2") cNRAEnvID))
               (cNRAEnvUnop (OpRec g)
                       (cNRAEnvMap (cNRAEnvUnop (OpDot "3") cNRAEnvID)
                              (cNRAEnvSelect
                                 (cNRAEnvBinop OpEqual
                                          (cNRAEnvUnop (OpRecProject sl) (cNRAEnvUnop (OpDot "1") cNRAEnvID))
                                          (cNRAEnvUnop (OpRecProject sl) (cNRAEnvUnop (OpDot "3") cNRAEnvID)))
                                 (cNRAEnvProduct (cNRAEnvUnop OpBag (cNRAEnvUnop (OpDot "2") cNRAEnvID))
                                            (cNRAEnvUnop (OpDot "4") cNRAEnvID))))))
      (cNRAEnvProduct
         (cNRAEnvUnop OpBag (cNRAEnvUnop (OpRec "4") (map_to_rec "3" op)))
         (map_to_rec "2" (map_to_rec "1" (cNRAEnvUnop OpDistinct (project sl op))))).

  (** This is an alternative definition that isn't quite as
      inefficient. It stores the result of the input operator in the
      environment so it isn't computed twice. This is still
      quadratic. *)
  
  (* g: partition name ; sl: list of grouping attributes *)
  (* Γ[g][sl](op) ==
      (χ⟨ ID ⊕ [ g : σ⟨ ENV.$key = π[sl](ID) ⟩(ENV.$pregroup) ◯ᵉ ([$key:ID] ⊕ ENV) ] ⟩
        (♯distinct(Π[sl](ENV.$pregroup)))) ◯ᵉ [ $pregroup : op ]

   *)
  Definition group_by_with_env (g:string) (sl:list string) (op : nraenv_core) : nraenv_core :=
    let op_pregroup := cNRAEnvUnop (OpDot "$pregroup") cNRAEnvEnv in
    cNRAEnvAppEnv
      (cNRAEnvMap
         (cNRAEnvBinop OpRecConcat
                  (cNRAEnvUnop (OpRec g)
                          (cNRAEnvAppEnv (cNRAEnvSelect (cNRAEnvBinop OpEqual
                                                       (cNRAEnvUnop (OpRecProject sl) cNRAEnvID)
                                                       (cNRAEnvUnop (OpDot "$key") cNRAEnvEnv))
                                              op_pregroup
                                    )
                                    (cNRAEnvBinop OpRecConcat (cNRAEnvUnop (OpRec "$key") cNRAEnvID) cNRAEnvEnv)
                          )
                  )
                  cNRAEnvID
         )
         (cNRAEnvUnop OpDistinct (project sl op_pregroup))
      )
      (cNRAEnvUnop (OpRec "$pregroup") op).

  (** ** Unnesting *)

  Definition unnest_one (s:string) (op:nraenv_core) : nraenv_core :=
    cNRAEnvMap ((cNRAEnvUnop (OpRecRemove s)) cNRAEnvID) (cNRAEnvMapProduct ((cNRAEnvUnop (OpDot s)) cNRAEnvID) op).

  Definition unnest (a b:string) (op:nraenv_core) : nraenv_core :=
    cNRAEnvMap ((cNRAEnvUnop (OpRecRemove a)) cNRAEnvID) (cNRAEnvMapProduct (cNRAEnvMap ((cNRAEnvUnop (OpRec b)) cNRAEnvID) ((cNRAEnvUnop (OpDot a)) cNRAEnvID)) op).

  (** * Evaluation Semantics *)

  (** The semantics of NRAEnv is defined as macro-expansion to the core language cNRAEnv. *) 
  
  Fixpoint nraenv_core_of_nraenv (e:nraenv) : nraenv_core :=
    match e with
      | NRAEnvID => cNRAEnvID
      | NRAEnvConst d => cNRAEnvConst d
      | NRAEnvBinop b e1 e2 => cNRAEnvBinop b (nraenv_core_of_nraenv e1) (nraenv_core_of_nraenv e2)
      | NRAEnvUnop u e1 => cNRAEnvUnop u (nraenv_core_of_nraenv e1)
      | NRAEnvMap e1 e2 => cNRAEnvMap (nraenv_core_of_nraenv e1) (nraenv_core_of_nraenv e2)
      | NRAEnvMapProduct e1 e2 => cNRAEnvMapProduct (nraenv_core_of_nraenv e1) (nraenv_core_of_nraenv e2)
      | NRAEnvProduct e1 e2 => cNRAEnvProduct (nraenv_core_of_nraenv e1) (nraenv_core_of_nraenv e2)
      | NRAEnvSelect e1 e2 => cNRAEnvSelect (nraenv_core_of_nraenv e1) (nraenv_core_of_nraenv e2)
      | NRAEnvDefault e1 e2 => cNRAEnvDefault (nraenv_core_of_nraenv e1) (nraenv_core_of_nraenv e2)
      | NRAEnvEither opl opr => cNRAEnvEither (nraenv_core_of_nraenv opl) (nraenv_core_of_nraenv opr)
      | NRAEnvEitherConcat op1 op2 => cNRAEnvEitherConcat (nraenv_core_of_nraenv op1) (nraenv_core_of_nraenv op2)
      | NRAEnvApp e1 e2 => cNRAEnvApp (nraenv_core_of_nraenv e1) (nraenv_core_of_nraenv e2)
      | NRAEnvGetConstant s => cNRAEnvGetConstant s
      | NRAEnvEnv => cNRAEnvEnv
      | NRAEnvAppEnv e1 e2 => cNRAEnvAppEnv (nraenv_core_of_nraenv e1) (nraenv_core_of_nraenv e2)
      | NRAEnvMapEnv e1 => cNRAEnvMapEnv (nraenv_core_of_nraenv e1)
      | NRAEnvFlatMap e1 e2 => flat_map (nraenv_core_of_nraenv e1) (nraenv_core_of_nraenv e2)
      | NRAEnvJoin e1 e2 e3 => join (nraenv_core_of_nraenv e1) (nraenv_core_of_nraenv e2) (nraenv_core_of_nraenv e3)
      | NRAEnvProject ls e1 => project ls (nraenv_core_of_nraenv e1)
      | NRAEnvGroupBy s ls e1 => group_by_with_env s ls (nraenv_core_of_nraenv e1)
      | NRAEnvUnnest a b e1 => unnest a b (nraenv_core_of_nraenv e1)
    end.

  Definition nraenv_eval c (e:nraenv) (env:data) (x:data) : option data :=
    nraenv_core_eval h c (nraenv_core_of_nraenv e) env x.

  (** * Round-tripping *)

  (** Just checking that cNRAEnv can be lifted back to NRAEnv, and
  showing that we can round-trip. *)

  Fixpoint nraenv_of_nraenv_core (a:nraenv_core) : nraenv :=
    match a with
      | cNRAEnvID => NRAEnvID
      | cNRAEnvConst d => NRAEnvConst d
      | cNRAEnvBinop b e1 e2 => NRAEnvBinop b (nraenv_of_nraenv_core e1) (nraenv_of_nraenv_core e2)
      | cNRAEnvUnop u e1 => NRAEnvUnop u (nraenv_of_nraenv_core e1)
      | cNRAEnvMap e1 e2 => NRAEnvMap (nraenv_of_nraenv_core e1) (nraenv_of_nraenv_core e2)
      | cNRAEnvMapProduct e1 e2 => NRAEnvMapProduct (nraenv_of_nraenv_core e1) (nraenv_of_nraenv_core e2)
      | cNRAEnvProduct e1 e2 => NRAEnvProduct (nraenv_of_nraenv_core e1) (nraenv_of_nraenv_core e2)
      | cNRAEnvSelect e1 e2 => NRAEnvSelect (nraenv_of_nraenv_core e1) (nraenv_of_nraenv_core e2)
      | cNRAEnvDefault e1 e2 => NRAEnvDefault (nraenv_of_nraenv_core e1) (nraenv_of_nraenv_core e2)
      | cNRAEnvEither opl opr => NRAEnvEither (nraenv_of_nraenv_core opl) (nraenv_of_nraenv_core opr)
      | cNRAEnvEitherConcat op1 op2 => NRAEnvEitherConcat (nraenv_of_nraenv_core op1) (nraenv_of_nraenv_core op2)
      | cNRAEnvApp e1 e2 => NRAEnvApp (nraenv_of_nraenv_core e1) (nraenv_of_nraenv_core e2)
      | cNRAEnvGetConstant s => NRAEnvGetConstant s
      | cNRAEnvEnv => NRAEnvEnv
      | cNRAEnvAppEnv e1 e2 => NRAEnvAppEnv (nraenv_of_nraenv_core e1) (nraenv_of_nraenv_core e2)
      | cNRAEnvMapEnv e1 => NRAEnvMapEnv (nraenv_of_nraenv_core e1)
    end.

  Lemma nraenv_roundtrip (a:nraenv_core) :
    (nraenv_core_of_nraenv (nraenv_of_nraenv_core a)) = a.
  Proof.
    induction a; simpl; try reflexivity; try (rewrite IHa1; rewrite IHa2; try rewrite IHa3; reflexivity); rewrite IHa; reflexivity.
  Qed.

  (** * Toplevel *)
  
  (** Top-level evaluation is used externally by the Q*cert
  compiler. It takes an NRAEnv expression and a global environment as
  input. The initial current environment is set to an empty record,
  and the initial current value to unit. *)

  Section Top.
  
    Definition nraenv_eval_top (q:nraenv) (env:bindings) :=
      nraenv_eval (rec_sort env) q (drec nil) dunit.

  End Top.

  Section FreeVars.
    Fixpoint nraenv_free_vars (q:nraenv) : list string :=
      match q with
      | NRAEnvID => nil
      | NRAEnvConst rd => nil
      | NRAEnvBinop _ q1 q2 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvUnop _ q1 =>
        nraenv_free_vars q1
      | NRAEnvMap q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvMapProduct q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvProduct q1 q2 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvSelect q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvEither ql qr =>
        nraenv_free_vars ql ++ nraenv_free_vars qr
      | NRAEnvEitherConcat q1 q2 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvDefault q1 q2 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvApp q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvGetConstant s => s :: nil
      | NRAEnvEnv => nil
      | NRAEnvAppEnv q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvMapEnv q1 =>
        nraenv_free_vars q1
      | NRAEnvFlatMap q2 q1 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2
      | NRAEnvJoin q3 q1 q2 =>
        nraenv_free_vars q1 ++ nraenv_free_vars q2 ++ nraenv_free_vars q3
      | NRAEnvProject _ q1 =>
        nraenv_free_vars q1
      | NRAEnvGroupBy _ _ q1 =>
        nraenv_free_vars q1
      | NRAEnvUnnest _ _ q1 =>
        nraenv_free_vars q1
      end.

    Lemma nraenv_free_vars_as_core (q:nraenv) :
      nraenv_core_free_vars (nraenv_core_of_nraenv q) = nraenv_free_vars q.
    Proof.
      induction q; simpl; try reflexivity;
        try solve[rewrite IHq1; rewrite IHq2; reflexivity|rewrite IHq;reflexivity].
      - rewrite IHq1; rewrite IHq2; rewrite IHq3.
        rewrite app_assoc; reflexivity.
      - rewrite app_nil_r; rewrite IHq; reflexivity.
      - rewrite app_nil_r; rewrite IHq; reflexivity.
      - rewrite app_nil_r; rewrite app_nil_r; rewrite IHq; reflexivity.
    Qed.
  End FreeVars.

End NRAEnv.

(* begin hide *)
Delimit Scope nraenv_scope with nraenv.

Notation "h ⊢ EOp @ₓ x ⊣ c ; env" := (nraenv_eval h c EOp env x) (at level 10): nraenv_scope.
(* end hide *)

Local Open Scope string_scope.
Tactic Notation "nraenv_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NRAEnvID"
  | Case_aux c "NRAEnvConst"
  | Case_aux c "NRAEnvBinop"
  | Case_aux c "NRAEnvUnop"
  | Case_aux c "NRAEnvMap"
  | Case_aux c "NRAEnvMapProduct"
  | Case_aux c "NRAEnvProduct"
  | Case_aux c "NRAEnvSelect"
  | Case_aux c "NRAEnvDefault"
  | Case_aux c "NRAEnvEither"
  | Case_aux c "NRAEnvEitherConcat"
  | Case_aux c "NRAEnvApp"
  | Case_aux c "NRAEnvGetConstant"
  | Case_aux c "NRAEnvEnv"
  | Case_aux c "NRAEnvAppEnv"
  | Case_aux c "NRAEnvMapEnv"
  | Case_aux c "NRAEnvFlatMap"
  | Case_aux c "NRAEnvJoin"
  | Case_aux c "NRAEnvProject"
  | Case_aux c "NRAEnvGroupBy"
  | Case_aux c "NRAEnvUnnest"].

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
