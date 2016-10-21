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

Section RAlgEnvExt.
  Require Import String List Compare_dec.
  Require Import EquivDec.

  Require Import Utils BasicRuntime.
  Require Import RAlgEnv.

  (* Algebra *)

  (* By convention, "static" parameters come first, followed by
     dependent operators. This allows for instanciation on those
     parameters *)

  (* Joins *)

  Context {fruntime:foreign_runtime}.

  Definition join (op1 op2 op3 : algenv) : algenv :=
    (ANSelect op1 (ANProduct op2 op3)).

  Definition semi_join (op1 op2 op3 : algenv) : algenv :=
    ANSelect (ANUnop ANeg (ANBinop AEq (ANSelect op1 (ANProduct ((ANUnop AColl) ANID) op3)) (ANConst (dcoll nil)))) op2.

  Definition anti_join (op1 op2 op3 : algenv) : algenv :=
    ANSelect (ANBinop AEq (ANSelect op1 (ANProduct ((ANUnop AColl) ANID) op3)) (ANConst (dcoll nil))) op2.

  (* Maps *)

  Definition map_add_rec (s:string) (op1 op2 : algenv) : algenv :=
    ANMap ((ANBinop AConcat) ANID ((ANUnop (ARec s)) op1)) op2.
  Definition map_to_rec (s:string) (op : algenv) : algenv :=
    ANMap (ANUnop (ARec s) ANID) op.

  Definition flat_map (op1 op2 : algenv) : algenv :=
    ANUnop AFlatten (ANMap op1 op2).
  
  (* Projects *)
  Definition project (fields:list string) (op:algenv) : algenv
    := ANMap (ANUnop (ARecProject fields) ANID) op.

  Definition project_remove (s:string) (op:algenv) : algenv :=
    ANMap ((ANUnop (ARecRemove s)) ANID) op.

  (* Renaming *)
  (* renames field s1 to s2 *)
  Definition map_rename_rec (s1 s2:string) (op:algenv) : algenv :=
    ANMap ((ANBinop AConcat) ((ANUnop (ARec s2)) ((ANUnop (ADot s1)) ANID))
                  ((ANUnop (ARecRemove s1)) ANID)) op.

  (* Grouping *)

  (* Tricky -- you need to do two passes, and compare elements with
     the same set of attribute names which means you need to
     encapsulate each branch with distinct record names... This is not
     so great. *)

  (*
    group1 g s1 [{s1->1,r_1}, {s1->2,r_2}, {s1->1,r_3}] 
  = [{s1->1,g->[{s1->1,r_1}, {s1->1,r_3}]}, {s1->2, g->[{s1->2,r_2}]}]
  *)

  Import ListNotations.
  (* g: partition name ; s1: single grouping attribute *)
  (* Γ₁[g][s1](op) ==
     χ⟨
         ID.t1.t2
         ⊗
         [ g : χ⟨ ID.t3 ⟩
               (σ⟨ ID.t1.s1 = ID.t3.s1 ⟩
                 ({ ID.t2 } × ID.t4)) ]
       ⟩
      ({ [ t4 : χ⟨[t3]⟩(op) ] } × (χ⟨[t2:ID]⟩(χ⟨[t1:ID]⟩(♯distinct(Π[s1](op)))))) *)
  
    Definition group_one (g:string) (s1:string) (op : algenv) : algenv :=
      ANMap
        (ANBinop AConcat
                 (ANUnop (ADot "1") (ANUnop (ADot "2") ANID))
                 (ANUnop (ARec g)
                         (ANMap (ANUnop (ADot "3") ANID)
                                (ANSelect
                                   (ANBinop AEq
                                            (ANUnop (ADot s1) (ANUnop (ADot "1") ANID))
                                            (ANUnop (ADot s1) (ANUnop (ADot "3") ANID)))
                                   (ANProduct (ANUnop AColl (ANUnop (ADot "2") ANID))
                                              (ANUnop (ADot "4") ANID))))))
        (ANProduct
           (ANUnop AColl (ANUnop (ARec "4") (map_to_rec "3" op)))
           (map_to_rec "2" (map_to_rec "1" (ANUnop ADistinct (project (s1::nil) op))))).

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
  
    Definition group_full (g:string) (sl:list string) (op : algenv) : algenv :=
      ANMap
        (ANBinop AConcat
                 (ANUnop (ADot "1") (ANUnop (ADot "2") ANID))
                 (ANUnop (ARec g)
                         (ANMap (ANUnop (ADot "3") ANID)
                                (ANSelect
                                   (ANBinop AEq
                                            (ANUnop (ARecProject sl) (ANUnop (ADot "1") ANID))
                                            (ANUnop (ARecProject sl) (ANUnop (ADot "3") ANID)))
                                   (ANProduct (ANUnop AColl (ANUnop (ADot "2") ANID))
                                              (ANUnop (ADot "4") ANID))))))
        (ANProduct
           (ANUnop AColl (ANUnop (ARec "4") (map_to_rec "3" op)))
           (map_to_rec "2" (map_to_rec "1" (ANUnop ADistinct (project sl op))))).

    Definition group_full_with_env (g:string) (sl:list string) (op : algenv) : algenv :=
      let op_result := ANUnop (ADot "$pregroup") ANEnv in
      let group_over_op_result := group_full g sl op_result in
      ANAppEnv group_over_op_result (ANBinop AConcat ANEnv (ANUnop (ARec "$pregroup") op)).

  (* Unnest *)

    Definition unnest_one (s:string) (op:algenv) : algenv :=
      ANMap ((ANUnop (ARecRemove s)) ANID) (ANMapConcat ((ANUnop (ADot s)) ANID) op).

    Definition unnest_two (s1 s2:string) (op:algenv) : algenv :=
      ANMap ((ANUnop (ARecRemove s1)) ANID) (ANMapConcat (ANMap ((ANUnop (ARec s2)) ANID) ((ANUnop (ADot s1)) ANID)) op).


  (* NRAEnv for Optim *)
  (* A representation for the NRA with additional operators, usually
     helpful when considering optimization *)
  
  Inductive algenvx : Set :=
  (* Those correspond to operators in the underlying NRA *)
  | ANXID : algenvx
  | ANXConst : data -> algenvx
  | ANXBinop : binOp -> algenvx -> algenvx -> algenvx
  | ANXUnop : unaryOp -> algenvx -> algenvx
  | ANXMap : algenvx -> algenvx -> algenvx
  | ANXMapConcat : algenvx -> algenvx -> algenvx
  | ANXProduct : algenvx -> algenvx -> algenvx
  | ANXSelect : algenvx -> algenvx -> algenvx
  | ANXDefault : algenvx -> algenvx -> algenvx
  | ANXEither : algenvx -> algenvx -> algenvx
  | ANXEitherConcat : algenvx -> algenvx -> algenvx
  | ANXApp : algenvx -> algenvx -> algenvx
  | ANXGetConstant : string -> algenvx
  | ANXEnv : algenvx
  | ANXAppEnv : algenvx -> algenvx -> algenvx
  | ANXMapEnv : algenvx -> algenvx
  (* Those are additional operators *)
  | ANXFlatMap : algenvx -> algenvx -> algenvx
  | ANXJoin : algenvx -> algenvx -> algenvx -> algenvx
  | ANXProject : list string -> algenvx -> algenvx
  .

  Global Instance algenvx_eqdec : EqDec algenvx eq.
  Proof.
    change (forall x y : algenvx,  {x = y} + {x <> y}).
    decide equality;
      try solve [apply binOp_eqdec | apply unaryOp_eqdec | apply data_eqdec | apply string_eqdec | apply list_eqdec; apply string_eqdec].
  Qed.

  Fixpoint algenv_of_algenvx (e:algenvx) : algenv :=
    match e with
      | ANXID => ANID
      | ANXConst d => ANConst d
      | ANXBinop b e1 e2 => ANBinop b (algenv_of_algenvx e1) (algenv_of_algenvx e2)
      | ANXUnop u e1 => ANUnop u (algenv_of_algenvx e1)
      | ANXMap e1 e2 => ANMap (algenv_of_algenvx e1) (algenv_of_algenvx e2)
      | ANXMapConcat e1 e2 => ANMapConcat (algenv_of_algenvx e1) (algenv_of_algenvx e2)
      | ANXProduct e1 e2 => ANProduct (algenv_of_algenvx e1) (algenv_of_algenvx e2)
      | ANXSelect e1 e2 => ANSelect (algenv_of_algenvx e1) (algenv_of_algenvx e2)
      | ANXDefault e1 e2 => ANDefault (algenv_of_algenvx e1) (algenv_of_algenvx e2)
      | ANXEither opl opr => ANEither (algenv_of_algenvx opl) (algenv_of_algenvx opr)
      | ANXEitherConcat op1 op2 => ANEitherConcat (algenv_of_algenvx op1) (algenv_of_algenvx op2)
      | ANXApp e1 e2 => ANApp (algenv_of_algenvx e1) (algenv_of_algenvx e2)
      | ANXGetConstant s => ANGetConstant s
      | ANXEnv => ANEnv
      | ANXAppEnv e1 e2 => ANAppEnv (algenv_of_algenvx e1) (algenv_of_algenvx e2)
      | ANXMapEnv e1 => ANMapEnv (algenv_of_algenvx e1)
      | ANXFlatMap e1 e2 => flat_map (algenv_of_algenvx e1) (algenv_of_algenvx e2)
      | ANXJoin e1 e2 e3 => join (algenv_of_algenvx e1) (algenv_of_algenvx e2) (algenv_of_algenvx e3)
      | ANXProject ls e1 => project ls (algenv_of_algenvx e1)
    end.

  Fixpoint algenvx_of_algenv (a:algenv) : algenvx :=
    match a with
      | ANID => ANXID
      | ANConst d => ANXConst d
      | ANBinop b e1 e2 => ANXBinop b (algenvx_of_algenv e1) (algenvx_of_algenv e2)
      | ANUnop u e1 => ANXUnop u (algenvx_of_algenv e1)
      | ANMap e1 e2 => ANXMap (algenvx_of_algenv e1) (algenvx_of_algenv e2)
      | ANMapConcat e1 e2 => ANXMapConcat (algenvx_of_algenv e1) (algenvx_of_algenv e2)
      | ANProduct e1 e2 => ANXProduct (algenvx_of_algenv e1) (algenvx_of_algenv e2)
      | ANSelect e1 e2 => ANXSelect (algenvx_of_algenv e1) (algenvx_of_algenv e2)
      | ANDefault e1 e2 => ANXDefault (algenvx_of_algenv e1) (algenvx_of_algenv e2)
      | ANEither opl opr => ANXEither (algenvx_of_algenv opl) (algenvx_of_algenv opr)
      | ANEitherConcat op1 op2 => ANXEitherConcat (algenvx_of_algenv op1) (algenvx_of_algenv op2)
      | ANApp e1 e2 => ANXApp (algenvx_of_algenv e1) (algenvx_of_algenv e2)
      | ANGetConstant s => ANXGetConstant s
      | ANEnv => ANXEnv
      | ANAppEnv e1 e2 => ANXAppEnv (algenvx_of_algenv e1) (algenvx_of_algenv e2)
      | ANMapEnv e1 => ANXMapEnv (algenvx_of_algenv e1)
    end.

  Lemma algenvx_roundtrip (a:algenv) :
    (algenv_of_algenvx (algenvx_of_algenv a)) = a.
  Proof.
    induction a; simpl; try reflexivity; try (rewrite IHa1; rewrite IHa2; try rewrite IHa3; reflexivity); rewrite IHa; reflexivity.
  Qed.
    
  Context (h:list(string*string)).
  
  Definition fun_of_algenvx c (e:algenvx) (env:data) (x:data) : option data :=
    fun_of_algenv h c (algenv_of_algenvx e) env x.

  Lemma initial_algenvx_ident c (e:algenv) (env:data) (x:data) :
    fun_of_algenvx c (algenvx_of_algenv e) env x = fun_of_algenv h c e env x.
  Proof.
    unfold fun_of_algenvx.
    rewrite algenvx_roundtrip.
    reflexivity.
  Qed.

End RAlgEnvExt.

(* begin hide *)
Delimit Scope algenvx_scope with algenvx.

Notation "h ⊢ EOp @ₑₓ x ⊣ c ; env" := (fun_of_algenvx h c EOp env x) (at level 10): algenvx_scope.

(* As much as possible, notations are aligned with those of [CM93]
   S. Cluet and G. Moerkotte. Nested queries in object bases. In
   Proc. Int.  Workshop on Database Programming Languages , pages
   226-242, 1993.

   See also chapter 7.2 in:
   http://pi3.informatik.uni-mannheim.de/~moer/querycompiler.pdf
 *)

(* end hide *)

Local Open Scope string_scope.
Tactic Notation "algenvx_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANXID"
  | Case_aux c "ANXConst"
  | Case_aux c "ANXBinop"
  | Case_aux c "ANXUnop"
  | Case_aux c "ANXMap"
  | Case_aux c "ANXMapConcat"
  | Case_aux c "ANXProduct"
  | Case_aux c "ANXSelect"
  | Case_aux c "ANXDefault"
  | Case_aux c "ANXEither"
  | Case_aux c "ANXEitherConcat"
  | Case_aux c "ANXApp"
  | Case_aux c "ANXEnv"
  | Case_aux c "ANXCEnv"
  | Case_aux c "ANXAppEnv"
  | Case_aux c "ANXMapEnv"
  | Case_aux c "ANXFlatMap"
  | Case_aux c "ANXJoin"
  | Case_aux c "ANXProject" ].

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
