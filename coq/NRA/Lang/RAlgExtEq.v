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

Section RAlgExt.
  Require Import String List Compare_dec.

  Require Import Utils BasicRuntime.
  Require Import RAlg RAlgEq RAlgExt.

  (* Equivalence for extended algebra *)

  Local Open Scope algext_scope.

  Context {fruntime:foreign_runtime}.

  Definition algext_eq (op1 op2:algext) : Prop :=
    forall h:list(string*string),
    forall x:data,
      data_normalized h x ->
      h ⊢ op1 @ₓ x = h ⊢ op2 @ₓ x.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.

  Global Instance algext_equiv : Equivalence algext_eq.
  Proof.
    constructor.
    - unfold Reflexive, algext_eq.
      intros; reflexivity.
    - unfold Symmetric, algext_eq.
      intros; rewrite (H h x0) by trivial; reflexivity.
    - unfold Transitive, algext_eq.
      intros; rewrite (H h x0) by trivial; rewrite (H0 h x0) by trivial; reflexivity.
  Qed.

  Definition algext_eq_alg_eq (op1 op2:algext) : algext_eq op1 op2 <-> alg_eq (alg_of_algext op1) (alg_of_algext op2).
  Proof.
    split; intro; assumption.
   Qed.
    
  (* all the extended algebraic constructors are proper wrt. equivalence *)

  (* AXID *)
  Global Instance eaid_proper : Proper algext_eq AXID.
  Proof.
    unfold Proper, respectful, algext_eq.
    apply aid_proper; assumption.
  Qed.

  (* AXConst *)
  Global Instance eaconst_proper : Proper (eq ==> algext_eq) AXConst.
  Proof.
    unfold Proper, respectful, algext_eq; intros.
    apply aconst_proper; assumption.
  Qed.

  (* AXBinOp *)

  Global Instance eabinop_proper : Proper (binop_eq ==> algext_eq ==> algext_eq ==> algext_eq) AXBinop.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply abinop_proper; assumption.
  Qed.

  (* AXUnop *)
  Global Instance eaunop_proper : Proper (unaryop_eq ==> algext_eq ==> algext_eq) AXUnop.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply aunop_proper; assumption.
  Qed.

  (* AXMap *)
  Global Instance eamap_proper : Proper (algext_eq ==> algext_eq ==> algext_eq) AXMap.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply amap_proper; assumption.
  Qed.

  (* AXMapConcat *)
  Global Instance eamapconcat_proper : Proper (algext_eq ==> algext_eq ==> algext_eq) AXMapConcat.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply amapconcat_proper; assumption.
  Qed.

  (* AXProduct *)
  Global Instance eaproduct_proper : Proper (algext_eq ==> algext_eq ==> algext_eq) AXProduct.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply aproduct_proper; assumption.
  Qed.

  (* AXSelect *)
  Global Instance easelect_proper : Proper (algext_eq ==> algext_eq ==> algext_eq) AXSelect.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply aselect_proper; assumption.
  Qed.

  (* AXEither *)
  Global Instance eaeither_proper : Proper (algext_eq ==> algext_eq ==> algext_eq) AXEither.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros; simpl.
    destruct x1; simpl; trivial; inversion H1; subst; eauto.
  Qed.

  (* AXEitherConcat *)
  Global Instance eaeitherconcat_proper : Proper (algext_eq ==> algext_eq ==> algext_eq) AXEitherConcat.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros; simpl.
    rewrite (H0 h x1) by trivial; rewrite (H h x1) by trivial.
    case_eq (h ⊢ alg_of_algext y0 @ₐ x1); case_eq (h ⊢ alg_of_algext y @ₐ x1); intros; simpl; trivial.
  Qed.
  
  (* AXDefault *)
  Global Instance eadefault_proper : Proper (algext_eq ==> algext_eq ==> algext_eq) AXDefault.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply adefault_proper; assumption.
  Qed.

  (* AXApp *)
  Global Instance eaapp_proper : Proper (algext_eq ==> algext_eq ==> algext_eq) AXApp.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply aapp_proper; assumption.
  Qed.

  (* AXJoin *)
  Global Instance eajoin_proper : Proper (algext_eq ==> algext_eq ==> algext_eq ==> algext_eq) AXJoin.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply aselect_proper; try assumption.
    apply aproduct_proper; assumption.
  Qed.

  (* AXSemiJoin *)
  Global Instance easemi_join_proper : Proper (algext_eq ==> algext_eq ==> algext_eq ==> algext_eq) AXSemiJoin.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply aselect_proper; try assumption.
    apply aunop_proper; try assumption; try reflexivity.
    apply abinop_proper; try assumption; try reflexivity.
    apply aselect_proper; try assumption; try reflexivity.
    apply aproduct_proper; try assumption; reflexivity.
  Qed.

  (* AXAntiJoin *)
  Global Instance eaanti_join_proper : Proper (algext_eq ==> algext_eq ==> algext_eq ==> algext_eq) AXAntiJoin.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply aselect_proper; try assumption.
    apply abinop_proper; try assumption; try reflexivity.
    apply aselect_proper; try assumption; try reflexivity.
    apply aproduct_proper; try assumption; reflexivity.
  Qed.

  (* AXMapToRec *)
  Global Instance eamap_to_rec_proper : Proper (eq ==> algext_eq ==> algext_eq) AXMapToRec.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply amap_proper; try assumption.
    rewrite H; reflexivity.
  Qed.    

  (* AXMapAddRec *)
  Global Instance eamap_add_rec_proper : Proper (eq ==> algext_eq ==> algext_eq ==> algext_eq) AXMapAddRec.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    apply amap_proper; try assumption.
    apply abinop_proper; try assumption; try reflexivity.
    apply aunop_proper; try assumption; try reflexivity.
    rewrite H; reflexivity.
  Qed.    

  (* rproject *)
  Global Instance rproject_proper : Proper (eq ==> alg_eq ==> alg_eq) rproject.
  Proof.
    unfold Proper, respectful, alg_eq, fun_of_algext; intros ls ls' ?; subst ls'. intros.
    induction ls; trivial.
    simpl.
    rewrite H, IHls by trivial.
    reflexivity.
  Qed.

  (* AXRProject *)
  Global Instance earproject_proper : Proper (eq ==> algext_eq ==> algext_eq) AXRProject.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite algext_eq_alg_eq in *.
    simpl. rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* project *)
  Global Instance project_proper : Proper (eq ==> alg_eq ==> alg_eq) project.
  Proof.
    unfold Proper, respectful; intros; subst.
    unfold project.
    rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* AXProject *)
  Global Instance eaproject_proper : Proper (eq ==> algext_eq ==> algext_eq) AXProject.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite algext_eq_alg_eq in *.
    simpl. rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* AXProjectRemove *)
  Global Instance eaproject_remove_proper : Proper (eq ==> algext_eq ==> algext_eq) AXProjectRemove.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    rewrite H by trivial; clear H.
    apply amap_proper; try assumption; reflexivity.
  Qed.    

  (* AXMapRename *)
  Global Instance eamap_rename_rec_proper : Proper (eq ==> eq ==> algext_eq ==> algext_eq) AXMapRename.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    rewrite H by trivial; rewrite H0 by trivial; clear H H0.
    apply amap_proper; try assumption; reflexivity.
  Qed.    

  (* AXUnnestOne *)
  Global Instance eaunnest_one_proper : Proper (eq ==> algext_eq ==> algext_eq) AXUnnestOne.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    rewrite H by trivial; clear H.
    apply amap_proper; try assumption; try reflexivity.
    apply amapconcat_proper; try assumption; reflexivity.
  Qed.    

  (* AXUnnestTwo *)
  Global Instance eaunnest_two_proper : Proper (eq ==> eq ==> algext_eq ==> algext_eq) AXUnnestTwo.
  Proof.
    unfold Proper, respectful, algext_eq, fun_of_algext; intros.
    rewrite H by trivial; rewrite H0 by trivial; clear H H0.
    apply amap_proper; try assumption; try reflexivity.
    apply amapconcat_proper; try assumption; reflexivity.
  Qed.    

  (* group1 *)
  Global Instance group1_proper : Proper (eq ==> eq ==> alg_eq ==> alg_eq) group1.
  Proof.
    unfold Proper, respectful, group1; intros; subst; simpl.
    repeat (apply amap_proper
                  || apply amapconcat_proper
                  || apply aunop_proper
                  || apply abinop_proper
                  || assumption
                  || reflexivity).
  Qed.

  (* AXGroupBy *)
  Global Instance eagroupby_proper : Proper (eq ==> eq ==> algext_eq ==> algext_eq) AXGroupBy.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite algext_eq_alg_eq in *.
    simpl. rewrite H1.
    reflexivity.
  Qed.

End RAlgExt.

Notation "X ≡ₓ Y" := (algext_eq X Y) (at level 90) : algext_scope. (* ≡ = \equiv *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)

