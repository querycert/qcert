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

Section NRAExt.
  Require Import String List Compare_dec.

  Require Import Utils BasicRuntime.
  Require Import NRA NRAEq NRAExt.

  (* Equivalence for extended algebra *)

  Local Open Scope nraext_scope.

  Context {fruntime:foreign_runtime}.

  Definition nraext_eq (op1 op2:nraext) : Prop :=
    forall h:list(string*string),
    forall x:data,
      data_normalized h x ->
      h ⊢ op1 @ₓ x = h ⊢ op2 @ₓ x.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.

  Global Instance nraext_equiv : Equivalence nraext_eq.
  Proof.
    constructor.
    - unfold Reflexive, nraext_eq.
      intros; reflexivity.
    - unfold Symmetric, nraext_eq.
      intros; rewrite (H h x0) by trivial; reflexivity.
    - unfold Transitive, nraext_eq.
      intros; rewrite (H h x0) by trivial; rewrite (H0 h x0) by trivial; reflexivity.
  Qed.

  Definition nraext_eq_nra_eq (op1 op2:nraext) : nraext_eq op1 op2 <-> nra_eq (nra_of_nraext op1) (nra_of_nraext op2).
  Proof.
    split; intro; assumption.
   Qed.
    
  (* all the extended nraebraic constructors are proper wrt. equivalence *)

  (* AXID *)
  Global Instance eaid_proper : Proper nraext_eq AXID.
  Proof.
    unfold Proper, respectful, nraext_eq.
    apply aid_proper; assumption.
  Qed.

  (* AXConst *)
  Global Instance eaconst_proper : Proper (eq ==> nraext_eq) AXConst.
  Proof.
    unfold Proper, respectful, nraext_eq; intros.
    apply aconst_proper; assumption.
  Qed.

  (* AXBinOp *)

  Global Instance eabinop_proper : Proper (binop_eq ==> nraext_eq ==> nraext_eq ==> nraext_eq) AXBinop.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply abinop_proper; assumption.
  Qed.

  (* AXUnop *)
  Global Instance eaunop_proper : Proper (unaryop_eq ==> nraext_eq ==> nraext_eq) AXUnop.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply aunop_proper; assumption.
  Qed.

  (* AXMap *)
  Global Instance eamap_proper : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) AXMap.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply amap_proper; assumption.
  Qed.

  (* AXMapConcat *)
  Global Instance eamapconcat_proper : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) AXMapConcat.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply amapconcat_proper; assumption.
  Qed.

  (* AXProduct *)
  Global Instance eaproduct_proper : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) AXProduct.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply aproduct_proper; assumption.
  Qed.

  (* AXSelect *)
  Global Instance easelect_proper : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) AXSelect.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply aselect_proper; assumption.
  Qed.

  (* AXEither *)
  Global Instance eaeither_proper : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) AXEither.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros; simpl.
    destruct x1; simpl; trivial; inversion H1; subst; eauto.
  Qed.

  (* AXEitherConcat *)
  Global Instance eaeitherconcat_proper : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) AXEitherConcat.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros; simpl.
    rewrite (H0 h x1) by trivial; rewrite (H h x1) by trivial.
    case_eq (h ⊢ nra_of_nraext y0 @ₐ x1); case_eq (h ⊢ nra_of_nraext y @ₐ x1); intros; simpl; trivial.
  Qed.
  
  (* AXDefault *)
  Global Instance eadefault_proper : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) AXDefault.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply adefault_proper; assumption.
  Qed.

  (* AXApp *)
  Global Instance eaapp_proper : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) AXApp.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply aapp_proper; assumption.
  Qed.

  (* AXJoin *)
  Global Instance eajoin_proper : Proper (nraext_eq ==> nraext_eq ==> nraext_eq ==> nraext_eq) AXJoin.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply aselect_proper; try assumption.
    apply aproduct_proper; assumption.
  Qed.

  (* AXSemiJoin *)
  Global Instance easemi_join_proper : Proper (nraext_eq ==> nraext_eq ==> nraext_eq ==> nraext_eq) AXSemiJoin.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply aselect_proper; try assumption.
    apply aunop_proper; try assumption; try reflexivity.
    apply abinop_proper; try assumption; try reflexivity.
    apply aselect_proper; try assumption; try reflexivity.
    apply aproduct_proper; try assumption; reflexivity.
  Qed.

  (* AXAntiJoin *)
  Global Instance eaanti_join_proper : Proper (nraext_eq ==> nraext_eq ==> nraext_eq ==> nraext_eq) AXAntiJoin.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply aselect_proper; try assumption.
    apply abinop_proper; try assumption; try reflexivity.
    apply aselect_proper; try assumption; try reflexivity.
    apply aproduct_proper; try assumption; reflexivity.
  Qed.

  (* AXMapToRec *)
  Global Instance eamap_to_rec_proper : Proper (eq ==> nraext_eq ==> nraext_eq) AXMapToRec.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply amap_proper; try assumption.
    rewrite H; reflexivity.
  Qed.    

  (* AXMapAddRec *)
  Global Instance eamap_add_rec_proper : Proper (eq ==> nraext_eq ==> nraext_eq ==> nraext_eq) AXMapAddRec.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply amap_proper; try assumption.
    apply abinop_proper; try assumption; try reflexivity.
    apply aunop_proper; try assumption; try reflexivity.
    rewrite H; reflexivity.
  Qed.    

  (* rproject *)
  Global Instance rproject_proper : Proper (eq ==> nra_eq ==> nra_eq) rproject.
  Proof.
    unfold Proper, respectful, nra_eq, nraext_eval; intros ls ls' ?; subst ls'. intros.
    induction ls; trivial.
    simpl.
    rewrite H, IHls by trivial.
    reflexivity.
  Qed.

  (* AXRProject *)
  Global Instance earproject_proper : Proper (eq ==> nraext_eq ==> nraext_eq) AXRProject.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraext_eq_nra_eq in *.
    simpl. rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* project *)
  Global Instance project_proper : Proper (eq ==> nra_eq ==> nra_eq) project.
  Proof.
    unfold Proper, respectful; intros; subst.
    unfold project.
    rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* AXProject *)
  Global Instance eaproject_proper : Proper (eq ==> nraext_eq ==> nraext_eq) AXProject.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraext_eq_nra_eq in *.
    simpl. rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* AXProjectRemove *)
  Global Instance eaproject_remove_proper : Proper (eq ==> nraext_eq ==> nraext_eq) AXProjectRemove.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    rewrite H by trivial; clear H.
    apply amap_proper; try assumption; reflexivity.
  Qed.    

  (* AXMapRename *)
  Global Instance eamap_rename_rec_proper : Proper (eq ==> eq ==> nraext_eq ==> nraext_eq) AXMapRename.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    rewrite H by trivial; rewrite H0 by trivial; clear H H0.
    apply amap_proper; try assumption; reflexivity.
  Qed.    

  (* AXUnnestOne *)
  Global Instance eaunnest_one_proper : Proper (eq ==> nraext_eq ==> nraext_eq) AXUnnestOne.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    rewrite H by trivial; clear H.
    apply amap_proper; try assumption; try reflexivity.
    apply amapconcat_proper; try assumption; reflexivity.
  Qed.    

  (* AXUnnestTwo *)
  Global Instance eaunnest_two_proper : Proper (eq ==> eq ==> nraext_eq ==> nraext_eq) AXUnnestTwo.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    rewrite H by trivial; rewrite H0 by trivial; clear H H0.
    apply amap_proper; try assumption; try reflexivity.
    apply amapconcat_proper; try assumption; reflexivity.
  Qed.    

  (* group1 *)
  Global Instance group1_proper : Proper (eq ==> eq ==> nra_eq ==> nra_eq) group1.
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
  Global Instance eagroupby_proper : Proper (eq ==> eq ==> nraext_eq ==> nraext_eq) AXGroupBy.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraext_eq_nra_eq in *.
    simpl. rewrite H1.
    reflexivity.
  Qed.

End NRAExt.

Notation "X ≡ₓ Y" := (nraext_eq X Y) (at level 90) : nraext_scope. (* ≡ = \equiv *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)

