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
Require Import Compare_dec.
Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import CommonRuntime.
Require Import NRA.
Require Import NRAEq.
Require Import NRAExt.

Section NRAExt.
  (* Equivalence for extended algebra *)

  Local Open Scope nraext_scope.

  Context {fruntime:foreign_runtime}.

  Definition nraext_eq (op1 op2:nraext) : Prop :=
    forall
      (h:list(string*string))
      (c:list (string*data))
      (dn_c:Forall (fun d => data_normalized h (snd d)) c)
      (x:data)
      (dn_x:data_normalized h x),
      h ⊢ op1 @ₓ x ⊣ c = h ⊢ op2 @ₓ x ⊣ c.

  Global Instance nraext_equiv : Equivalence nraext_eq.
  Proof.
    constructor.
    - unfold Reflexive, nraext_eq.
      intros; reflexivity.
    - unfold Symmetric, nraext_eq.
      intros; rewrite (H h c dn_c x0) by trivial; reflexivity.
    - unfold Transitive, nraext_eq.
      intros; rewrite (H h c dn_c x0) by trivial; rewrite (H0 h c dn_c x0) by trivial; reflexivity.
  Qed.

  Definition nraext_eq_nra_eq (op1 op2:nraext) : nraext_eq op1 op2 <-> nra_eq (nra_of_nraext op1) (nra_of_nraext op2).
  Proof.
    split; intro; assumption.
   Qed.
    
  (** all the extended nraebraic constructors are proper wrt. equivalence *)

  (* xNRAGetConstant *)
  Global Instance proper_xNRAGetConstant s : Proper (nraext_eq) (xNRAGetConstant s).
  Proof.
    unfold Proper, respectful, nraext_eq; intros; simpl.
    reflexivity.
  Qed.

  (* xNRAID *)
  Global Instance proper_xNRAID : Proper nraext_eq xNRAID.
  Proof.
    unfold Proper, respectful, nraext_eq.
    apply proper_NRAID; assumption.
  Qed.

  (* xNRAConst *)
  Global Instance proper_xNRAConst : Proper (eq ==> nraext_eq) xNRAConst.
  Proof.
    unfold Proper, respectful, nraext_eq; intros.
    apply proper_NRAConst; assumption.
  Qed.

  (* xNRABinop *)

  Global Instance proper_xNRABinop : Proper (binary_op_eq ==> nraext_eq ==> nraext_eq ==> nraext_eq) xNRABinop.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRABinop; assumption.
  Qed.

  (* xNRAUnop *)
  Global Instance proper_xNRAUnop : Proper (unary_op_eq ==> nraext_eq ==> nraext_eq) xNRAUnop.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRAUnop; assumption.
  Qed.

  (* xNRAMap *)
  Global Instance proper_xNRAMap : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) xNRAMap.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRAMap; assumption.
  Qed.

  (* xNRAMapProduct *)
  Global Instance proper_xNRAMapProduct : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) xNRAMapProduct.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRAMapProduct; assumption.
  Qed.

  (* xNRAProduct *)
  Global Instance proper_xNRAProduct : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) xNRAProduct.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRAProduct; assumption.
  Qed.

  (* xNRASelect *)
  Global Instance proper_xNRASelect : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) xNRASelect.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRASelect; assumption.
  Qed.

  (* xNRAEither *)
  Global Instance proper_xNRAEither : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) xNRAEither.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros; simpl.
    destruct x1; simpl; trivial; inversion dn_x; subst; eauto.
  Qed.

  (* xNRAEitherConcat *)
  Global Instance proper_xNRAEitherConcat : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) xNRAEitherConcat.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros; simpl.
    rewrite (H0 h c dn_c x1) by trivial; rewrite (H h c dn_c x1) by trivial.
    case_eq (h ⊢ nra_of_nraext y0 @ₐ x1 ⊣ c); case_eq (h ⊢ nra_of_nraext y @ₐ x1 ⊣ c); intros; simpl; trivial.
  Qed.
  
  (* xNRADefault *)
  Global Instance proper_xNRADefault : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) xNRADefault.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRADefault; assumption.
  Qed.

  (* xNRAApp *)
  Global Instance proper_xNRAApp : Proper (nraext_eq ==> nraext_eq ==> nraext_eq) xNRAApp.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRAApp; assumption.
  Qed.

  (* xNRAJoin *)
  Global Instance proper_xNRAJoin : Proper (nraext_eq ==> nraext_eq ==> nraext_eq ==> nraext_eq) xNRAJoin.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRASelect; try assumption.
    apply proper_NRAProduct; assumption.
  Qed.

  (* xNRASemiJoin *)
  Global Instance proper_xNRASemiJoin : Proper (nraext_eq ==> nraext_eq ==> nraext_eq ==> nraext_eq) xNRASemiJoin.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRASelect; try assumption.
    apply proper_NRAUnop; try assumption; try reflexivity.
    apply proper_NRABinop; try assumption; try reflexivity.
    apply proper_NRASelect; try assumption; try reflexivity.
    apply proper_NRAProduct; try assumption; reflexivity.
  Qed.

  (* xNRAAntiJoin *)
  Global Instance proper_xNRAAntiJoin : Proper (nraext_eq ==> nraext_eq ==> nraext_eq ==> nraext_eq) xNRAAntiJoin.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRASelect; try assumption.
    apply proper_NRABinop; try assumption; try reflexivity.
    apply proper_NRASelect; try assumption; try reflexivity.
    apply proper_NRAProduct; try assumption; reflexivity.
  Qed.

  (* xNRAMapToRec *)
  Global Instance proper_xNRAMapToRec : Proper (eq ==> nraext_eq ==> nraext_eq) xNRAMapToRec.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRAMap; try assumption.
    rewrite H; reflexivity.
  Qed.    

  (* xNRAMapAddRec *)
  Global Instance proper_xNRAMapAddRec : Proper (eq ==> nraext_eq ==> nraext_eq ==> nraext_eq) xNRAMapAddRec.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    apply proper_NRAMap; try assumption.
    apply proper_NRABinop; try assumption; try reflexivity.
    apply proper_NRAUnop; try assumption; try reflexivity.
    rewrite H; reflexivity.
  Qed.    

  (* xNRARProject *)
  Global Instance rproject_proper : Proper (eq ==> nra_eq ==> nra_eq) rproject.
  Proof.
    unfold Proper, respectful, nra_eq, nraext_eval; intros ls ls' ?; subst ls'. intros.
    induction ls; trivial.
    simpl.
    rewrite H, IHls by trivial.
    reflexivity.
  Qed.

  Global Instance proper_xNRARProject : Proper (eq ==> nraext_eq ==> nraext_eq) xNRARProject.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraext_eq_nra_eq in *.
    simpl. rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* xNRAProject *)
  Global Instance project_proper : Proper (eq ==> nra_eq ==> nra_eq) project.
  Proof.
    unfold Proper, respectful; intros; subst.
    unfold project.
    rewrite H0 by trivial.
    reflexivity.
  Qed.

  Global Instance proper_xNRAProject : Proper (eq ==> nraext_eq ==> nraext_eq) xNRAProject.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraext_eq_nra_eq in *.
    simpl. rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* xNRAProjectRemove *)
  Global Instance proper_xNRAProjectRemove : Proper (eq ==> nraext_eq ==> nraext_eq) xNRAProjectRemove.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    rewrite H by trivial; clear H.
    apply proper_NRAMap; try assumption; reflexivity.
  Qed.    

  (* xNRAMapRename *)
  Global Instance proper_xNRAMapRename : Proper (eq ==> eq ==> nraext_eq ==> nraext_eq) xNRAMapRename.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    rewrite H by trivial; rewrite H0 by trivial; clear H H0.
    apply proper_NRAMap; try assumption; reflexivity.
  Qed.    

  (* xNRAUnnestOne *)
  Global Instance proper_xNRAUnnestOne : Proper (eq ==> nraext_eq ==> nraext_eq) xNRAUnnestOne.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    rewrite H by trivial; clear H.
    apply proper_NRAMap; try assumption; try reflexivity.
    apply proper_NRAMapProduct; try assumption; reflexivity.
  Qed.    

  (* xNRAUnnestTwo *)
  Global Instance proper_xNRAUnnestTwo : Proper (eq ==> eq ==> nraext_eq ==> nraext_eq) xNRAUnnestTwo.
  Proof.
    unfold Proper, respectful, nraext_eq, nraext_eval; intros.
    rewrite H by trivial; rewrite H0 by trivial; clear H H0.
    apply proper_NRAMap; try assumption; try reflexivity.
    apply proper_NRAMapProduct; try assumption; reflexivity.
  Qed.    

  (* xNRAGroupBy *)
  Global Instance group1_proper : Proper (eq ==> eq ==> nra_eq ==> nra_eq) group1.
  Proof.
    unfold Proper, respectful, group1; intros; subst; simpl.
    repeat (apply proper_NRAMap
                  || apply proper_NRAMapProduct
                  || apply proper_NRAUnop
                  || apply proper_NRABinop
                  || assumption
                  || reflexivity).
  Qed.

  Global Instance proper_xNRAGroupBy : Proper (eq ==> eq ==> nraext_eq ==> nraext_eq) xNRAGroupBy.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite nraext_eq_nra_eq in *.
    simpl. rewrite H1.
    reflexivity.
  Qed.

End NRAExt.

Notation "X ≡ₓ Y" := (nraext_eq X Y) (at level 90) : nraext_scope. (* ≡ = \equiv *)

