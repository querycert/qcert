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

(*******************************
 * Algebra constructors proper *
 *******************************)

Require Import Equivalence.
Require Import Morphisms.
Require Import Setoid.
Require Import EquivDec.
Require Import Program.
Require Import List.
Require Import String.
Require Import Utils.
Require Import CommonRuntime.
Require Import NRA.

Section NRAEq.
  Local Open Scope nra_scope.

  Context {fruntime:foreign_runtime}.

  (* Equivalence relation between algebraic plans.
     Two plans are equivalent iff they return the same value for every input.
   *)
  
  Definition nra_eq (op1 op2:nra) : Prop :=
    forall
      (h:list(string*string))
      (c:list (string*data))
      (dn_c:Forall (fun d => data_normalized h (snd d)) c)
      (x:data)
      (dn_x:data_normalized h x),
      h ⊢ op1 @ₐ x ⊣ c = h ⊢ op2 @ₐ x ⊣ c.

  Global Instance nra_equiv : Equivalence nra_eq.
  Proof.
    constructor.
    - unfold Reflexive, nra_eq.
      intros; reflexivity.
    - unfold Symmetric, nra_eq.
      intros. rewrite H; trivial.
    - unfold Transitive, nra_eq.
      intros.
      rewrite H, H0 by trivial.
      trivial.
  Qed.

  (* all the algebraic constructors are proper wrt. equivalence *)

  (* NRAGetConstant *)
  Global Instance proper_NRAGetConstant s : Proper (nra_eq) (NRAGetConstant s).
  Proof.
    unfold Proper, respectful, nra_eq; intros; simpl.
    reflexivity.
  Qed.

  (* NRAID *)
  Global Instance proper_NRAID : Proper nra_eq NRAID.
  Proof.
    unfold Proper, respectful, nra_eq.
    intros; reflexivity.
  Qed.

  (* NRAConst *)
  Global Instance proper_NRAConst : Proper (eq ==> nra_eq) NRAConst.
  Proof.
    unfold Proper, respectful, nra_eq.
    intros; rewrite H; reflexivity.
  Qed.

  (* NRABinop *)

  Global Instance proper_NRABinop : Proper (binary_op_eq ==> nra_eq ==> nra_eq ==> nra_eq) NRABinop.
  Proof.
    unfold Proper, respectful, nra_eq.
    intros; simpl.
    rewrite H0, H1 by trivial.
    case_eq (h ⊢ y1 @ₐ x2 ⊣ c); case_eq (h ⊢ y0 @ₐ x2 ⊣ c); simpl; trivial.
    intros.
    rewrite (H h); eauto.
  Qed.

  (* NRAUnop *)
  Global Instance proper_NRAUnop : Proper (unary_op_eq ==> nra_eq ==> nra_eq) NRAUnop.
  Proof.
    unfold Proper, respectful, nra_eq.
    intros; simpl.
    rewrite (H0 h c dn_c x1) by trivial.
    case_eq (h ⊢ y0 @ₐ x1 ⊣ c); simpl; trivial; intros.
    rewrite (H h); eauto.
  Qed.
    
  Hint Resolve data_normalized_dcoll_in.

  (* NRAMap *)
  Global Instance proper_NRAMap : Proper (nra_eq ==> nra_eq ==> nra_eq) NRAMap.
  Proof.
    unfold Proper, respectful.
    intros; unfold nra_eq in *; intros; simpl.
    rewrite (H0 h c dn_c x1) by trivial.
    case_eq (h ⊢ y0 @ₐ x1 ⊣ c); simpl; trivial; intros.
    destruct d; try reflexivity.
    simpl; f_equal.
    apply lift_map_ext.
    eauto.
  Qed.

  (* NRAMapProduct *)

  Global Instance proper_NRAMapProduct : Proper (nra_eq ==> nra_eq ==> nra_eq) NRAMapProduct.
  Proof.
    unfold Proper, respectful.
    intros; unfold nra_eq in *; intros; simpl.
    rewrite (H0 h c dn_c x1); case_eq (h ⊢ y0 @ₐ x1 ⊣ c); intros; trivial.
    destruct d; try reflexivity.
    apply olift_ext; inversion 1; subst; intros.
    simpl. f_equal.
    apply omap_product_ext; intros.
    eauto.
  Qed.

  (* NRAProduct *)
  Global Instance proper_NRAProduct : Proper (nra_eq ==> nra_eq ==> nra_eq) NRAProduct.
  Proof.
    unfold Proper, respectful.
    intros; unfold nra_eq in *; intros; simpl.
    rewrite (H0 h c dn_c x1) by trivial; rewrite (H h c dn_c x1) by trivial.
    reflexivity.
  Qed.

  (* NRASelect *)
  Global Instance proper_NRASelect : Proper (nra_eq ==> nra_eq ==> nra_eq) NRASelect.
  Proof.
    unfold Proper, respectful, nra_eq.
    intros; simpl.
    rewrite (H0 h c dn_c x1) by trivial.
    case_eq (h ⊢ y0 @ₐ x1 ⊣ c); intro; trivial.
    destruct d; try reflexivity.
    intros. apply olift_ext; inversion 1; subst; intros.
    simpl.
    f_equal.
    apply lift_filter_ext; intros.
    rewrite H; trivial.
    eauto.
  Qed.

  (* NRADefault *)
  Global Instance proper_NRADefault : Proper (nra_eq ==> nra_eq ==> nra_eq) NRADefault.
  Proof.
    unfold Proper, respectful, nra_eq; intros; simpl.
    rewrite (H0 h c dn_c x1) by trivial; rewrite (H h c dn_c x1) by trivial.
    case_eq (h ⊢ y0 @ₐ x1 ⊣ c); intros; case_eq (h ⊢ y @ₐ x1 ⊣ c); intros; simpl; trivial.
  Qed.

  (* NRAEither *)
  Global Instance proper_NRAEither : Proper (nra_eq ==> nra_eq ==> nra_eq) NRAEither.
  Proof.
    unfold Proper, respectful, nra_eq; intros; simpl.
    destruct x1; simpl; trivial; inversion dn_x; subst; auto.
  Qed.

  (* NRAEitherConcat *)
  Global Instance proper_NRAEitherConcat : Proper (nra_eq ==> nra_eq ==> nra_eq) NRAEitherConcat.
  Proof.
    unfold Proper, respectful, nra_eq; intros; simpl.
    rewrite (H0 h c dn_c x1) by trivial; rewrite (H h c dn_c x1) by trivial.
    case_eq (h ⊢ y0 @ₐ x1 ⊣ c); case_eq (h ⊢ y @ₐ x1 ⊣ c); intros; simpl; trivial.
  Qed.

  (* NRAApp *)
  Global Instance proper_NRAApp : Proper (nra_eq ==> nra_eq ==> nra_eq) NRAApp.
  Proof.
    unfold Proper, respectful, nra_eq; intros; simpl.
    rewrite (H0 h c dn_c x1) by trivial. case_eq (h ⊢ y0 @ₐ x1 ⊣ c); intros; simpl; trivial.
    rewrite (H h c dn_c d); eauto.
  Qed.

End NRAEq.

Notation "X ≡ₐ Y" := (nra_eq X Y) (at level 90) : nra_scope.                             (* ≡ = \equiv *)

