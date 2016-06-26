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

Section RAlgEnvExtEq.
  Require Import String List Compare_dec.

  Require Import Utils BasicRuntime.
  Require Import RAlgEnv RAlgEnvEq RAlgEnvExt.

  (* Equivalence for extended algebra *)

  Local Open Scope algenv_scope.
  Local Open Scope algenvx_scope.

  Context {fruntime:foreign_runtime}.

  Definition algenvx_eq (op1 op2:algenvx) : Prop :=
    forall (h:list(string*string))
           (c:list (string*data))
           (dn_c: Forall (fun d : string * data => data_normalized h (snd d)) c)
           (env:data)
           (dn_env:data_normalized h env)
           (x:data)
           (dn_x:data_normalized h x),
        fun_of_algenvx h c op1 env x = fun_of_algenvx h c op2 env x.

  Require Import Equivalence.
  Require Import Morphisms.
  Require Import Setoid.
  Require Import EquivDec.
  Require Import Program.

  Global Instance algenvx_equiv : Equivalence algenvx_eq.
  Proof.
    constructor.
    - unfold Reflexive, algenvx_eq.
      intros; reflexivity.
    - unfold Symmetric, algenvx_eq.
      intros. rewrite (H h c dn_c env dn_env x0) by trivial; reflexivity.
    - unfold Transitive, algenvx_eq.
      intros. rewrite (H h c dn_c env dn_env x0) by trivial; rewrite (H0 h c dn_c env dn_env x0) by trivial; reflexivity.
  Qed.

  Definition algenvx_eq_algenv_eq (op1 op2:algenvx) : algenvx_eq op1 op2 <-> algenv_eq (algenv_of_algenvx op1) (algenv_of_algenvx op2).
  Proof.
    split; intro; assumption.
  Qed.

  (* all the extended algebraic constructors are proper wrt. equivalence *)

  (* ANXID *)
  Global Instance exaid_proper : Proper algenvx_eq ANXID.
  Proof.
    unfold Proper, respectful, algenvx_eq.
    apply anid_proper; assumption.
  Qed.

  (* ANXConst *)
  Global Instance exaconst_proper : Proper (eq ==> algenvx_eq) ANXConst.
  Proof.
    unfold Proper, respectful, algenvx_eq; intros.
    apply anconst_proper; assumption.
  Qed.

  (* ANXBinOp *)

  Global Instance exabinop_proper : Proper (binop_eq ==> algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXBinop.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply anbinop_proper; assumption.
  Qed.

  (* ANXUnop *)
  Global Instance exaunop_proper : Proper (unaryop_eq ==> algenvx_eq ==> algenvx_eq) ANXUnop.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply anunop_proper; assumption.
  Qed.

  (* ANXMap *)
  Global Instance examap_proper : Proper (algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXMap.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply anmap_proper; assumption.
  Qed.

  (* ANXMapConcat *)
  Global Instance examapconcat_proper : Proper (algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXMapConcat.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply anmapconcat_proper; assumption.
  Qed.

  (* ANXProduct *)
  Global Instance exaproduct_proper : Proper (algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXProduct.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply anproduct_proper; assumption.
  Qed.

  (* ANXSelect *)
  Global Instance exaselect_proper : Proper (algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXSelect.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply anselect_proper; assumption.
  Qed.

  (* ANXEither *)
  Global Instance exaeither_proper : Proper (algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXEither.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros; simpl.
    destruct x1; simpl; trivial; inversion dn_x; subst; eauto.
  Qed.

  (* ANXEitherConcat *)
  Global Instance exaeitherconcat_proper : Proper (algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXEitherConcat.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros; simpl.
    rewrite (H0 h c dn_c env dn_env x1) by trivial; rewrite (H h c dn_c env dn_env x1) by trivial.
    case_eq (h ⊢ₑ algenv_of_algenvx y0 @ₑ x1 ⊣ c;env); case_eq (h ⊢ₑ algenv_of_algenvx y @ₑ x1 ⊣ c;env); intros; simpl; trivial.
  Qed.
  
  (* ANXDefault *)
  Global Instance exadefault_proper : Proper (algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXDefault.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply andefault_proper; assumption.
  Qed.

  (* ANXApp *)
  Global Instance exaapp_proper : Proper (algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXApp.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply anapp_proper; assumption.
  Qed.

  (* ANXENV *)
  Global Instance exagetconstant_proper s : Proper algenvx_eq (ANXGetConstant s).
  Proof.
    unfold Proper, respectful, algenvx_eq.
    apply angetconstant_proper; assumption.
  Qed.
  
  (* ANXENV *)
  Global Instance exaenv_proper : Proper algenvx_eq ANXEnv.
  Proof.
    unfold Proper, respectful, algenvx_eq.
    apply anenv_proper; assumption.
  Qed.

  (* ANXApp *)
  Global Instance exaappenv_proper : Proper (algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXAppEnv.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply anappenv_proper; assumption.
  Qed.

  (* ANXMapEnv *)
  Global Instance examapenv_proper : Proper (algenvx_eq ==> algenvx_eq) ANXMapEnv.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply anmapenv_proper; assumption.
  Qed.

  (* ANXFlatMap *)
  Global Instance exaflatmap_proper : Proper (algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXFlatMap.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply anunop_proper; try assumption; try reflexivity.
    apply anmap_proper; assumption.
  Qed.

  (* ANXJoin *)
  Global Instance exajoin_proper : Proper (algenvx_eq ==> algenvx_eq ==> algenvx_eq ==> algenvx_eq) ANXJoin.
  Proof.
    unfold Proper, respectful, algenvx_eq, fun_of_algenvx; intros.
    apply anselect_proper; try assumption.
    apply anproduct_proper; assumption.
  Qed.

  (* project *)
  Global Instance project_proper : Proper (eq ==> algenv_eq ==> algenv_eq) project.
  Proof.
    unfold Proper, respectful; intros; subst.
    unfold project.
    rewrite H0 by trivial.
    reflexivity.
  Qed.

  (* ANXProject *)
  Global Instance exaproject_proper : Proper (eq ==> algenvx_eq ==> algenvx_eq) ANXProject.
  Proof.
    unfold Proper, respectful.
    intros; subst.
    rewrite algenvx_eq_algenv_eq in *.
    simpl. rewrite H0 by trivial.
    reflexivity.
  Qed.

End RAlgEnvExtEq.

Notation "X ≡ₑₓ Y" := (algenvx_eq X Y) (at level 90) : algenvx_scope. (* ≡ = \equiv *)

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
